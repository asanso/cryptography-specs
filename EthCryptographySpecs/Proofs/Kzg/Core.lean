import EthCryptographySpecs.Kzg.Core
import EthCryptographySpecs.Proofs.Kzg.Polynomials

/-!
# Proofs: `Core`

The validation surface of the blob-commitment methods: the byte
validators succeed exactly on valid bytes (returning them unchanged),
`computeChallenge` produces a canonical field element, and each entry
point rejects malformed input with exactly the documented error before
doing any real work.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)
open EthCryptographySpecs.Kzg.Constants

/-- `bytesToKzgCommitment` succeeds exactly on valid bytes, and returns
them unchanged. -/
theorem bytesToKzgCommitment_ok_iff {b : Bytes48} {c : KZGCommitment} :
    bytesToKzgCommitment b = .ok c ↔ validateKzgG1 b ∧ c = b := by
  rw [bytesToKzgCommitment]
  split
  · rename_i h
    constructor
    · intro he
      cases he
      exact ⟨h, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  · rename_i h
    constructor
    · intro he
      cases he
    · rintro ⟨hv, _⟩
      exact absurd hv h

/-- `bytesToKzgProof` succeeds exactly on valid bytes, and returns them
unchanged. -/
theorem bytesToKzgProof_ok_iff {b : Bytes48} {p : KZGProof} :
    bytesToKzgProof b = .ok p ↔ validateKzgG1 b ∧ p = b := by
  rw [bytesToKzgProof]
  split
  · rename_i h
    constructor
    · intro he
      cases he
      exact ⟨h, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  · rename_i h
    constructor
    · intro he
      cases he
    · rintro ⟨hv, _⟩
      exact absurd hv h

/-- The Fiat-Shamir challenge is a canonical field element. -/
theorem val_computeChallenge_lt (blob : Blob) (commitment : KZGCommitment) :
    (computeChallenge blob commitment).val < Fr.modulus :=
  val_hashToBlsField_lt _

/-- `g1Lincomb` rejects mismatched input lengths. -/
theorem g1Lincomb_length_mismatch {points : Array KZGCommitment}
    {scalars : Array Fr} (h : points.size ≠ scalars.size) :
    g1Lincomb points scalars
      = throw (.lincombLengthMismatch points.size scalars.size) := by
  simp [g1Lincomb, h]
  rfl

/-- `g1Lincomb` of nothing is the identity (the point at infinity). -/
theorem g1Lincomb_empty :
    g1Lincomb #[] #[] = pure (Bls.G1.compress Bls.G1.zero) := by
  simp [g1Lincomb]
  rfl

/-- `computeKzgProof` rejects a wrongly-sized blob. -/
theorem computeKzgProof_badBlobSize {blob : Blob} (zBytes : Bytes32)
    (h : blob.size ≠ BYTES_PER_BLOB) :
    computeKzgProof blob zBytes = throw (.badBlobSize blob.size) := by
  simp [computeKzgProof, h]
  rfl

/-- `computeKzgProof` rejects a wrongly-sized evaluation point. -/
theorem computeKzgProof_badFieldElementSize {blob : Blob} {zBytes : Bytes32}
    (hb : blob.size = BYTES_PER_BLOB)
    (h : zBytes.size ≠ BYTES_PER_FIELD_ELEMENT) :
    computeKzgProof blob zBytes
      = throw (.badFieldElementSize zBytes.size) := by
  simp [computeKzgProof, hb, h]
  rfl

/-- `verifyKzgProof` rejects a wrongly-sized commitment. -/
theorem verifyKzgProof_badCommitmentSize {commitmentBytes : Bytes48}
    (zBytes yBytes : Bytes32) (proofBytes : Bytes48)
    (h : commitmentBytes.size ≠ BYTES_PER_COMMITMENT) :
    verifyKzgProof commitmentBytes zBytes yBytes proofBytes
      = throw (.badCommitmentSize commitmentBytes.size) := by
  simp [verifyKzgProof, h]
  rfl

/-- `blobToKzgCommitment` rejects a wrongly-sized blob. -/
theorem blobToKzgCommitment_badBlobSize {blob : Blob}
    (h : blob.size ≠ BYTES_PER_BLOB) :
    blobToKzgCommitment blob = throw (.badBlobSize blob.size) := by
  simp [blobToKzgCommitment, h]
  rfl

/-- `computeBlobKzgProof` rejects a wrongly-sized blob. -/
theorem computeBlobKzgProof_badBlobSize {blob : Blob}
    (commitmentBytes : Bytes48) (h : blob.size ≠ BYTES_PER_BLOB) :
    computeBlobKzgProof blob commitmentBytes
      = throw (.badBlobSize blob.size) := by
  simp [computeBlobKzgProof, h]
  rfl

/-- `verifyBlobKzgProof` rejects a wrongly-sized blob. -/
theorem verifyBlobKzgProof_badBlobSize {blob : Blob}
    (commitmentBytes proofBytes : Bytes48)
    (h : blob.size ≠ BYTES_PER_BLOB) :
    verifyBlobKzgProof blob commitmentBytes proofBytes
      = throw (.badBlobSize blob.size) := by
  simp [verifyBlobKzgProof, h]
  rfl

/-- `verifyBlobKzgProofBatch` rejects a commitments array whose length
does not match the blobs array. -/
theorem verifyBlobKzgProofBatch_commitments_mismatch
    {blobs : Array Blob} {commitmentsBytes : Array Bytes48}
    (proofsBytes : Array Bytes48)
    (h : commitmentsBytes.size ≠ blobs.size) :
    verifyBlobKzgProofBatch blobs commitmentsBytes proofsBytes
      = throw (.inputLengthMismatch "commitmentsBytes" blobs.size
          commitmentsBytes.size) := by
  simp [verifyBlobKzgProofBatch, h]
  rfl

/-- `verifyBlobKzgProofBatch` rejects a proofs array whose length does
not match the blobs array. -/
theorem verifyBlobKzgProofBatch_proofs_mismatch
    {blobs : Array Blob} {commitmentsBytes proofsBytes : Array Bytes48}
    (hc : commitmentsBytes.size = blobs.size)
    (h : proofsBytes.size ≠ blobs.size) :
    verifyBlobKzgProofBatch blobs commitmentsBytes proofsBytes
      = throw (.inputLengthMismatch "proofsBytes" blobs.size
          proofsBytes.size) := by
  simp [verifyBlobKzgProofBatch, hc, h]
  rfl

end EthCryptographySpecs.Kzg

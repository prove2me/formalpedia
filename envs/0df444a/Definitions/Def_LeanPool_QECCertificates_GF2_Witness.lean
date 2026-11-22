-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_Witness
-- name    : LeanPool_QECCertificates_GF2_Witness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:45:38.844412+00:00
-- url     : https://prove2.me/theorems/5e856cf4-543c-4838-9444-4ae222ab3e7e
-- title:
--   Witness
-- statement:
--   Definitions and structural lemmas for Witness, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
variable {n : ℕ}
structure DualWitness {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (E : Vec n) where
  /-- The witness vector. -/
  w : Vec n
  /-- Orthogonal to every check row. -/
  mem_ker : w ∈ LinearMap.ker H.toLin'
  /-- Pairs to 1 with the target operator (that is, anticommutes over GF(2)). -/
  pairing : w ⬝ᵥ E = 1
@[reducible] def undetectableSet {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) : Set (Vec n) :=
  (↑(LinearMap.ker M₁.toLin') : Set (Vec n)) \ (↑M₂.certificateRowSpace : Set (Vec n))
noncomputable abbrev codeDistance {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  minWeightKernelOutsideRowSpace H H
end QECCertificates



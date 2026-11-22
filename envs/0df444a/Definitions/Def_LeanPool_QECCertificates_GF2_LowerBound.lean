-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
-- name    : LeanPool_QECCertificates_GF2_LowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:46:57.553541+00:00
-- url     : https://prove2.me/theorems/43b6eb13-b81e-4100-8d44-272dc92ae874
-- title:
--   Lower Bound
-- statement:
--   Definitions and structural lemmas for Lower Bound, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
variable {n : ℕ}
abbrev IsLightUndetectable {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (v : Vec n) : Prop :=
  0 < hammingNorm v ∧ inKerB M₁ v = true ∧
    inSpanEch (List.ofFn fun i => M₂ i) v = false
def lightCand {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (d : ℕ) : List (Vec n) :=
  let echelon := echelonFrom (List.ofFn fun i => M₂ i)
  (lightVecs n (d - 1)).filter fun v =>
    decide (0 < hammingNorm v ∧ inKerB M₁ v = true ∧
      decide (reduceAgainst echelon v = 0) = false)
def lightSet {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (d : ℕ) : Finset (Vec n) :=
  (lightCand M₁ M₂ d).toFinset
end QECCertificates



-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T01:34:58.747987+00:00
-- url     : https://prove2.me/theorems/14b39aa5-be7d-411c-9965-b7f65f382927
-- title:
--   LPSOriginal Meromorphic Degree Bound
-- statement:
--   Definitions and structural lemmas for LPSOriginal Meromorphic Degree Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelOne_unique_polynomial_j

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
abbrev LPSOriginalMeromorphicCosets (N : ℕ) := 𝒮ℒ ⧸
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ
abbrev LPSOriginalMeromorphicLevelForm (N k : ℕ) :=
  ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ((k : ℤ)*12)
def lpsOriginalMeromorphicRatioNorm
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (c : ℂ) :
    ModularForm 𝒮ℒ (12*((k * Nat.card (LPSOriginalMeromorphicCosets N) : ℕ) : ℤ)) :=
  (ModularForm.norm 𝒮ℒ (A-c • B)).mcast (by push_cast; ring)
def lpsOriginalMeromorphicRatioCosetPolynomial
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (τ : ℍ) : Polynomial ℂ := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  exact ∏ q : LPSOriginalMeromorphicCosets N,
    (Polynomial.C (SlashInvariantForm.quotientFunc A q τ) -
      Polynomial.X * Polynomial.C (SlashInvariantForm.quotientFunc B q τ))
def lpsOriginalMeromorphicRatioNormCoefficient
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (c : ℂ) :
    Polynomial ℂ := Classical.choose
      (lpsOriginalLevelOne_unique_polynomial_j (k*Nat.card (LPSOriginalMeromorphicCosets N))
        (lpsOriginalMeromorphicRatioNorm N k A B c)).exists
def lpsOriginalMeromorphicRatioEquation
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) :
    Polynomial (Polynomial ℂ) := by
  classical
  let r := Nat.card (LPSOriginalMeromorphicCosets N)
  exact ∑ i : Fin (r+1),
    Polynomial.C (lpsOriginalMeromorphicRatioNormCoefficient N k A B (i.val : ℂ)) *
      (Lagrange.basis (Finset.univ : Finset (Fin (r+1))) (fun j => (j.val : ℂ)) i).map Polynomial.C
def lpsOriginalFullMeromorphicJFractionEmbedding
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    FractionRing (Polynomial ℂ) →+* lpsOriginalFilledMeromorphicRestrictionSubfield N hN where
  toFun r := ⟨lpsOriginalHolomorphicFractionToMeromorphicGerm (lpsOriginalJFractionEmbedding r),
    lpsOriginalFilledMeromorphicRestriction_j_fraction_mem N hN r⟩
  map_one' := Subtype.ext ((lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    lpsOriginalJFractionEmbedding).map_one)
  map_mul' r s := Subtype.ext ((lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    lpsOriginalJFractionEmbedding).map_mul r s)
  map_zero' := Subtype.ext ((lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    lpsOriginalJFractionEmbedding).map_zero)
  map_add' r s := Subtype.ext ((lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    lpsOriginalJFractionEmbedding).map_add r s)
def lpsOriginalMeromorphicJFunctionCoefficient : Polynomial ℂ →+* (ℂ → ℂ) where
  toFun P z := P.eval (lpsOriginalJInvariant (UpperHalfPlane.ofComplex z))
  map_one' := by funext z;exact Polynomial.eval_one
  map_mul' P Q := by funext z;exact Polynomial.eval_mul
  map_zero' := by funext z;exact Polynomial.eval_zero
  map_add' P Q := by funext z;exact Polynomial.eval_add
end
end QEC.Coding.TannerLiftedProduct



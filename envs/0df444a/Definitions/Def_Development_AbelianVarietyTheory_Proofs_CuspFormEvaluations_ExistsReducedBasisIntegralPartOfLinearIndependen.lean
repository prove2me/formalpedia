-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:26.252322+00:00
-- url     : https://prove2.me/theorems/78d6fa83-10e5-4ffd-bab2-e194e2eca266
-- title:
--   Exists Reduced Basis Integral Part Of Linear Independen
-- statement:
--   Definitions and structural lemmas for Exists Reduced Basis Integral Part Of Linear Independen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
namespace GlobalTheory
namespace MvPoly
variable {K σ : Type*} [Field K]
def integralPart (W : Submodule K (MvPolynomial σ K)) : Submodule ℤ (MvPolynomial σ K) :=
  W.restrictScalars ℤ ⊓ coeffsIn σ (integralClosure ℤ K).toSubmodule
theorem mem_integralPart {W : Submodule K (MvPolynomial σ K)} {P : MvPolynomial σ K} :
    P ∈ integralPart W ↔ P ∈ W ∧ ∀ α, IsIntegral ℤ (P.coeff α) := Iff.rfl
variable [NumberField K] [Fintype σ]
def conjCoeffs (K σ : Type*) [Field K] [NumberField K] [Fintype σ] [DecidableEq σ] (D : ℕ) :
    MvPolynomial σ K →+ EuclideanSpace ℂ ((K →+* ℂ) × monomialsLE σ D) where
  toFun P := WithLp.toLp 2 fun p => p.1 (P.coeff p.2)
  map_zero' := by ext; simp
  map_add' P Q := by ext; simp
example : (X 0 : MvPolynomial (Fin 1) ℚ) ∈ integralPart (span ℚ {X 0}) ∧
    (1 / 2 : ℚ) • (X 0 : MvPolynomial (Fin 1) ℚ) ∉ integralPart (span ℚ {X 0}) := by
  refine ⟨⟨mem_span_singleton_self _, fun α => ?_⟩, fun h => ?_⟩
  · change IsIntegral ℤ (coeff α (X 0))
    rw [coeff_X]
    split_ifs
    exacts [isIntegral_one, isIntegral_zero]
  · have h1 := (mem_integralPart.1 h).2 (Finsupp.single 0 1)
    rw [coeff_smul, coeff_X, if_pos rfl, smul_eq_mul, mul_one] at h1
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
    rw [eq_intCast] at hm
    have h2 : (2 * m : ℤ) = 1 := by exact_mod_cast (by rw [hm]; norm_num : (2 * m : ℚ) = 1)
    omega
end MvPoly
end GlobalTheory



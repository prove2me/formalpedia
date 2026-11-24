-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:12.653793+00:00
-- url     : https://prove2.me/theorems/dbcbd5f9-bf16-4e5a-8b19-47a208c10390
-- title:
--   Rest Cut Basic
-- statement:
--   Definitions and structural lemmas for Rest Cut Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace KRest
open MvPolynomial
noncomputable section
def psiPolyFun {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) : MvPolynomial σ ℚ :=
  ∑ β ∈ P.support, monomial β (ψ (coeff β P))
theorem coeff_psiPolyFun {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) (β : σ →₀ ℕ) :
    coeff β (psiPolyFun ψ P) = ψ (coeff β P) := by
  classical
  rw [psiPolyFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [mem_support_iff, not_not] at h
    rw [h, map_zero]
def psiPoly {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) : MvPolynomial σ ℝ →+ MvPolynomial σ ℚ :=
  AddMonoidHom.mk' (psiPolyFun ψ) fun P Q => by
    ext β
    simp only [coeff_psiPolyFun, coeff_add, map_add]
end
end KRest
end GroundTheory.Heights₂.Heights



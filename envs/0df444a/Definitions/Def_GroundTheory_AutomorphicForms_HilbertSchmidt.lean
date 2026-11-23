-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
-- name    : GroundTheory_AutomorphicForms_HilbertSchmidt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:56.277383+00:00
-- url     : https://prove2.me/theorems/73388edd-0c09-4b5a-8ccc-8290c18e054a
-- title:
--   Hilbert Schmidt
-- statement:
--   Definitions and structural lemmas for Hilbert Schmidt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
section Auxiliary
theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  rcases eq_or_ne b ∞ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]
end Auxiliary
section HilbertSchmidt
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]
variable (𝕜 H) in

def stdHilbertBasis : HilbertBasis (exists_hilbertBasis 𝕜 H).choose 𝕜 H :=
  (exists_hilbertBasis 𝕜 H).choose_spec.choose
def hsNormSq (T : H →L[𝕜] K) : ℝ≥0∞ := ∑' i, ‖T (stdHilbertBasis 𝕜 H i)‖ₑ ^ 2
def IsHilbertSchmidt (T : H →L[𝕜] K) : Prop := hsNormSq T < ∞
def hsNorm (T : H →L[𝕜] K) : ℝ := √(hsNormSq T).toReal
theorem hsNormSq_zero : hsNormSq (0 : H →L[𝕜] K) = 0 := by
  simp [hsNormSq]
theorem hsNormSq_smul (c : 𝕜) (T : H →L[𝕜] K) : hsNormSq (c • T) = ‖c‖ₑ ^ 2 * hsNormSq T := by
  simp only [hsNormSq, smul_apply, enorm_smul, mul_pow, ENNReal.tsum_mul_left]
theorem hsNormSq_add_le (S T : H →L[𝕜] K) :
    hsNormSq (S + T) ≤ 2 * hsNormSq S + 2 * hsNormSq T := by
  simp only [hsNormSq, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  calc ‖(S + T) _‖ₑ ^ 2 ≤ (‖S _‖ₑ + ‖T _‖ₑ) ^ 2 := by
        gcongr; exact enorm_add_le _ _
    _ ≤ _ := ennreal_add_sq_le _ _
variable (𝕜 H K) in

def hilbertSchmidt : Submodule 𝕜 (H →L[𝕜] K) where
  carrier := {T | IsHilbertSchmidt T}
  add_mem' {S T} hS hT := by
    refine (hsNormSq_add_le S T).trans_lt ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hS, ENNReal.mul_lt_top (by simp) hT⟩
  zero_mem' := by
    show hsNormSq (0 : H →L[𝕜] K) < ∞
    simp [hsNormSq_zero]
  smul_mem' c T hT := by
    show hsNormSq (c • T) < ∞
    rw [hsNormSq_smul]
    exact ENNReal.mul_lt_top (by simp) hT
end HilbertSchmidt
end
end GroundTheory.Automorphic



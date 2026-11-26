-- Prove2me | solution 1 for Auto.aux_CuboidNorm.finite_jump_energy_lower_of_cube_dom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:54:35.7849+00:00
-- url     : https://prove2.me/submissions/171bf675-2535-402c-957d-31dcff32eb96

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_count_enorm_rpow_eq_finset
public import Theorems.Thm_Auto_aux_CuboidNorm_count_energy_mul_le_eLpNorm_two_sq_of_cube_dom
public import Theorems.Thm_Auto_aux_CuboidNorm_finite_energy_factor

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n J : ℕ}
    {ε c : ℝ} (hε : ε ≤ 1) (hc : 0 ≤ c)
    (A : Finset (ZVector n)) (d : Fin J → ZVector n → ℝ)
    (G : Fin J → RVector n → ℝ)
    (hsupport : ∀ j k, k ∉ A → c * d j k = 0)
    (hdom : ∀ j k, k ∈ A → ∀ x, x ∈ latticeCuboid ε k →
      ‖c * d j k‖ₑ ≤ ‖G j x‖ₑ) :
    (ENNReal.ofReal c ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
        ∑ j : Fin J, ∑ k ∈ A, ‖d j k‖ₑ ^ (2 : ℝ) ≤
      ∑ j : Fin J, eLpNorm (G j) (2 : ℝ≥0∞) volume ^ (2 : ℕ) := by
  calc
    (ENNReal.ofReal c ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
        ∑ j : Fin J, ∑ k ∈ A, ‖d j k‖ₑ ^ (2 : ℝ) =
        ∑ j : Fin J,
          ((ENNReal.ofReal c ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
            ∑ k ∈ A, ‖d j k‖ₑ ^ (2 : ℝ)) := by
          rw [Finset.mul_sum]
    _ = ∑ j : Fin J,
          ((∫⁻ k, ‖c * d j k‖ₑ ^ (2 : ℝ) ∂Measure.count) *
            ∏ _ : Fin n, ENNReal.ofReal ε) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [lintegral_count_enorm_rpow_eq_finset A (fun k ↦ c * d j k) 2
            (by norm_num) (hsupport j)]
          exact (finite_energy_factor A ε c hc (d j)).symm
    _ ≤ ∑ j : Fin J, eLpNorm (G j) (2 : ℝ≥0∞) volume ^ (2 : ℕ) := by
          apply Finset.sum_le_sum
          intro j hj
          exact count_energy_mul_le_eLpNorm_two_sq_of_cube_dom hε A (d j) (G j)
            (hsupport j) (hdom j)
end Auto.aux_CuboidNorm

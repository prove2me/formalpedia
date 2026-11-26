-- Prove2me | solution 1 for Auto.aux_CuboidNorm.count_energy_mul_le_lintegral_of_cube_dom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:52:07.257902+00:00
-- url     : https://prove2.me/submissions/0ad6e5ff-974d-419c-b62d-532e65db6efe

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_finiteLatticeCubeStep_eq_count_mul
public import Theorems.Thm_Auto_aux_CuboidNorm_finiteLatticeCubeStep_enorm_le_of_cube_dom

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
theorem _root_.solution {n : ℕ}
    {ε c : ℝ} (hε : ε ≤ 1) (A : Finset (ZVector n))
    (a : ZVector n → ℝ) (G : RVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → c * a k = 0)
    (hdom : ∀ k, k ∈ A → ∀ x, x ∈ latticeCuboid ε k →
      ‖c * a k‖ₑ ≤ ‖G x‖ₑ) :
    (∫⁻ k, ‖c * a k‖ₑ ^ (2 : ℝ) ∂Measure.count) *
        ∏ _ : Fin n, ENNReal.ofReal ε ≤
      ∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂volume := by
  rw [← lintegral_finiteLatticeCubeStep_eq_count_mul hε A (fun k ↦ c * a k)
    hsupport 2 (by norm_num)]
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow
    (finiteLatticeCubeStep_enorm_le_of_cube_dom hε A a G hdom x) (by norm_num)
end Auto.aux_CuboidNorm

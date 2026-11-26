-- Prove2me | solution 1 for Auto.aux_CuboidNorm.count_energy_mul_le_eLpNorm_two_sq_of_cube_dom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:28.133588+00:00
-- url     : https://prove2.me/submissions/d1737351-7343-4580-bc21-97bc2bd14958

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_count_energy_mul_le_lintegral_of_cube_dom
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_two_sq_nat

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
      eLpNorm G (2 : ℝ≥0∞) volume ^ (2 : ℕ) := by
  rw [eLpNorm_two_sq_nat]
  have h := count_energy_mul_le_lintegral_of_cube_dom hε A a G hsupport hdom
  convert h using 1
  norm_num [ENNReal.rpow_natCast]
end Auto.aux_CuboidNorm

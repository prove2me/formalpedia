-- Prove2me | solution 1 for Auto.aux_CuboidNorm.lintegral_finiteLatticeCubeStep_eq_count_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:50:55.7968+00:00
-- url     : https://prove2.me/submissions/364b5e48-345e-4a8d-bb46-6f21603ae065

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_count_enorm_rpow_eq_finset
public import Theorems.Thm_Auto_aux_CuboidNorm_volume_latticeCuboid
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_finiteLatticeCubeStep_enorm_rpow

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
    {ε : ℝ} (hε : ε ≤ 1) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (q : ℝ) (hq : 0 < q) :
    (∫⁻ x, ‖finiteLatticeCubeStep ε A a x‖ₑ ^ q ∂volume) =
      (∫⁻ k, ‖a k‖ₑ ^ q ∂Measure.count) *
        ∏ _ : Fin n, ENNReal.ofReal ε := by
  rw [lintegral_finiteLatticeCubeStep_enorm_rpow hε A a q hq]
  calc
    (∑ k ∈ A, ‖a k‖ₑ ^ q * volume (latticeCuboid ε k)) =
        (∑ k ∈ A, ‖a k‖ₑ ^ q) * ∏ _ : Fin n, ENNReal.ofReal ε := by
          simp_rw [volume_latticeCuboid]
          rw [← Finset.sum_mul]
    _ = (∫⁻ k, ‖a k‖ₑ ^ q ∂Measure.count) *
        ∏ _ : Fin n, ENNReal.ofReal ε := by
          rw [lintegral_count_enorm_rpow_eq_finset A a q hq hsupport]
end Auto.aux_CuboidNorm

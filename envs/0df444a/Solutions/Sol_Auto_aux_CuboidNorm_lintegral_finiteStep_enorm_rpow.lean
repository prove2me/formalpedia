-- Prove2me | solution 1 for Auto.aux_CuboidNorm.lintegral_finiteStep_enorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:48:50.563238+00:00
-- url     : https://prove2.me/submissions/1b37f76d-d29a-4bbb-9062-03eb58198024

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_finiteStep_enorm_rpow

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
omit [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution (μ : Measure α) (A : Finset κ)
    (s : κ → Set α) (a : κ → ℝ) (q : ℝ) (hq : 0 < q)
    (hmeas : ∀ k ∈ A, MeasurableSet (s k))
    (hdisj : ∀ ⦃k⦄, k ∈ A → ∀ ⦃l⦄, l ∈ A → k ≠ l → Disjoint (s k) (s l)) :
    (∫⁻ x, ‖finiteStep A s a x‖ₑ ^ q ∂μ) =
      ∑ k ∈ A, ‖a k‖ₑ ^ q * μ (s k) := by
  simp_rw [finiteStep_enorm_rpow A s a q hq hdisj]
  rw [lintegral_finsetSum A]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [lintegral_indicator_const (hmeas k hk)]
  · intro k hk
    exact measurable_const.indicator (hmeas k hk)
end Auto.aux_CuboidNorm

-- Prove2me | solution 1 for Auto.aux_ErgodicBox.finite_box_orbit_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:54:22.911623+00:00
-- url     : https://prove2.me/submissions/90129acd-85d7-4f7d-9f4e-cecaae3beff6

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_two_sq_nat
public import Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_two_sq_nat
public import Theorems.Thm_Auto_aux_ErgodicBox_lintegral_finite_orbit_sum

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution
    {X κ : Type*} [MeasurableSpace X] {μ : Measure X}
    (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    {J : ℕ} (d : Fin J → X → ℝ)
    (hd : ∀ j, AEStronglyMeasurable (d j) μ)
    (D : X → ℝ≥0∞)
    (hpoint : ∀ x, ∑ j : Fin J, ∑ k ∈ B,
      ‖d j (T k x)‖ₑ ^ (2 : ℕ) ≤ D x) :
    (B.card : ℝ≥0∞) * ∑ j : Fin J, eLpNorm (d j) 2 μ ^ 2 ≤
      ∫⁻ x, D x ∂μ := by
  calc
    (B.card : ℝ≥0∞) * ∑ j : Fin J, eLpNorm (d j) 2 μ ^ 2 =
        (B.card : ℝ≥0∞) * ∑ j : Fin J,
          ∫⁻ x, ‖d j x‖ₑ ^ (2 : ℕ) ∂μ := by
      apply congrArg (fun z : ℝ≥0∞ ↦ (B.card : ℝ≥0∞) * z)
      apply Finset.sum_congr rfl
      intro j _
      exact eLpNorm_two_sq_nat μ (d j)
    _ = ∫⁻ x, ∑ j : Fin J, ∑ k ∈ B,
        ‖d j (T k x)‖ₑ ^ (2 : ℕ) ∂μ :=
      (lintegral_finite_orbit_sum μ B T hT d hd).symm
    _ ≤ ∫⁻ x, D x ∂μ := lintegral_mono hpoint
end Auto.aux_ErgodicBox

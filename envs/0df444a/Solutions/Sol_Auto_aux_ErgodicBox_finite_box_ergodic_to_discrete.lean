-- Prove2me | solution 1 for Auto.aux_ErgodicBox.finite_box_ergodic_to_discrete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:10.208663+00:00
-- url     : https://prove2.me/submissions/2e270b62-b676-4d10-8dab-8f262fe51199

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_finite_box_orbit_lower_bound

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
    (B B' : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    {J : ℕ} (d : Fin J → X → ℝ)
    (hd : ∀ j, AEStronglyMeasurable (d j) μ)
    (A P : ℝ≥0∞) (D Q : X → ℝ≥0∞)
    (hpoint : ∀ x, ∑ j : Fin J, ∑ k ∈ B,
      ‖d j (T k x)‖ₑ ^ (2 : ℕ) ≤ D x)
    (hdiscrete : ∀ x, D x ≤ A * Q x)
    (hQmeas : AEMeasurable Q μ)
    (hright : ∫⁻ x, Q x ∂μ ≤ (B'.card : ℝ≥0∞) * P) :
    (B.card : ℝ≥0∞) * ∑ j : Fin J, eLpNorm (d j) 2 μ ^ 2 ≤
      A * ((B'.card : ℝ≥0∞) * P) := by
  calc
    (B.card : ℝ≥0∞) * ∑ j : Fin J, eLpNorm (d j) 2 μ ^ 2 ≤
        ∫⁻ x, D x ∂μ :=
      finite_box_orbit_lower_bound B T hT d hd D hpoint
    _ ≤ ∫⁻ x, A * Q x ∂μ := lintegral_mono hdiscrete
    _ = A * ∫⁻ x, Q x ∂μ := lintegral_const_mul'' A hQmeas
    _ ≤ A * ((B'.card : ℝ≥0∞) * P) := mul_le_mul_right hright A
end Auto.aux_ErgodicBox

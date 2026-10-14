-- Prove2me | solution 1 for Apery.block_A
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T00:45:53.091332+00:00
-- url     : https://prove2.me/submissions/bf82d4b7-f9c2-447f-ac5d-8ac7582010fc

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# Block (A) — the self-energy of a circle equals $(2\pi)^2 \log \varepsilon$

This file proves the platform theorem `Apery.block_A`:

  `Plog t ε (Sum.inl i) (Sum.inl i) = (2π)² log ε`

directly from Mathlib's circle-average log-potential identity
(`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`), as a faithful port of the
pinned source project mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/CircleAtoms.lean` (the circle integrals) and `Apery/EnergyBlocks.lean` (block (A)).
No open theorems are imported: this is a direct proof.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic
import Definitions.Def_Zeta5_SourceEnergy
import Definitions.Def_Zeta5_SourceAtoms

set_option autoImplicit false

section Port0
/-!
# Block (A): the self-energy of a circle

`Plog t ε (inl i) (inl i) = (2π)² log ε`, from Mathlib's circle-average log-potential
identity. Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/CircleAtoms.lean` (circle integrals) and `Apery/EnergyBlocks.lean` (block (A)).
-/

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Apery

/-- `∫₀^{2π} log ‖circleMap c R θ - a‖ = 2π (log R + log⁺ (R⁻¹ ‖c - a‖))`. -/
lemma circle_log_integral (c a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    ∫ θ in (0:ℝ)..2 * π, Real.log ‖circleMap c R θ - a‖ =
      2 * π * (Real.log R + log⁺ (R⁻¹ * ‖c - a‖)) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := a) (c := c) hR
  rw [circleAverage_def, smul_eq_mul] at h
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  rw [← h, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]

lemma norm_circleMap_sub_center' (c : ℝ) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) :
    ‖(c : ℂ) - circleMap c ε θ‖ = ε := by
  rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]

lemma circle_log_integral' (c a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    ∫ θ in (0:ℝ)..2 * π, Real.log ‖a - circleMap c R θ‖ =
      2 * π * (Real.log R + log⁺ (R⁻¹ * ‖c - a‖)) := by
  rw [← circle_log_integral c a hR]
  apply integral_congr
  intro θ _
  simp only
  rw [norm_sub_rev]

/-- (A): the self-energy of a circle. -/
lemma block_A {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin h) :
    Plog t ε (Sum.inl i) (Sum.inl i) = (2 * π) ^ 2 * Real.log ε := by
  unfold Plog pairInt
  have hin : ∀ θ, (∫ φ in (0:ℝ)..2 * π,
      Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inl i) φ‖) = 2 * π * Real.log ε := by
    intro θ
    simp only [atomγ]
    rw [circle_log_integral' _ _ hε.ne', norm_circleMap_sub_center' _ hε, inv_mul_cancel₀ hε.ne',
      (posLog_eq_zero_iff _).mpr (by simp), add_zero]
  simp_rw [hin]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

end Apery
end Port0


open MeasureTheory Real Polynomial Finset in
/-- The platform target `Apery.block_A`, restated at top level as `solution`. -/
theorem solution {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin h) :
    Apery.Plog t ε (Sum.inl i) (Sum.inl i) = (2 * Real.pi) ^ 2 * Real.log ε :=
  Apery.block_A t hε i

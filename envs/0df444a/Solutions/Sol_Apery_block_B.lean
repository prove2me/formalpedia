-- Prove2me | solution 1 for Apery.block_B
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T00:51:46.917324+00:00
-- url     : https://prove2.me/submissions/f93c63e9-3a33-4fe5-83cd-9ea1d22982dc

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# Block (B) — the mutual energy of two circles

This file proves the platform theorem `Apery.block_B`:

  `(2π)² log|tᵢ - tᵢ'| ≤ Plog t ε (Sum.inl i) (Sum.inl i')`

directly from Mathlib's circle-average log-potential identity and the countability of the
point preimages under `circleMap`, as a faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/CircleAtoms.lean` and
`Apery/EnergyBlocks.lean` (blocks (A) and (B)). The inner interval-integrability is proved
directly from the explicit value of the inner integral (continuity of `log⁺`), instead of
the product-integrability chain of `Apery/EnergyAtoms.lean`. Only definitions are imported:
this is a direct proof.
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

section Port1
/-!
# Block (B): the mutual energy of two circles

`(2π)² log|tᵢ - tᵢ'| ≤ Plog t ε (inl i) (inl i')`, from the circle log-potential identity.
Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/CircleAtoms.lean`
(the circle integrals and the countability of the point preimages) and `Apery/EnergyBlocks.lean`
(block (B)), with the inner interval-integrability proved directly from the explicit value of
the inner integral instead of the product-integrability chain.
-/

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Apery

lemma circle_log_integrable (c a : ℂ) (R : ℝ) :
    IntervalIntegrable (fun θ => Real.log ‖circleMap c R θ - a‖) volume 0 (2 * π) :=
  circleIntegrable_log_norm_sub_const R

lemma log_le_log_add_posLog {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    Real.log x ≤ Real.log ε + log⁺ (ε⁻¹ * x) := by
  have h1 : Real.log (ε⁻¹ * x) ≤ log⁺ (ε⁻¹ * x) := le_max_right _ _
  rw [Real.log_mul (inv_ne_zero hε.ne') hx.ne', Real.log_inv] at h1
  linarith

/-- Point preimages under `circleMap` are countable. -/
lemma circleMap_preimage_countable (c : ℂ) {R : ℝ} (hR : R ≠ 0) (z : ℂ) :
    (circleMap c R ⁻¹' {z}).Countable := by
  rcases (circleMap c R ⁻¹' {z}).eq_empty_or_nonempty with h | ⟨θ₀, hθ₀⟩
  · rw [h]; exact Set.countable_empty
  refine (Set.countable_range fun n : ℤ => θ₀ + n * (2 * π)).mono ?_
  intro θ hθ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, circleMap] at hθ hθ₀
  have he : Complex.exp (θ * Complex.I) = Complex.exp (θ₀ * Complex.I) := by
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
    have := hθ.trans hθ₀.symm
    have h2 : (R : ℂ) * Complex.exp (θ * Complex.I) = R * Complex.exp (θ₀ * Complex.I) := by
      linear_combination this
    exact mul_left_cancel₀ hR' h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  refine ⟨n, ?_⟩
  have : (θ : ℂ) = θ₀ + n * (2 * π) := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h3 : (θ : ℂ) * Complex.I = (θ₀ + n * (2 * π)) * Complex.I := by
      rw [hn]; ring
    exact mul_right_cancel₀ hI h3
  exact_mod_cast this.symm

/-- The inner integral of the circle–circle block is interval integrable. -/
lemma inner_intervalIntegrable_circles {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε)
    (i i' : Fin h) :
    IntervalIntegrable (fun θ => ∫ φ in (0:ℝ)..2 * π,
      Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inl i') φ‖) volume 0 (2 * π) := by
  have hcont : Continuous fun θ : ℝ => 2 * π * (Real.log ε +
      log⁺ (ε⁻¹ * ‖(t i' : ℂ) - circleMap (t i) ε θ‖)) := by
    fun_prop
  refine (hcont.intervalIntegrable 0 (2 * π)).congr ?_
  intro θ _
  simp only [atomγ]
  rw [circle_log_integral' (t i') (circleMap (t i) ε θ) hε.ne', norm_sub_rev]

/-- (B): the mutual energy of two circles dominates `log |tᵢ - tᵢ'|`. -/
lemma block_B {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i i' : Fin h) (hne : t i ≠ t i') :
    (2 * π) ^ 2 * Real.log |t i - t i'| ≤ Plog t ε (Sum.inl i) (Sum.inl i') := by
  unfold Plog pairInt
  have hin : ∀ θ, circleMap (t i) ε θ ≠ (t i' : ℂ) →
      2 * π * Real.log ‖circleMap (t i) ε θ - t i'‖ ≤
        ∫ φ in (0:ℝ)..2 * π, Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inl i') φ‖ := by
    intro θ hθ
    simp only [atomγ]
    rw [circle_log_integral' _ _ hε.ne', norm_sub_rev (t i' : ℂ)]
    have := log_le_log_add_posLog hε (norm_pos_iff.mpr (sub_ne_zero.mpr hθ))
    nlinarith [Real.pi_pos]
  have h1 : (∫ θ in (0:ℝ)..2 * π, 2 * π * Real.log ‖circleMap (t i) ε θ - t i'‖) ≤
      ∫ θ in (0:ℝ)..2 * π, ∫ φ in (0:ℝ)..2 * π,
        Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inl i') φ‖ := by
    refine intervalIntegral.integral_mono_ae (by positivity)
      ((circle_log_integrable _ _ _).const_mul _) (inner_intervalIntegrable_circles t hε _ _) ?_
    have hc := (circleMap_preimage_countable (t i) hε.ne' (t i')).measure_zero (volume : Measure ℝ)
    filter_upwards [compl_mem_ae_iff.mpr hc] with θ hθ
    exact hin θ hθ
  have h2 : (∫ θ in (0:ℝ)..2 * π, 2 * π * Real.log ‖circleMap (t i) ε θ - t i'‖) =
      2 * π * (2 * π * (Real.log ε + log⁺ (ε⁻¹ * ‖(t i : ℂ) - t i'‖))) := by
    rw [intervalIntegral.integral_const_mul, circle_log_integral _ _ hε.ne']
  have h3 : Real.log |t i - t i'| ≤ Real.log ε + log⁺ (ε⁻¹ * ‖(t i : ℂ) - t i'‖) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact log_le_log_add_posLog hε (abs_pos.mpr (sub_ne_zero.mpr hne))
  nlinarith [Real.pi_pos]

end Apery
end Port1


open MeasureTheory Real Polynomial Finset in
/-- The platform target `Apery.block_B`, restated at top level as `solution`. -/
theorem solution {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i i' : Fin h) (hne : t i ≠ t i') :
    (2 * Real.pi) ^ 2 * Real.log |t i - t i'| ≤ Apery.Plog t ε (Sum.inl i) (Sum.inl i') :=
  Apery.block_B t hε i i' hne

-- Prove2me | solution 1 for Apery.pairInt_log_symm
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T13:30:28.903847+00:00
-- url     : https://prove2.me/submissions/e8ff3327-5660-41b5-a217-e68fbcf923bb

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# Symmetry of the logarithmic pair integrals

This file proves the platform theorem `Apery.pairInt_log_symm`:

  `pairInt (atomγ t ε) (fun z w => log ‖z-w‖) k l =
     pairInt (atomγ t ε) (fun z w => log ‖z-w‖) l k`

directly from the torus integrability of the logarithmic kernel on each pair of atoms
(Fubini on the product of two circles). The development is a faithful port of the pinned
source project mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/EnergyAtoms.lean` (the hypotheses of `energy_log_nonpos`), `Apery/EnergyLimit.lean`
(`pairInt` as a product integral) and `Apery/CircleAtoms.lean` (`cos_preimage_countable`).
Only definitions are imported: this is a direct proof.
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

section Port2
/-!
# Block (D): the arcsine–arcsine energy

`(2π)² log((b_{j'}-a_{j'})/4) ≤ Plog t ε (inr j) (inr j')`, from the closed form (A.1) of
the arcsine potential. Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/ArcsineAtoms.lean`, `Apery/ArcsinePotential.lean` (through `arc_potential_real`),
`Apery/CircleAtoms.lean` and `Apery/EnergyBlocks.lean` (blocks (D)). The inner
interval-integrability is obtained from the log-max representation of `Uω` and continuity of
`log⁺`/`Uω` along the arcsine curve, instead of the product-integrability chain.
-/

open MeasureTheory Set Real intervalIntegral Filter Topology Finset

namespace Apery

lemma aρ_lt_bρ : ∀ j ∈ Finset.Icc 1 16, aρ j < bρ j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [aρ, bρ, table1]

lemma rρ_pos (j : Fin 16) : 0 < rρ (j + 1) := by
  have := aρ_lt_bρ (j + 1) (by simp only [Finset.mem_Icc]; omega)
  unfold rρ; linarith

lemma Uω_of_mem {a b t : ℝ} (h1 : a ≤ t) (h2 : t ≤ b) : Uω a b t = Real.log ((b - a) / 4) := by
  simp [Uω, h1, h2]

/-- `Uω a b t ≥ log ((b - a)/4)` for all `t`. -/
lemma log_le_Uω {a b : ℝ} (hab : a < b) (t : ℝ) : Real.log ((b - a) / 4) ≤ Uω a b t := by
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [Uω_of_mem h.1 h.2]
  · unfold Uω
    rw [if_neg h]
    have hs := Real.sqrt_nonneg ((t - a) * (t - b))
    have h1 : (b - a) / 2 ≤ |t - (a + b) / 2| := by
      rw [le_abs]
      rcases not_and_or.mp h with h | h
      · right; linarith [not_le.mp h]
      · left; linarith [not_le.mp h]
    apply Real.log_le_log (by linarith)
    linarith

/-- The log-max representation of the arcsine potential:
`Uω a b = log ∘ max ((b-a)/4) ((|t - (a+b)/2| + √((t-a)(t-b)))/2)`. -/
lemma Uω_eq_log_max {a b : ℝ} (hab : a < b) :
    Uω a b = fun t => Real.log (max ((b - a) / 4)
      ((|t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2)) := by
  funext t
  set g : ℝ := (|t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2 with hg
  by_cases h : a ≤ t ∧ t ≤ b
  · have hgc : g ≤ (b - a) / 4 := by
      rw [hg]
      have hsqrt : Real.sqrt ((t - a) * (t - b)) = 0 :=
        Real.sqrt_eq_zero_of_nonpos (by nlinarith [h.1, h.2])
      rw [hsqrt, add_zero]
      have hA : |t - (a + b) / 2| ≤ (b - a) / 2 := by rw [abs_le]; constructor <;> linarith
      linarith
    rw [Uω, if_pos h]
    show Real.log ((b - a) / 4) = Real.log (max ((b - a) / 4) g)
    rw [show max ((b - a) / 4) g = (b - a) / 4 from
      le_antisymm (max_le le_rfl hgc) (le_max_left _ _)]
  · have hcg : (b - a) / 4 ≤ g := by
      rw [hg]
      rcases not_and_or.mp h with hta | hbt
      · have ht : t < a := not_le.mp hta
        have habs : |t - (a + b) / 2| = (a + b) / 2 - t := by
          rw [abs_of_neg (by linarith), neg_sub]
        rw [habs]
        have : (b - a) / 2 - ((a + b) / 2 - t) < 0 := by linarith
        linarith [Real.sqrt_nonneg ((t - a) * (t - b))]
      · have ht : b < t := not_le.mp hbt
        have habs : |t - (a + b) / 2| = t - (a + b) / 2 := by
          rw [abs_of_nonneg (by linarith)]
        rw [habs]
        have : (b - a) / 2 - (t - (a + b) / 2) < 0 := by linarith
        linarith [Real.sqrt_nonneg ((t - a) * (t - b))]
    rw [Uω, if_neg h]
    show Real.log g = Real.log (max ((b - a) / 4) g)
    rw [show max ((b - a) / 4) g = g from le_antisymm (max_le hcg le_rfl) (le_max_right _ _)]

/-- Continuity of `θ ↦ Uω a b (m + r cos θ)`. -/
lemma continuous_arcUω (a b m r : ℝ) (hab : a < b) :
    Continuous fun θ : ℝ => 2 * π * Uω a b (m + r * Real.cos θ) := by
  rw [Uω_eq_log_max hab]
  apply Continuous.const_mul
  apply Continuous.log
  · fun_prop
  · intro θ
    have hb : 0 < (b - a) / 4 := by linarith
    exact ne_of_gt (lt_of_lt_of_le hb (le_max_left _ _))

/-! ### The circle integrals on the unit circle -/

lemma circle_log_integral_zero_one (a : ℂ) :
    ∫ θ in (0:ℝ)..2 * π, Real.log ‖circleMap 0 1 θ - a‖ = 2 * π * log⁺ ‖a‖ := by
  rw [circle_log_integral 0 a one_ne_zero]
  simp

lemma cos_eq_half_add_inv (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) = (circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, circleMap_zero]
  simp only [Complex.ofReal_one, one_mul]
  rw [← Complex.exp_neg]
  ring_nf

lemma norm_circleMap_zero_one (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  simp [circleMap]

/-! ### The arcsine atoms -/

lemma continuous_arcCurve (m r : ℝ) : Continuous (arcCurve m r) := by
  unfold arcCurve; fun_prop

lemma norm_arcCurve_le (m r θ : ℝ) : ‖arcCurve m r θ‖ ≤ |m| + |r| := by
  unfold arcCurve
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc |m + r * Real.cos θ| ≤ |m| + |r * Real.cos θ| := abs_add_le _ _
    _ ≤ |m| + |r| := by
      rw [abs_mul]
      have := Real.abs_cos_le_one θ
      nlinarith [abs_nonneg r]

/-- The factorisation of `z - y(θ)`. -/
lemma sub_arcCurve_eq {z : ℂ} {m r : ℝ} (hr : r ≠ 0) (θ : ℝ) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    z - arcCurve m r θ = -(r / (2 * circleMap 0 1 θ)) *
      ((circleMap 0 1 θ - ((z - m) / r + sq)) * (circleMap 0 1 θ - ((z - m) / r - sq))) := by
  have hw : circleMap 0 1 θ ≠ 0 := by
    intro h; have := norm_circleMap_zero_one θ; rw [h] at this; simp at this
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have e1 : (circleMap 0 1 θ - ((z - m) / r + sq)) * (circleMap 0 1 θ - ((z - m) / r - sq)) =
      circleMap 0 1 θ ^ 2 - 2 * ((z - m) / r) * circleMap 0 1 θ + 1 := by
    linear_combination (-1 : ℂ) * hsq
  rw [e1]
  simp only [arcCurve, Complex.ofReal_add, Complex.ofReal_mul]
  rw [cos_eq_half_add_inv]
  field_simp
  ring

lemma norm_sub_arcCurve {z : ℂ} {m r : ℝ} (hr : 0 < r) (θ : ℝ) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    ‖z - arcCurve m r θ‖ = r / 2 * (‖circleMap 0 1 θ - ((z - m) / r + sq)‖ *
      ‖circleMap 0 1 θ - ((z - m) / r - sq)‖) := by
  rw [sub_arcCurve_eq hr.ne' θ hsq, norm_mul, norm_neg, norm_div, norm_mul, norm_mul,
    norm_circleMap_zero_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simp

/-- The exceptional set is countable. -/
lemma arc_exceptional_countable (q₁ q₂ : ℂ) :
    ({θ : ℝ | circleMap 0 1 θ = q₁ ∨ circleMap 0 1 θ = q₂}).Countable := by
  have : {θ : ℝ | circleMap 0 1 θ = q₁ ∨ circleMap 0 1 θ = q₂} =
      circleMap 0 1 ⁻¹' {q₁} ∪ circleMap 0 1 ⁻¹' {q₂} := by
    ext θ; simp
  rw [this]
  exact (circleMap_preimage_countable 0 one_ne_zero q₁).union
    (circleMap_preimage_countable 0 one_ne_zero q₂)

lemma arc_log_ae {z : ℂ} {m r : ℝ} (hr : 0 < r) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    ∀ᵐ θ ∂(volume : Measure ℝ), Real.log ‖z - arcCurve m r θ‖ =
      Real.log (r / 2) + Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
        Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖ := by
  have h0 := (arc_exceptional_countable ((z - m) / r + sq) ((z - m) / r - sq)).measure_zero
    (volume : Measure ℝ)
  filter_upwards [compl_mem_ae_iff.mpr h0] with θ hθ
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or] at hθ
  rw [norm_sub_arcCurve hr θ hsq, Real.log_mul (by positivity) (by
      apply mul_ne_zero <;> exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by tauto))),
    Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hθ.1))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hθ.2)), add_assoc]

lemma arc_log_integrable {z : ℂ} {m r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun θ => Real.log ‖z - arcCurve m r θ‖) volume 0 (2 * π) := by
  set sq : ℂ := (((z - m) / r) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq_def
  have hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1 := Complex.cpow_nat_inv_pow _ two_ne_zero
  have hg : IntervalIntegrable (fun θ => Real.log (r / 2) +
      Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
        Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖) volume 0 (2 * π) :=
    (intervalIntegrable_const.add (circle_log_integrable 0 _ 1)).add (circle_log_integrable 0 _ 1)
  refine hg.congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [arc_log_ae hr hsq] with θ hθ
  exact hθ.symm

/-- The arcsine potential at a complex point: `∫₀^{2π} log ‖z - y(θ)‖ dθ`. -/
lemma arc_log_integral {z : ℂ} {m r : ℝ} (hr : 0 < r) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    ∫ θ in (0:ℝ)..2 * π, Real.log ‖z - arcCurve m r θ‖ =
      2 * π * (Real.log (r / 2) + log⁺ ‖(z - m) / r + sq‖ + log⁺ ‖(z - m) / r - sq‖) := by
  rw [intervalIntegral.integral_congr_ae (g := fun θ => Real.log (r / 2) +
      Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
        Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖) (by
      filter_upwards [arc_log_ae hr hsq] with θ hθ _
      exact hθ)]
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add (circle_log_integrable 0 _ 1))
    (circle_log_integrable 0 _ 1), intervalIntegral.integral_add intervalIntegrable_const
    (circle_log_integrable 0 _ 1), intervalIntegral.integral_const, circle_log_integral_zero_one,
    circle_log_integral_zero_one]
  simp only [sub_zero, smul_eq_mul]
  ring

/-! ### The arcsine potential (A.1) -/

/-- A square root of `ζ² - 1` for real `ζ`. -/
noncomputable def sqR (ζ : ℝ) : ℂ :=
  if 1 ≤ ζ ^ 2 then ((Real.sqrt (ζ ^ 2 - 1) : ℝ) : ℂ) else ((Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I

lemma sqR_sq (ζ : ℝ) : sqR ζ ^ 2 = (ζ : ℂ) ^ 2 - 1 := by
  unfold sqR
  split_ifs with h
  · rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  · rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring

/-- The value `log⁺ ‖ζ + s‖ + log⁺ ‖ζ - s‖` for real `ζ`. -/
lemma posLog_sum_real (ζ : ℝ) :
    log⁺ ‖(ζ : ℂ) + sqR ζ‖ + log⁺ ‖(ζ : ℂ) - sqR ζ‖ =
      if 1 ≤ |ζ| then Real.log (|ζ| + Real.sqrt (ζ ^ 2 - 1)) else 0 := by
  unfold sqR
  by_cases h : 1 ≤ ζ ^ 2
  · rw [if_pos h]
    have h1 : 1 ≤ |ζ| := by nlinarith [abs_nonneg ζ, sq_abs ζ]
    rw [if_pos h1]
    have hs0 : 0 ≤ Real.sqrt (ζ ^ 2 - 1) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt (ζ ^ 2 - 1) ^ 2 = ζ ^ 2 - 1 := Real.sq_sqrt (by linarith)
    rw [← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_or_gt 0 ζ with hζ | hζ
    · rw [abs_of_nonneg hζ] at h1 ⊢
      set s := Real.sqrt (ζ ^ 2 - 1) with hs
      have h2 : s ≤ ζ := Real.sqrt_le_iff.mpr ⟨hζ, by nlinarith⟩
      have h3 : 0 < ζ - s := by
        refine sub_pos.mpr (lt_of_le_of_ne h2 fun h => ?_)
        rw [h] at hs2; linarith
      have h4 : ζ - 1 ≤ s := (Real.le_sqrt (by linarith) (by nlinarith)).mpr (by nlinarith)
      have hA : 0 < ζ + s := by linarith
      rw [abs_of_pos hA, abs_of_pos h3, posLog_eq_log (by rw [abs_of_pos hA]; linarith),
        (posLog_eq_zero_iff _).mpr (by rw [abs_of_pos h3]; linarith), add_zero]
    · rw [abs_of_neg hζ] at h1 ⊢
      set s := Real.sqrt (ζ ^ 2 - 1) with hs
      have h2 : s ≤ -ζ := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      have hA' : -1 - ζ ≤ s := (Real.le_sqrt (by linarith) (by nlinarith)).mpr (by nlinarith)
      have hA : ζ + s ≤ 0 := by linarith
      have hB : ζ - s < 0 := by linarith
      have hB1 : 1 ≤ -(ζ - s) := by linarith
      rw [abs_of_nonpos hA, abs_of_neg hB,
        (posLog_eq_zero_iff _).mpr (by rw [abs_of_nonneg (by linarith)]; linarith),
        posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hB1), zero_add]
      ring_nf
  · rw [if_neg h]
    have h1 : ¬ 1 ≤ |ζ| := by
      intro h1; apply h; nlinarith [abs_nonneg ζ, sq_abs ζ]
    rw [if_neg h1]
    have hs2 : Real.sqrt (1 - ζ ^ 2) ^ 2 = 1 - ζ ^ 2 := Real.sq_sqrt (by linarith)
    have e1 : (ζ : ℂ) + ((Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I =
        (ζ : ℝ) + ((Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I := rfl
    have e2 : (ζ : ℂ) - ((Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I =
        (ζ : ℝ) + ((-Real.sqrt (1 - ζ ^ 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e1, e2, Complex.norm_add_mul_I, Complex.norm_add_mul_I, neg_sq, hs2,
      show ζ ^ 2 + (1 - ζ ^ 2) = 1 by ring, Real.sqrt_one]
    simp

/-- The closed form `Uω` in terms of `ζ = (t - m)/r`. -/
lemma Uω_eq_log_add {a b t : ℝ} (hab : a < b) :
    Uω a b t = Real.log ((b - a) / 4) +
      (if 1 ≤ |(t - (a + b) / 2) / ((b - a) / 2)| then
        Real.log (|(t - (a + b) / 2) / ((b - a) / 2)| +
          Real.sqrt (((t - (a + b) / 2) / ((b - a) / 2)) ^ 2 - 1)) else 0) := by
  set r := (b - a) / 2 with hr
  set m := (a + b) / 2 with hm
  have hr0 : 0 < r := by rw [hr]; linarith
  have hζ : |(t - m) / r| = |t - m| / r := by rw [abs_div, abs_of_pos hr0]
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [Uω_of_mem h.1 h.2]
    have h1 : |t - m| ≤ r := by rw [abs_le]; constructor <;> linarith
    have h2 : |(t - m) / r| ≤ 1 := by rw [hζ, div_le_one hr0]; exact h1
    split_ifs with h3
    · have h4 : |(t - m) / r| = 1 := le_antisymm h2 h3
      rw [← sq_abs ((t - m) / r), h4, one_pow, sub_self, Real.sqrt_zero, add_zero, Real.log_one,
        add_zero]
    · ring
  · have h1 : 1 < |(t - m) / r| := by
      rw [hζ, one_lt_div hr0, lt_abs]
      rcases not_and_or.mp h with h | h
      · right; linarith [not_le.mp h]
      · left; linarith [not_le.mp h]
    rw [if_pos h1.le]
    unfold Uω
    rw [if_neg h]
    have hpos : 0 < |t - m| / r + Real.sqrt (((t - m) / r) ^ 2 - 1) := by
      have := Real.sqrt_nonneg (((t - m) / r) ^ 2 - 1)
      rw [hζ] at h1; linarith
    rw [hζ, ← Real.log_mul (by positivity) hpos.ne']
    congr 1
    have e : (t - a) * (t - b) = r ^ 2 * (((t - m) / r) ^ 2 - 1) := by
      have hba : b - a ≠ 0 := by linarith
      rw [hr, hm]; field_simp; ring
    rw [e, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0.le]
    rw [show (b - a) / 4 = r / 2 by rw [hr]; ring, ← hm]
    field_simp

/-- **(A.1)**: the arcsine potential at a real point. -/
lemma arc_potential_real {a b : ℝ} (hab : a < b) (t : ℝ) :
    ∫ θ in (0:ℝ)..2 * π, Real.log ‖(t : ℂ) - arcCurve ((a + b) / 2) ((b - a) / 2) θ‖ =
      2 * π * Uω a b t := by
  have hr0 : 0 < (b - a) / 2 := by linarith
  have hsq : sqR ((t - (a + b) / 2) / ((b - a) / 2)) ^ 2 =
      (((t : ℂ) - ((a + b) / 2 : ℝ)) / ((b - a) / 2 : ℝ)) ^ 2 - 1 := by
    rw [sqR_sq]; push_cast; ring
  rw [arc_log_integral hr0 hsq, Uω_eq_log_add hab]
  congr 1
  have e : ((t : ℂ) - ((a + b) / 2 : ℝ)) / ((b - a) / 2 : ℝ) =
      (((t - (a + b) / 2) / ((b - a) / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e, add_assoc, posLog_sum_real, show (b - a) / 2 / 2 = (b - a) / 4 by ring]

/-- **(A.1)** in the midpoint/half-length form. -/
lemma arc_potential_real' {m r : ℝ} (hr : 0 < r) (t : ℝ) :
    ∫ θ in (0:ℝ)..2 * π, Real.log ‖(t : ℂ) - arcCurve m r θ‖ = 2 * π * Uω (m - r) (m + r) t := by
  have h := arc_potential_real (a := m - r) (b := m + r) (by linarith) t
  convert h using 2 <;> ring

/-! ### Block (D) -/

/-- The inner integral of the arcsine–arcsine block is interval integrable. -/
lemma inner_intervalIntegrable_arcs {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (j j' : Fin 16) :
    IntervalIntegrable (fun θ => ∫ φ in (0:ℝ)..2 * π,
      Real.log ‖atomγ t ε (Sum.inr j) θ - atomγ t ε (Sum.inr j') φ‖) volume 0 (2 * π) := by
  have hab : aρ (j' + 1) < bρ (j' + 1) := aρ_lt_bρ (j' + 1) (by simp only [Finset.mem_Icc]; omega)
  have hcont : Continuous fun θ : ℝ => 2 * π * Uω (aρ (j' + 1)) (bρ (j' + 1))
      (mρ (j + 1) + rρ (j + 1) * Real.cos θ) := continuous_arcUω _ _ _ _ hab
  refine (hcont.intervalIntegrable 0 (2 * π)).congr ?_
  intro θ _
  show 2 * π * Uω (aρ (j' + 1)) (bρ (j' + 1)) (mρ (j + 1) + rρ (j + 1) * Real.cos θ) =
    ∫ φ in (0:ℝ)..2 * π, Real.log ‖((mρ (j + 1) + rρ (j + 1) * Real.cos θ : ℝ) : ℂ) -
      arcCurve (mρ (j' + 1)) (rρ (j' + 1)) φ‖
  rw [arc_potential_real' (rρ_pos j')]
  have e1 : mρ (j' + 1) - rρ (j' + 1) = aρ (j' + 1) := by unfold mρ rρ; ring
  have e2 : mρ (j' + 1) + rρ (j' + 1) = bρ (j' + 1) := by unfold mρ rρ; ring
  rw [e1, e2]

/-- (D): arcsine–arcsine energy is at least `log ((bⱼ' - aⱼ')/4)`. -/
lemma block_D {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (j j' : Fin 16) :
    (2 * π) ^ 2 * Real.log ((bρ (j' + 1) - aρ (j' + 1)) / 4) ≤
      Plog t ε (Sum.inr j) (Sum.inr j') := by
  unfold Plog pairInt
  have hab : aρ (j' + 1) < bρ (j' + 1) := aρ_lt_bρ (j' + 1) (by simp only [Finset.mem_Icc]; omega)
  have key : ∀ θ : ℝ, 2 * π * Real.log ((bρ (j' + 1) - aρ (j' + 1)) / 4) ≤
      ∫ φ in (0:ℝ)..2 * π, Real.log ‖atomγ t ε (Sum.inr j) θ - atomγ t ε (Sum.inr j') φ‖ := by
    intro θ
    have h1 : (∫ φ in (0:ℝ)..2 * π,
        Real.log ‖atomγ t ε (Sum.inr j) θ - atomγ t ε (Sum.inr j') φ‖) =
        2 * π * Uω (aρ (j' + 1)) (bρ (j' + 1)) (mρ (j + 1) + rρ (j + 1) * Real.cos θ) := by
      show (∫ φ in (0:ℝ)..2 * π, Real.log ‖((mρ (j + 1) + rρ (j + 1) * Real.cos θ : ℝ) : ℂ) -
        arcCurve (mρ (j' + 1)) (rρ (j' + 1)) φ‖) = _
      rw [arc_potential_real' (rρ_pos j')]
      have e1 : mρ (j' + 1) - rρ (j' + 1) = aρ (j' + 1) := by unfold mρ rρ; ring
      have e2 : mρ (j' + 1) + rρ (j' + 1) = bρ (j' + 1) := by unfold mρ rρ; ring
      rw [e1, e2]
    rw [h1]
    exact mul_le_mul_of_nonneg_left (log_le_Uω hab _) (by positivity)
  calc (2 * π) ^ 2 * Real.log ((bρ (j' + 1) - aρ (j' + 1)) / 4)
      = ∫ θ in (0:ℝ)..2 * π, 2 * π * Real.log ((bρ (j' + 1) - aρ (j' + 1)) / 4) := by
        rw [intervalIntegral.integral_const]; simp only [sub_zero, smul_eq_mul]; ring
    _ ≤ _ := integral_mono_on (by positivity) intervalIntegrable_const
        (inner_intervalIntegrable_arcs t j j') (fun θ _ => key θ)

end Apery
end Port2

section Port3
/-!
# Block (C): the circle–arcsine energy

`Plog t ε (inl i) (inr j) ≤ (2π)² (Uω a b (tᵢ) + errj ε (tᵢ) m r)`, from the Hölder-`1/2`
estimate for the arcsine potential. Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/CircleAtoms.lean`, `Apery/ArcsineAtoms.lean`, `Apery/ArcsinePotential.lean` (the
Hölder continuity section) and `Apery/EnergyBlocks.lean` (block (C)). The inner
interval-integrability is obtained from a uniform bound on the section integrals
(measurable + bounded), instead of the product-integrability chain.
-/

open MeasureTheory Set Real intervalIntegral Filter Topology Finset

namespace Apery

/-! ### Absolute values of the circle integrals -/

lemma abs_log_eq (x : ℝ) : |Real.log x| = 2 * log⁺ x - Real.log x := by
  rw [posLog_apply]
  rcases le_total 0 (Real.log x) with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

lemma posLog_norm_sub_le (w q : ℂ) (hw : ‖w‖ ≤ 1) : log⁺ ‖w - q‖ ≤ Real.log (1 + ‖q‖) := by
  calc log⁺ ‖w - q‖ ≤ log⁺ (1 + ‖q‖) := by
        apply posLog_le_posLog (by linarith [norm_nonneg (w - q)])
        calc ‖w - q‖ ≤ ‖w‖ + ‖q‖ := norm_sub_le _ _
          _ ≤ 1 + ‖q‖ := by linarith
    _ = Real.log (1 + ‖q‖) := posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith [norm_nonneg q])

/-- Uniform bound `∫₀^{2π} |log ‖e^{iθ} - q‖| ≤ 4π log (1 + ‖q‖)`. -/
lemma abs_log_circle_integral_le (q : ℂ) :
    ∫ θ in (0:ℝ)..2 * π, |Real.log ‖circleMap 0 1 θ - q‖| ≤ 4 * π * Real.log (1 + ‖q‖) := by
  simp_rw [abs_log_eq]
  have hc : Continuous fun θ => log⁺ ‖circleMap 0 1 θ - q‖ := by
    have := continuous_circleMap 0 1
    fun_prop
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _ |>.const_mul 2)
    (circle_log_integrable 0 q 1), intervalIntegral.integral_const_mul,
    circle_log_integral_zero_one]
  have h1 : (∫ θ in (0:ℝ)..2 * π, log⁺ ‖circleMap 0 1 θ - q‖) ≤
      ∫ θ in (0:ℝ)..2 * π, Real.log (1 + ‖q‖) := by
    apply integral_mono_on (by positivity) (hc.intervalIntegrable _ _) intervalIntegrable_const
    intro θ _
    apply posLog_norm_sub_le
    simp [circleMap]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
  have h2 := posLog_nonneg (x := ‖q‖)
  nlinarith [Real.pi_pos]

/-- A uniform bound for `∫₀^{2π} |log ‖z - y(θ)‖| dθ`. -/
lemma arc_abs_log_integral_le {z : ℂ} {m r : ℝ} (hr : 0 < r) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    ∫ θ in (0:ℝ)..2 * π, |Real.log ‖z - arcCurve m r θ‖| ≤
      2 * π * |Real.log (r / 2)| + 4 * π * Real.log (1 + ‖(z - m) / r + sq‖) +
        4 * π * Real.log (1 + ‖(z - m) / r - sq‖) := by
  rw [intervalIntegral.integral_congr_ae (g := fun θ => |Real.log (r / 2) +
      Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
        Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖|) (by
      filter_upwards [arc_log_ae hr hsq] with θ hθ _
      rw [hθ])]
  have h1 := abs_log_circle_integral_le ((z - m) / r + sq)
  have h2 := abs_log_circle_integral_le ((z - m) / r - sq)
  have hi1 := (circle_log_integrable 0 ((z - m) / r + sq) 1).abs
  have hi2 := (circle_log_integrable 0 ((z - m) / r - sq) 1).abs
  have hmono : (∫ θ in (0:ℝ)..2 * π, |Real.log (r / 2) +
      Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
        Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖|) ≤
      ∫ θ in (0:ℝ)..2 * π, (|Real.log (r / 2)| +
        |Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖| +
        |Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖|) := by
    apply integral_mono_on (by positivity)
    · exact ((intervalIntegrable_const.add (circle_log_integrable 0 _ 1)).add
        (circle_log_integrable 0 _ 1)).abs
    · exact (intervalIntegrable_const.add hi1).add hi2
    intro θ _
    exact abs_add_three _ _ _
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add hi1) hi2,
    intervalIntegral.integral_add intervalIntegrable_const hi1, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hmono
  linarith

/-! ### Hölder continuity of the potential -/

lemma norm_mul_roots {ζ sq : ℂ} (hsq : sq ^ 2 = ζ ^ 2 - 1) : ‖ζ + sq‖ * ‖ζ - sq‖ = 1 := by
  rw [← norm_mul, show (ζ + sq) * (ζ - sq) = ζ ^ 2 - sq ^ 2 by ring, hsq]; simp

/-- `log⁺ ‖ζ + s‖ + log⁺ ‖ζ - s‖ = log (max ‖ζ + s‖ ‖ζ - s‖)`. -/
lemma posLog_sum_eq_log_max {ζ sq : ℂ} (hsq : sq ^ 2 = ζ ^ 2 - 1) :
    log⁺ ‖ζ + sq‖ + log⁺ ‖ζ - sq‖ = Real.log (max ‖ζ + sq‖ ‖ζ - sq‖) := by
  have h := norm_mul_roots hsq
  have h1 := norm_nonneg (ζ + sq)
  have h2 := norm_nonneg (ζ - sq)
  rcases le_total 1 ‖ζ + sq‖ with hle | hle
  · have h3 : ‖ζ - sq‖ ≤ 1 := by nlinarith
    rw [max_eq_left (h3.trans hle), posLog_eq_log (x := ‖ζ + sq‖) (by rw [abs_of_nonneg h1]; exact hle),
      (posLog_eq_zero_iff ‖ζ - sq‖).mpr (by rw [abs_of_nonneg h2]; exact h3), add_zero]
  · have h3 : 1 ≤ ‖ζ - sq‖ := by
      by_contra hc; rw [not_le] at hc; nlinarith
    rw [max_eq_right (hle.trans h3), posLog_eq_log (x := ‖ζ - sq‖) (by rw [abs_of_nonneg h2]; exact h3),
      (posLog_eq_zero_iff ‖ζ + sq‖).mpr (by rw [abs_of_nonneg h1]; exact hle), zero_add]

lemma one_le_max_roots {ζ sq : ℂ} (hsq : sq ^ 2 = ζ ^ 2 - 1) : 1 ≤ max ‖ζ + sq‖ ‖ζ - sq‖ := by
  have h := norm_mul_roots hsq
  have h1 := norm_nonneg (ζ + sq)
  have h2 := norm_nonneg (ζ - sq)
  by_contra hc
  rw [not_le, max_lt_iff] at hc
  nlinarith

lemma log_sub_log_le_of_one_le {M M' : ℝ} (hM : 1 ≤ M) (hM' : 1 ≤ M') :
    Real.log M - Real.log M' ≤ |M - M'| := by
  rcases le_total M' M with h | h
  · rw [abs_of_nonneg (by linarith), ← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < M / M' by positivity)
    have h2 : M / M' - 1 = (M - M') / M' := by field_simp
    have h3 : (M - M') / M' ≤ M - M' := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  · have := Real.log_le_log (by linarith) h
    linarith [abs_nonneg (M - M')]

lemma abs_log_max_sub_le {M M' : ℝ} (hM : 1 ≤ M) (hM' : 1 ≤ M') :
    |Real.log M - Real.log M'| ≤ |M - M'| := by
  rw [abs_le]
  constructor
  · have := log_sub_log_le_of_one_le hM' hM; rw [abs_sub_comm] at this; linarith
  · exact log_sub_log_le_of_one_le hM hM'

lemma max_roots_sub_le_aux (ζ ζ' s s' : ℂ) :
    |max ‖ζ + s‖ ‖ζ - s‖ - max ‖ζ' + s'‖ ‖ζ' - s'‖| ≤ ‖ζ - ζ'‖ + ‖s - s'‖ := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · calc |‖ζ + s‖ - ‖ζ' + s'‖| ≤ ‖(ζ + s) - (ζ' + s')‖ := abs_norm_sub_norm_le _ _
      _ = ‖(ζ - ζ') + (s - s')‖ := by ring_nf
      _ ≤ ‖ζ - ζ'‖ + ‖s - s'‖ := norm_add_le _ _
  · calc |‖ζ - s‖ - ‖ζ' - s'‖| ≤ ‖(ζ - s) - (ζ' - s')‖ := abs_norm_sub_norm_le _ _
      _ = ‖(ζ - ζ') - (s - s')‖ := by ring_nf
      _ ≤ ‖ζ - ζ'‖ + ‖s - s'‖ := norm_sub_le _ _

lemma max_roots_sub_le (ζ ζ' s s' : ℂ) :
    |max ‖ζ + s‖ ‖ζ - s‖ - max ‖ζ' + s'‖ ‖ζ' - s'‖| ≤ ‖ζ - ζ'‖ + min ‖s - s'‖ ‖s + s'‖ := by
  rcases le_total ‖s - s'‖ ‖s + s'‖ with h | h
  · rw [min_eq_left h]; exact max_roots_sub_le_aux ζ ζ' s s'
  · rw [min_eq_right h]
    have := max_roots_sub_le_aux ζ ζ' s (-s')
    rw [sub_neg_eq_add, sub_neg_eq_add, max_comm ‖ζ' + -s'‖, show ζ' + -s' = ζ' - s' by ring] at this
    exact this

lemma min_roots_le_sqrt (s s' : ℂ) : min ‖s - s'‖ ‖s + s'‖ ≤ Real.sqrt ‖s ^ 2 - s' ^ 2‖ := by
  rw [Real.le_sqrt (le_min (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)]
  have e : s ^ 2 - s' ^ 2 = (s - s') * (s + s') := by ring
  rw [e, norm_mul, sq]
  exact mul_le_mul (min_le_left _ _) (min_le_right _ _) (le_min (norm_nonneg _) (norm_nonneg _))
    (norm_nonneg _)

/-- The Hölder-`1/2` estimate for `G(ζ) = log⁺ ‖ζ + s‖ + log⁺ ‖ζ - s‖`. -/
lemma Gpot_sub_le {ζ ζ' s s' : ℂ} (hs : s ^ 2 = ζ ^ 2 - 1) (hs' : s' ^ 2 = ζ' ^ 2 - 1) :
    (log⁺ ‖ζ + s‖ + log⁺ ‖ζ - s‖) - (log⁺ ‖ζ' + s'‖ + log⁺ ‖ζ' - s'‖) ≤
      ‖ζ - ζ'‖ + Real.sqrt (‖ζ - ζ'‖ * ‖ζ + ζ'‖) := by
  rw [posLog_sum_eq_log_max hs, posLog_sum_eq_log_max hs']
  have h1 := abs_log_max_sub_le (one_le_max_roots hs) (one_le_max_roots hs')
  have h2 := max_roots_sub_le ζ ζ' s s'
  have h3 := min_roots_le_sqrt s s'
  rw [hs, hs', show ζ ^ 2 - 1 - (ζ' ^ 2 - 1) = (ζ - ζ') * (ζ + ζ') by ring, norm_mul] at h3
  linarith [le_abs_self (Real.log (max ‖ζ + s‖ ‖ζ - s‖) - Real.log (max ‖ζ' + s'‖ ‖ζ' - s'‖))]

/-! ### A uniform bound and integrability of the section integrals -/

lemma norm_root_le {ζ sq : ℂ} (hsq : sq ^ 2 = ζ ^ 2 - 1) : ‖sq‖ ≤ ‖ζ‖ + 1 := by
  have h1 : ‖sq‖ ^ 2 = ‖ζ ^ 2 - 1‖ := by rw [← norm_pow, hsq]
  have h2 : ‖ζ ^ 2 - 1‖ ≤ ‖ζ‖ ^ 2 + 1 := by
    calc ‖ζ ^ 2 - 1‖ ≤ ‖ζ ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖ζ‖ ^ 2 + 1 := by rw [norm_pow, norm_one]
  nlinarith [norm_nonneg sq, norm_nonneg ζ]

/-- A uniform bound for `∫₀^{2π} |log ‖z - y(θ)‖| dθ` over `‖z‖ ≤ R`. -/
lemma arc_point_abs_log_le' {m r : ℝ} (hr : 0 < r) {R : ℝ} (_hR : 0 ≤ R) :
    ∃ C, ∀ z : ℂ, ‖z‖ ≤ R → ∫ φ in (0:ℝ)..2 * π, |Real.log ‖z - arcCurve m r φ‖| ≤ C := by
  refine ⟨2 * π * |Real.log (r / 2)| + 4 * π * Real.log (1 + (2 * ((R + |m|) / r) + 1)) +
    4 * π * Real.log (1 + (2 * ((R + |m|) / r) + 1)), fun z hz => ?_⟩
  set sq : ℂ := (((z - m) / r) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq_def
  have hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1 := Complex.cpow_nat_inv_pow _ two_ne_zero
  have h := arc_abs_log_integral_le hr hsq
  have hζ : ‖(z - (m : ℂ)) / r‖ ≤ (R + |m|) / r := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    apply div_le_div_of_nonneg_right _ hr.le
    calc ‖z - (m : ℂ)‖ ≤ ‖z‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
      _ ≤ R + |m| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hsq_le : ‖sq‖ ≤ (R + |m|) / r + 1 := (norm_root_le hsq).trans (by linarith)
  have h1 : ‖(z - (m : ℂ)) / r + sq‖ ≤ 2 * ((R + |m|) / r) + 1 := by
    have := norm_add_le ((z - (m : ℂ)) / r) sq
    linarith
  have h2 : ‖(z - (m : ℂ)) / r - sq‖ ≤ 2 * ((R + |m|) / r) + 1 := by
    have := norm_sub_le ((z - (m : ℂ)) / r) sq
    linarith
  refine h.trans ?_
  gcongr

/-- The inner integral of the circle–arcsine block is interval integrable. -/
lemma inner_intervalIntegrable_circle_arc {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε)
    (i : Fin h) (j : Fin 16) :
    IntervalIntegrable (fun θ => ∫ φ in (0:ℝ)..2 * π,
      Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inr j) φ‖) volume 0 (2 * π) := by
  obtain ⟨C, hC⟩ := arc_point_abs_log_le' (m := mρ (j + 1)) (r := rρ (j + 1)) (rρ_pos j)
    (R := |t i| + ε) (by positivity)
  have hfun : (fun θ => ∫ φ in (0:ℝ)..2 * π,
      Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inr j) φ‖) =
      fun θ => ∫ φ, Real.log ‖circleMap (t i) ε θ - arcCurve (mρ (j + 1)) (rρ (j + 1)) φ‖
        ∂(volume.restrict (Ioc 0 (2 * π))) := by
    funext θ
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * π)]
    simp only [atomγ]
  rw [hfun]
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0:ℝ) ≤ 2 * π)).mpr ?_
  haveI : IsFiniteMeasure (volume.restrict (Ioc 0 (2 * π))) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  refine Integrable.of_bound ?_ C ?_
  · have hcont : Continuous fun p : ℝ × ℝ =>
        ‖circleMap (t i) ε p.1 - arcCurve (mρ (j + 1)) (rρ (j + 1)) p.2‖ :=
      (((continuous_circleMap (t i) ε).comp continuous_fst).sub
        ((continuous_arcCurve (mρ (j + 1)) (rρ (j + 1))).comp continuous_snd)).norm
    refine (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π)))
      (f := fun p : ℝ × ℝ =>
        Real.log ‖circleMap (t i) ε p.1 - arcCurve (mρ (j + 1)) (rρ (j + 1)) p.2‖)
      ((Real.measurable_log.comp hcont.measurable).stronglyMeasurable)).aestronglyMeasurable
  · filter_upwards with θ
    have hz : ‖circleMap (t i) ε θ‖ ≤ |t i| + ε := by
      calc ‖circleMap (t i) ε θ‖ = ‖(t i : ℂ) + (ε : ℂ) * Complex.exp (θ * Complex.I)‖ := rfl
        _ ≤ ‖(t i : ℂ)‖ + ‖(ε : ℂ) * Complex.exp (θ * Complex.I)‖ := norm_add_le _ _
        _ = |t i| + ε := by
            simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs]
            rw [abs_of_pos hε]
    calc ‖∫ φ, Real.log ‖circleMap (t i) ε θ - arcCurve (mρ (j + 1)) (rρ (j + 1)) φ‖
            ∂(volume.restrict (Ioc 0 (2 * π)))‖
        ≤ ∫ φ, ‖Real.log ‖circleMap (t i) ε θ - arcCurve (mρ (j + 1)) (rρ (j + 1)) φ‖‖
            ∂(volume.restrict (Ioc 0 (2 * π))) := norm_integral_le_integral_norm _
      _ ≤ C := by
          simp_rw [Real.norm_eq_abs]
          rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * π)]
          exact hC (circleMap (t i) ε θ) hz

/-! ### Block (C) -/

/-- (C): circle–arcsine energy. -/
lemma block_C {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin h) (j : Fin 16) :
    Plog t ε (Sum.inl i) (Sum.inr j) ≤ (2 * π) ^ 2 *
      (Uω (aρ (j + 1)) (bρ (j + 1)) (t i) + errj ε (t i) (mρ (j + 1)) (rρ (j + 1))) := by
  unfold Plog pairInt
  have hr := rρ_pos j
  have hab : aρ (j + 1) < bρ (j + 1) := aρ_lt_bρ (j + 1) (by simp only [Finset.mem_Icc]; omega)
  have hm' : mρ (j + 1) = (aρ (j + 1) + bρ (j + 1)) / 2 := rfl
  have hr' : rρ (j + 1) = (bρ (j + 1) - aρ (j + 1)) / 2 := rfl
  set sq' : ℂ := ((((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq'_def
  have hsq' : sq' ^ 2 = (((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)) ^ 2 - 1 := Complex.cpow_nat_inv_pow _ two_ne_zero
  have hU : 2 * π * (Real.log (rρ (j + 1) / 2) + log⁺ ‖((t i : ℂ) - mρ (j + 1)) / rρ (j + 1) + sq'‖ +
      log⁺ ‖((t i : ℂ) - mρ (j + 1)) / rρ (j + 1) - sq'‖) = 2 * π * Uω (aρ (j + 1)) (bρ (j + 1)) (t i) := by
    rw [← arc_log_integral hr hsq', hm', hr', arc_potential_real hab (t i)]
  have hin : ∀ θ, (∫ φ in (0:ℝ)..2 * π,
      Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inr j) φ‖) ≤
      2 * π * (Uω (aρ (j + 1)) (bρ (j + 1)) (t i) + errj ε (t i) (mρ (j + 1)) (rρ (j + 1))) := by
    intro θ
    simp only [atomγ]
    set z := circleMap (t i) ε θ with hz
    set sq : ℂ := (((z - mρ (j + 1)) / rρ (j + 1)) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq_def
    have hsq : sq ^ 2 = ((z - mρ (j + 1)) / rρ (j + 1)) ^ 2 - 1 := Complex.cpow_nat_inv_pow _ two_ne_zero
    rw [arc_log_integral hr hsq]
    have hG := Gpot_sub_le hsq hsq'
    have hzc : ‖z - (t i)‖ = ε := by
      rw [hz, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]
    have hd : ‖(z - mρ (j + 1)) / rρ (j + 1) - ((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)‖ = ε / rρ (j + 1) := by
      rw [← sub_div, show z - mρ (j + 1) - ((t i : ℂ) - mρ (j + 1)) = z - (t i) by ring, norm_div, hzc,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hs : ‖(z - mρ (j + 1)) / rρ (j + 1) + ((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)‖ ≤ (ε + 2 * |(t i) - mρ (j + 1)|) / rρ (j + 1) := by
      rw [← add_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      apply div_le_div_of_nonneg_right _ hr.le
      calc ‖z - mρ (j + 1) + ((t i : ℂ) - mρ (j + 1))‖ = ‖(z - t i) + 2 * ((t i : ℂ) - mρ (j + 1))‖ := by ring_nf
        _ ≤ ‖z - (t i)‖ + ‖(2 : ℂ) * ((t i : ℂ) - mρ (j + 1))‖ := norm_add_le _ _
        _ = ε + 2 * |(t i) - mρ (j + 1)| := by
          rw [hzc, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          simp
    have hsqrt : Real.sqrt (‖(z - mρ (j + 1)) / rρ (j + 1) - ((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)‖ * ‖(z - mρ (j + 1)) / rρ (j + 1) + ((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)‖)
        ≤ Real.sqrt (ε / rρ (j + 1) * ((ε + 2 * |(t i) - mρ (j + 1)|) / rρ (j + 1))) := by
      apply Real.sqrt_le_sqrt
      rw [hd]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    rw [hd] at hG hsqrt
    unfold errj
    nlinarith [Real.pi_pos]
  calc (∫ θ in (0:ℝ)..2 * π, ∫ φ in (0:ℝ)..2 * π,
        Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inr j) φ‖)
      ≤ ∫ θ in (0:ℝ)..2 * π, 2 * π * (Uω (aρ (j + 1)) (bρ (j + 1)) (t i) + errj ε (t i) (mρ (j + 1)) (rρ (j + 1))) :=
        integral_mono_on (by positivity) (inner_intervalIntegrable_circle_arc t hε i j)
          intervalIntegrable_const (fun θ _ => hin θ)
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [sub_zero, smul_eq_mul]; ring

end Apery
end Port3

section Port4
/-!
# Symmetry of the logarithmic pair integrals

`pairInt γ (log‖·-·‖) k l = pairInt γ (log‖·-·‖) l k` for the configuration atoms, from the
product-integrability of the logarithmic kernel on the torus. Ported from
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/EnergyAtoms.lean` (the
hypotheses of `energy_log_nonpos`), `Apery/EnergyLimit.lean` (`pairInt` as a product integral)
and `Apery/CircleAtoms.lean` (`cos_preimage_countable`).
-/

open MeasureTheory Set Real intervalIntegral Filter Topology Finset

namespace Apery

/-- The measure on `[0, 2π]`. -/
noncomputable abbrev μcirc : Measure ℝ := volume.restrict (Ioc 0 (2 * π))

variable {ι : Type*}

/-- `pairInt` as an integral over the product measure. -/
lemma pairInt_eq_prod (γ : ι → ℝ → ℂ) (f : ℂ → ℂ → ℝ) (k l : ι)
    (hf : Integrable (fun p : ℝ × ℝ => f (γ k p.1) (γ l p.2)) (μcirc.prod μcirc)) :
    pairInt γ f k l = ∫ p : ℝ × ℝ, f (γ k p.1) (γ l p.2) ∂(μcirc.prod μcirc) := by
  unfold pairInt
  rw [integral_prod _ hf, intervalIntegral.integral_of_le (by positivity)]
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * π)]

/-- Point preimages under `cos` are countable. -/
lemma cos_preimage_countable (c : ℝ) : (Real.cos ⁻¹' {c}).Countable := by
  rcases (Real.cos ⁻¹' {c}).eq_empty_or_nonempty with h | ⟨θ₀, hθ₀⟩
  · rw [h]; exact Set.countable_empty
  refine ((Set.countable_range fun k : ℤ => 2 * k * π + θ₀).union
    (Set.countable_range fun k : ℤ => 2 * k * π - θ₀)).mono ?_
  intro θ hθ
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hθ hθ₀
  obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp (hθ₀.trans hθ.symm)
  · exact Or.inl ⟨k, hk.symm⟩
  · exact Or.inr ⟨k, hk.symm⟩

-- numeric facts about Table 1

lemma rρ_le (j : Fin 16) : rρ (j + 1) ≤ 1 := by
  unfold rρ; fin_cases j <;> norm_num [aρ, bρ, table1]

lemma mρ_bounds (j : Fin 16) : 0 < mρ (j + 1) ∧ mρ (j + 1) < 2 := by
  unfold mρ; fin_cases j <;> norm_num [aρ, bρ, table1]

lemma continuous_atomγ {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) (k : Idx h) : Continuous (atomγ t ε k) := by
  cases k with
  | inl i => exact continuous_circleMap _ _
  | inr j => exact continuous_arcCurve _ _

lemma norm_atomγ_le {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) (k : Idx h) (θ : ℝ) :
    ‖atomγ t ε k θ‖ ≤ (∑ i, |t i|) + |ε| + 3 := by
  cases k with
  | inl i =>
    simp only [atomγ, circleMap]
    calc ‖(t i : ℂ) + ε * Complex.exp (θ * Complex.I)‖
        ≤ ‖(t i : ℂ)‖ + ‖(ε : ℂ) * Complex.exp (θ * Complex.I)‖ := norm_add_le _ _
      _ = |t i| + |ε| := by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (∑ i, |t i|) + |ε| + 3 := by
          have : |t i| ≤ ∑ i, |t i| := Finset.single_le_sum (fun i _ => abs_nonneg (t i))
            (Finset.mem_univ i)
          linarith
  | inr j =>
    simp only [atomγ]
    refine (norm_arcCurve_le _ _ _).trans ?_
    have h1 := mρ_bounds j
    have h2 := rρ_pos j
    have h3 := rρ_le j
    rw [abs_of_pos h1.1, abs_of_pos h2]
    have : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith [abs_nonneg ε]

/-- `∫₀^{2π} |log ‖z - circleMap c ε φ‖| ≤ 2π |log ε| + 4π log (1 + ‖(z - c)/ε‖)`. -/
lemma circle_point_abs_log_le (z c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ φ in (0:ℝ)..2 * π, |Real.log ‖z - circleMap c ε φ‖| ≤
      2 * π * |Real.log ε| + 4 * π * Real.log (1 + ‖(z - c) / ε‖) := by
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hfac : ∀ φ, ‖z - circleMap c ε φ‖ = ε * ‖circleMap 0 1 φ - (z - c) / ε‖ := by
    intro φ
    have e : z - circleMap c ε φ = -((ε : ℂ) * (circleMap 0 1 φ - (z - c) / ε)) := by
      simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]; field_simp; ring
    rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have hpt : ∀ φ, |Real.log ‖z - circleMap c ε φ‖| ≤
      |Real.log ε| + |Real.log ‖circleMap 0 1 φ - (z - c) / ε‖| := by
    intro φ
    rw [hfac]
    by_cases h0 : ‖circleMap 0 1 φ - (z - c) / ε‖ = 0
    · rw [h0, mul_zero, Real.log_zero, abs_zero]; positivity
    · rw [Real.log_mul hε.ne' h0]; exact abs_add_le _ _
  have hi : IntervalIntegrable (fun φ => |Real.log ‖z - circleMap c ε φ‖|) volume 0 (2 * π) := by
    have := (circle_log_integrable c z ε).abs
    refine this.congr ?_
    intro φ _; simp only [norm_sub_rev]
  calc ∫ φ in (0:ℝ)..2 * π, |Real.log ‖z - circleMap c ε φ‖|
      ≤ ∫ φ in (0:ℝ)..2 * π, (|Real.log ε| + |Real.log ‖circleMap 0 1 φ - (z - c) / ε‖|) :=
        integral_mono_on (by positivity) hi
          (intervalIntegrable_const.add (circle_log_integrable 0 _ 1).abs) (fun φ _ => hpt φ)
    _ = 2 * π * |Real.log ε| + ∫ φ in (0:ℝ)..2 * π, |Real.log ‖circleMap 0 1 φ - (z - c) / ε‖| := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (circle_log_integrable 0 _ 1).abs,
          intervalIntegral.integral_const]
        simp
    _ ≤ _ := by linarith [abs_log_circle_integral_le ((z - c) / ε)]

/-- Integrability of `φ ↦ log ‖z - atomγ k φ‖`. -/
lemma atom_point_integrable {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k : Idx h) (z : ℂ) :
    IntervalIntegrable (fun φ => Real.log ‖z - atomγ t ε k φ‖) volume 0 (2 * π) := by
  cases k with
  | inl i =>
    have := circle_log_integrable (t i) z ε
    refine this.congr ?_
    intro φ _; simp only [atomγ, norm_sub_rev]
  | inr j => exact arc_log_integrable (rρ_pos j)

/-- A uniform bound for `∫₀^{2π} |log ‖z - atomγ k φ‖| dφ` over `‖z‖ ≤ R`. -/
lemma atom_point_abs_log_le {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k : Idx h) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ C, ∀ z : ℂ, ‖z‖ ≤ R → ∫ φ in (0:ℝ)..2 * π, |Real.log ‖z - atomγ t ε k φ‖| ≤ C := by
  cases k with
  | inl i =>
    refine ⟨2 * π * |Real.log ε| + 4 * π * ((R + |t i|) / ε), fun z hz => ?_⟩
    refine (circle_point_abs_log_le z (t i) hε).trans ?_
    have h1 : Real.log (1 + ‖(z - t i) / ε‖) ≤ ‖(z - t i) / ε‖ := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖(z - t i) / ε‖ by positivity)
      linarith
    have h2 : ‖(z - t i) / ε‖ ≤ (R + |t i|) / ε := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      apply div_le_div_of_nonneg_right _ hε.le
      calc ‖z - t i‖ ≤ ‖z‖ + ‖(t i : ℂ)‖ := norm_sub_le _ _
        _ ≤ R + |t i| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    nlinarith [Real.pi_pos]
  | inr j =>
    set m := mρ (j + 1)
    set r := rρ (j + 1)
    have hr := rρ_pos j
    refine ⟨2 * π * |Real.log (r / 2)| + 8 * π * (2 * ((R + |m|) / r) + 1), fun z hz => ?_⟩
    set sq : ℂ := (((z - m) / r) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq_def
    have hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1 := Complex.cpow_nat_inv_pow _ two_ne_zero
    refine (arc_abs_log_integral_le hr hsq).trans ?_
    have hζ : ‖(z - m) / r‖ ≤ (R + |m|) / r := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      apply div_le_div_of_nonneg_right _ hr.le
      calc ‖z - m‖ ≤ ‖z‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
        _ ≤ R + |m| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have hs := norm_root_le hsq
    have hq1 : Real.log (1 + ‖(z - m) / r + sq‖) ≤ 2 * ((R + |m|) / r) + 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖(z - m) / r + sq‖ by positivity)
      have := norm_add_le ((z - m) / r) sq
      linarith
    have hq2 : Real.log (1 + ‖(z - m) / r - sq‖) ≤ 2 * ((R + |m|) / r) + 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖(z - m) / r - sq‖ by positivity)
      have := norm_sub_le ((z - m) / r) sq
      linarith
    nlinarith [Real.pi_pos]

lemma measurable_atom_kernel {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) (k l : Idx h) :
    Measurable fun p : ℝ × ℝ => Real.log ‖atomγ t ε k p.1 - atomγ t ε l p.2‖ := by
  apply Real.measurable_log.comp
  exact (continuous_norm.comp (((continuous_atomγ t ε k).comp continuous_fst).sub
    ((continuous_atomγ t ε l).comp continuous_snd))).measurable

/-- Torus integrability of the logarithmic kernel for each pair of atoms. -/
lemma atom_pair_integrable {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Idx h) :
    Integrable (fun p : ℝ × ℝ => Real.log ‖atomγ t ε k p.1 - atomγ t ε l p.2‖)
      (μcirc.prod μcirc) := by
  have hR0 : 0 ≤ (∑ i, |t i|) + |ε| + 3 := by
    have : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith [abs_nonneg ε]
  obtain ⟨C, hC⟩ := atom_point_abs_log_le t hε l hR0
  have hmeas := (measurable_atom_kernel t ε k l).aestronglyMeasurable (μ := μcirc.prod μcirc)
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with θ
    have := atom_point_integrable t hε l (atomγ t ε k θ)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp this
  · refine Integrable.mono' (integrable_const C) hmeas.norm.integral_prod_right' ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have := hC (atomγ t ε k θ) (norm_atomγ_le t ε k θ)
    rw [intervalIntegral.integral_of_le (by positivity)] at this
    simpa [Real.norm_eq_abs] using this

/-- Point preimages under the atoms are countable. -/
lemma atom_preimage_countable {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (l : Idx h) (c : ℂ) :
    {φ : ℝ | c = atomγ t ε l φ}.Countable := by
  cases l with
  | inl i =>
    refine (circleMap_preimage_countable (t i) hε.ne' c).mono ?_
    intro φ hφ
    simp only [Set.mem_ofPred_eq, atomγ] at hφ
    simp [hφ]
  | inr j =>
    refine (cos_preimage_countable ((c.re - mρ (j + 1)) / rρ (j + 1))).mono ?_
    intro φ hφ
    simp only [Set.mem_ofPred_eq, atomγ, arcCurve] at hφ
    have hr := rρ_pos j
    have : c.re = mρ (j + 1) + rρ (j + 1) * Real.cos φ := by
      rw [hφ, Complex.ofReal_re]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [this]; field_simp; ring

/-- Almost every pair of parameters gives distinct points. -/
lemma atom_pair_ae_ne {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Idx h) :
    ∀ᵐ p ∂(μcirc.prod μcirc), atomγ t ε k p.1 ≠ atomγ t ε l p.2 := by
  rw [ae_iff]
  simp only [not_not]
  have hS : MeasurableSet {p : ℝ × ℝ | atomγ t ε k p.1 = atomγ t ε l p.2} :=
    (isClosed_eq ((continuous_atomγ t ε k).comp continuous_fst)
      ((continuous_atomγ t ε l).comp continuous_snd)).measurableSet
  rw [Measure.prod_apply hS]
  have : ∀ θ, μcirc (Prod.mk θ ⁻¹' {p : ℝ × ℝ | atomγ t ε k p.1 = atomγ t ε l p.2}) = 0 := by
    intro θ
    have hc := (atom_preimage_countable t hε l (atomγ t ε k θ)).measure_zero (volume : Measure ℝ)
    refine le_antisymm ?_ bot_le
    calc μcirc (Prod.mk θ ⁻¹' {p : ℝ × ℝ | atomγ t ε k p.1 = atomγ t ε l p.2})
        ≤ volume (Prod.mk θ ⁻¹' {p : ℝ × ℝ | atomγ t ε k p.1 = atomγ t ε l p.2}) :=
          (Measure.le_iff'.mp Measure.restrict_le_self) _
      _ = volume {φ : ℝ | atomγ t ε k θ = atomγ t ε l φ} := rfl
      _ = 0 := hc
  simp only [this, lintegral_zero]

/-- Symmetry of the pair integrals of the logarithmic kernel. -/
lemma pairInt_log_symm {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Idx h) :
    pairInt (atomγ t ε) (fun z w => Real.log ‖z - w‖) k l =
      pairInt (atomγ t ε) (fun z w => Real.log ‖z - w‖) l k := by
  rw [pairInt_eq_prod _ _ _ _ (atom_pair_integrable t hε k l),
    pairInt_eq_prod _ _ _ _ (atom_pair_integrable t hε l k), ← integral_prod_swap]
  simp only [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]

end Apery
end Port4


open MeasureTheory Real Finset in
/-- The platform target `Apery.pairInt_log_symm`, restated at top level as `solution`. -/
theorem solution {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Apery.Idx h) :
    Apery.pairInt (Apery.atomγ t ε) (fun z w => Real.log ‖z - w‖) k l =
      Apery.pairInt (Apery.atomγ t ε) (fun z w => Real.log ‖z - w‖) l k :=
  Apery.pairInt_log_symm t hε k l

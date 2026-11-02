-- Prove2me | solution 1 for AffineStorage.Ruin.remark_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:24:42.229859+00:00
-- url     : https://prove2.me/submissions/61ae7be4-d949-4a28-976c-f52c635f0d9b

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology
open AffineStorage.Ruin

lemma affRuin3_d_integrable (P : Params) (hS : P.Standing) :
    IntegrableOn P.d (Set.Ioi 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := hS
  by_contra h
  rw [integral_undef h] at h1
  norm_num at h1

lemma affRuin3_lst_integrable (P : Params) (hS : P.Standing) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (fun y => Real.exp (-(s * y)) * P.d y) (Set.Ioi 0) := by
  have hdi := affRuin3_d_integrable P hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hdm, hd0, -, -⟩ := hS
  refine Integrable.mono' hdi
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable.mul
      hdm).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy' : (0 : ℝ) < y := hy
  have he : Real.exp (-(s * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hd0 y))]
  exact mul_le_of_le_one_left (hd0 y) he

lemma affRuin3_yexp (m y : ℝ) (hm : 0 < m) (hy : 0 ≤ y) : y * Real.exp (-(m * y)) ≤ 1 / m := by
  have h1 := Real.add_one_le_exp (m * y)
  have hpos := Real.exp_pos (m * y)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hpos hm]
  nlinarith

/-- `0 ≤ e^{-ay}(1 - e^{-ky})/k ≤ min(1/k, y e^{-ay})`. -/
lemma affRuin3_q_aux (a k y : ℝ) (ha : 0 ≤ a) (hk : 0 < k) (hy : 0 ≤ y) :
    0 ≤ Real.exp (-(a * y)) * (1 - Real.exp (-(k * y))) / k ∧
    Real.exp (-(a * y)) * (1 - Real.exp (-(k * y))) / k ≤ 1 / k ∧
    Real.exp (-(a * y)) * (1 - Real.exp (-(k * y))) / k ≤ y * Real.exp (-(a * y)) := by
  have e1 : Real.exp (-(k * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e2 := Real.add_one_le_exp (-(k * y))
  have ea := Real.exp_pos (-(a * y))
  have ek := Real.exp_pos (-(k * y))
  refine ⟨div_nonneg (mul_nonneg ea.le (by linarith)) hk.le, ?_, ?_⟩
  · rw [div_le_div_iff_of_pos_right hk]
    have : Real.exp (-(a * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith
  · rw [div_le_iff₀ hk]
    nlinarith

/-- The difference quotient kernel `q(y) = (e^{-βy} - e^{-sy})/(s - β)` is in `[0, 1/ϑ + 1/β]`
when `β ≥ 0`, `s ≥ ϑ > 0`, `s ≠ β`. -/
lemma affRuin3_q_bound (β s ϑ y : ℝ) (hβ : 0 ≤ β) (hϑ : 0 < ϑ) (hs : ϑ ≤ s) (hne : s ≠ β)
    (hy : 0 ≤ y) :
    0 ≤ (Real.exp (-(β * y)) - Real.exp (-(s * y))) / (s - β) ∧
    (Real.exp (-(β * y)) - Real.exp (-(s * y))) / (s - β) ≤ 1 / ϑ + 1 / β := by
  have hβi : 0 ≤ 1 / β := by positivity
  have hϑi : 0 < 1 / ϑ := by positivity
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- s < β
    have hk : 0 < β - s := by linarith
    have heq : (Real.exp (-(β * y)) - Real.exp (-(s * y))) / (s - β)
        = Real.exp (-(s * y)) * (1 - Real.exp (-((β - s) * y))) / (β - s) := by
      have : Real.exp (-(s * y)) * Real.exp (-((β - s) * y)) = Real.exp (-(β * y)) := by
        rw [← Real.exp_add]; ring_nf
      rw [show s - β = -(β - s) by ring, div_neg, ← neg_div]
      congr 1
      rw [mul_sub, mul_one, this]; ring
    obtain ⟨h0, h1, h2⟩ := affRuin3_q_aux s (β - s) y (by linarith) hk hy
    rw [heq]
    refine ⟨h0, ?_⟩
    by_cases hc : ϑ ≤ β - s
    · have : 1 / (β - s) ≤ 1 / ϑ := one_div_le_one_div_of_le hϑ hc
      linarith
    · have hs0 : 0 < s := by linarith
      have := affRuin3_yexp s y hs0 hy
      have : 1 / s ≤ 1 / ϑ := one_div_le_one_div_of_le hϑ hs
      linarith
  · -- β < s
    have hk : 0 < s - β := by linarith
    have heq : (Real.exp (-(β * y)) - Real.exp (-(s * y))) / (s - β)
        = Real.exp (-(β * y)) * (1 - Real.exp (-((s - β) * y))) / (s - β) := by
      have : Real.exp (-(β * y)) * Real.exp (-((s - β) * y)) = Real.exp (-(s * y)) := by
        rw [← Real.exp_add]; ring_nf
      rw [mul_sub, mul_one, this]
    obtain ⟨h0, h1, h2⟩ := affRuin3_q_aux β (s - β) y hβ hk hy
    rw [heq]
    refine ⟨h0, ?_⟩
    by_cases hc : ϑ ≤ s - β
    · have : 1 / (s - β) ≤ 1 / ϑ := one_div_le_one_div_of_le hϑ hc
      linarith
    · have hβ0 : 0 < β := by linarith
      have := affRuin3_yexp β y hβ0 hy
      linarith

lemma affRuin3_G3_bound (P : Params) (hS : P.Standing) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    |G3 P ϑ| ≤ P.lamMinus / P.r * (1 / ϑ + 1 / P.β) := by
  have hdi := affRuin3_d_integrable P hS
  obtain ⟨-, hr, -, hlm, -, -, -, hβ, hγ, hdm, hd0, -, h1⟩ := id hS
  have hlr : 0 < P.lamMinus / P.r := div_pos hlm hr
  have hB : 0 ≤ 1 / ϑ + 1 / P.β := by positivity
  have hgi : IntegrableOn (fun y => (1 / ϑ + 1 / P.β) * P.d y) (Set.Ioi 0) := hdi.const_mul _
  have hgint : ∫ y in Set.Ioi 0, (1 / ϑ + 1 / P.β) * P.d y = 1 / ϑ + 1 / P.β := by
    rw [integral_const_mul, h1, mul_one]
  unfold G3
  split_ifs with hc
  · -- removable point: `β = ϑ + γ > 0`
    have hβ0 : 0 < P.β := by linarith
    rw [abs_mul, abs_of_pos hlr]
    refine mul_le_mul_of_nonneg_left ?_ hlr.le
    rw [← Real.norm_eq_abs, ← hgint]
    refine norm_integral_le_of_norm_le hgi
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_))
    have hy' : (0:ℝ) < y := hy
    have := affRuin3_yexp P.β y hβ0 hy'.le
    have hnn : 0 ≤ y * Real.exp (-(P.β * y)) := mul_nonneg hy'.le (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (hd0 y))]
    have : y * Real.exp (-(P.β * y)) ≤ 1 / ϑ + 1 / P.β := by
      have : (0:ℝ) ≤ 1 / ϑ := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right this (hd0 y)
  · have hne : ϑ + P.γ ≠ P.β := hc
    have i1 := affRuin3_lst_integrable P hS P.β hβ
    have i2 := affRuin3_lst_integrable P hS (ϑ + P.γ) (by linarith)
    have heq : (P.lst P.β - P.lst (ϑ + P.γ)) / (ϑ + P.γ - P.β) = ∫ y in Set.Ioi 0,
        (Real.exp (-(P.β * y)) - Real.exp (-((ϑ + P.γ) * y))) / (ϑ + P.γ - P.β) * P.d y := by
      unfold Params.lst
      rw [← integral_sub i1 i2, ← integral_div]
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      ring
    rw [heq, abs_mul, abs_of_pos hlr]
    refine mul_le_mul_of_nonneg_left ?_ hlr.le
    rw [← Real.norm_eq_abs, ← hgint]
    refine norm_integral_le_of_norm_le hgi
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_))
    have hy' : (0:ℝ) < y := hy
    obtain ⟨q0, q1⟩ := affRuin3_q_bound P.β (ϑ + P.γ) ϑ y hβ hϑ (by linarith) hne hy'.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg q0 (hd0 y))]
    exact mul_le_mul_of_nonneg_right q1 (hd0 y)

lemma affRuin3_lst_measurable (P : Params) (hS : P.Standing) : Measurable P.lst := by
  have hdm : Measurable P.d := hS.2.2.2.2.2.2.2.2.2.1
  have : StronglyMeasurable (fun s => ∫ y, Real.exp (-(s * y)) * P.d y
      ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
    refine StronglyMeasurable.integral_prod_right (f := fun s y => Real.exp (-(s * y)) * P.d y) ?_
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2))).measurable.mul
      (hdm.comp measurable_snd)).stronglyMeasurable
  exact this.measurable

lemma affRuin3_G3_measurable (P : Params) (hS : P.Standing) : Measurable (G3 P) := by
  have hl := affRuin3_lst_measurable P hS
  unfold G3
  refine Measurable.ite (measurableSet_eq_fun (measurable_id.add_const _) measurable_const)
    measurable_const ?_
  exact measurable_const.mul ((measurable_const.sub (hl.comp (measurable_id.add_const _))).div
    ((measurable_id.add_const _).sub_const _))
lemma affRuinF_monoOn_Ioo {a b : ℝ} {h h' : ℝ → ℝ}
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (h' x) x) (hnn : ∀ x ∈ Set.Ioo a b, 0 ≤ h' x) :
    MonotoneOn h (Set.Ioo a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo a b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (by rw [interior_Ioo]; intro x hx; exact (hd x hx).hasDerivWithinAt)
    (by rw [interior_Ioo]; exact hnn)

lemma affRuinF_monoOn_Ioi {a : ℝ} {h h' : ℝ → ℝ}
    (hd : ∀ x ∈ Set.Ioi a, HasDerivAt h (h' x) x) (hnn : ∀ x ∈ Set.Ioi a, 0 ≤ h' x) :
    MonotoneOn h (Set.Ioi a) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi a)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (by rw [interior_Ioi]; intro x hx; exact (hd x hx).hasDerivWithinAt)
    (by rw [interior_Ioi]; exact hnn)

lemma affRuinF_d_integrable (P : Params) (hS : P.Standing) :
    IntegrableOn P.d (Set.Ioi 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := hS
  by_contra h
  rw [integral_undef h] at h1
  norm_num at h1

lemma affRuinF_lst_bounds (P : Params) (hS : P.Standing) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ P.lst s ∧ P.lst s ≤ 1 := by
  have hdi := affRuinF_d_integrable P hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hdm, hd0, -, h1⟩ := hS
  have hint : IntegrableOn (fun y => Real.exp (-(s * y)) * P.d y) (Set.Ioi 0) := by
    refine Integrable.mono' hdi
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable.mul
        hdm).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    have hy' : (0 : ℝ) < y := hy
    have he : Real.exp (-(s * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hd0 y))]
    nlinarith [hd0 y, Real.exp_pos (-(s * y))]
  constructor
  · unfold Params.lst
    exact setIntegral_nonneg measurableSet_Ioi fun y _ => mul_nonneg (Real.exp_pos _).le (hd0 y)
  · unfold Params.lst
    rw [← h1]
    refine setIntegral_mono_on hint hdi measurableSet_Ioi fun y hy => ?_
    have hy' : (0 : ℝ) < y := hy
    have he : Real.exp (-(s * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith [hd0 y, Real.exp_pos (-(s * y))]


lemma affRuin3_Fs_quant (P : Params) (hS : P.Standing) (Fs : ℝ → ℝ)
    (hF : IsPrimitiveF P Fs) :
    (∃ c, ∀ ϑ ∈ Set.Ioc 0 (P.μ / 4), c - (P.α + P.ν) / P.r * Real.log ϑ ≤ Fs ϑ) ∧
    (∃ c, ∀ ϑ ∈ Set.Ico (3 * P.μ / 4) P.μ, c - P.lamPlus / P.r * Real.log (P.μ - ϑ) ≤ Fs ϑ) ∧
    (∃ c, ∀ ϑ ∈ Set.Ioc P.μ (3 * P.μ / 2), c - P.lamPlus / P.r * Real.log (ϑ - P.μ) ≤ Fs ϑ) ∧
    (∃ x1 c, 3 * P.μ / 2 < x1 ∧ P.μ + 1 ≤ x1 ∧ 1 ≤ x1 ∧
      ∀ ϑ, x1 ≤ ϑ → c + P.p / P.r / 2 * ϑ ≤ Fs ϑ) := by
  obtain ⟨hp, hr, hlp, hlm, hμ, hν, hα, -⟩ := id hS
  set A := (P.α + P.ν) / P.r with hA_def
  set B := P.lamPlus / P.r with hB_def
  set L := P.lamMinus / P.r with hL_def
  have hA : 0 < A := div_pos (by linarith) hr
  have hB : 0 < B := div_pos hlp hr
  have hL : 0 < L := div_pos hlm hr
  have hpr : 0 < P.p / P.r := div_pos hp hr
  have key : ∀ ϑ, F P ϑ = P.p / P.r - L * ((1 - P.lst ϑ) / ϑ) + B * (1 / (P.μ - ϑ))
      - A * (1 / ϑ) := by
    intro ϑ; simp only [F, Fbar, hA_def, hB_def, hL_def]; ring
  have hq : ∀ ϑ, 0 < ϑ → 0 ≤ (1 - P.lst ϑ) / ϑ ∧ (1 - P.lst ϑ) / ϑ ≤ 1 / ϑ := by
    intro ϑ hϑ
    obtain ⟨h0, h1⟩ := affRuinF_lst_bounds P hS ϑ hϑ.le
    exact ⟨div_nonneg (by linarith) hϑ.le, div_le_div_of_nonneg_right (by linarith) hϑ.le⟩
  have hFd : ∀ η, 0 < η → η ≠ P.μ → HasDerivAt Fs (F P η) η := hF
  have h1 : Tendsto (F P) atTop (𝓝 (P.p / P.r)) := by
    have hinv : Tendsto (fun ϑ : ℝ => 1 / ϑ) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_inv_atTop_zero
    have hqt : Tendsto (fun ϑ => (1 - P.lst ϑ) / ϑ) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with ϑ hϑ using (hq ϑ hϑ).1
      · filter_upwards [eventually_gt_atTop 0] with ϑ hϑ using (hq ϑ hϑ).2
    have hm : Tendsto (fun ϑ : ℝ => 1 / (P.μ - ϑ)) atTop (𝓝 0) := by
      have : Tendsto (fun ϑ : ℝ => P.μ - ϑ) atTop atBot :=
        tendsto_atBot_add_const_left _ _ tendsto_neg_atTop_atBot
      simp only [one_div]; exact tendsto_inv_atBot_zero.comp this
    have := ((tendsto_const_nhds (x := P.p / P.r)).sub (hqt.const_mul L)).add
      (hm.const_mul B) |>.sub (hinv.const_mul A)
    simp only [mul_zero, sub_zero, add_zero] at this
    exact this.congr fun ϑ => (key ϑ).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · set C := P.p / P.r + B * (2 / P.μ)
    have hC : 0 ≤ C := by positivity
    have hmono : MonotoneOn (fun ϑ => -Fs ϑ + C * ϑ - A * Real.log ϑ) (Set.Ioo 0 (P.μ / 2)) := by
      refine affRuinF_monoOn_Ioo (h' := fun ϑ => -F P ϑ + C - A * (1 / ϑ)) ?_ ?_
      · intro x hx
        have hx0 : 0 < x := hx.1
        have := ((hFd x hx0 (by linarith [hx.2])).neg.add
          ((hasDerivAt_id' x).const_mul C)).sub ((Real.hasDerivAt_log hx0.ne').const_mul A)
        exact this.congr_deriv (by ring)
      · intro x hx
        have hx0 : 0 < x := hx.1
        have hx2 : x < P.μ / 2 := hx.2
        have h2 : 1 / (P.μ - x) ≤ 2 / P.μ := by
          rw [div_le_div_iff₀ (by linarith) hμ]; linarith
        have := (hq x hx0).1
        have hk := key x
        nlinarith [mul_nonneg hL.le this, mul_le_mul_of_nonneg_left h2 hB.le]
    set x0 := P.μ / 4
    have hx0 : x0 ∈ Set.Ioo 0 (P.μ / 2) := ⟨by positivity, by simp only [x0]; linarith⟩
    refine ⟨-(-Fs x0 + C * x0 - A * Real.log x0), fun ϑ hϑ => ?_⟩
    have hm := hmono ⟨hϑ.1, lt_of_le_of_lt hϑ.2 hx0.2⟩ hx0 hϑ.2
    simp only at hm
    nlinarith [hϑ.1]
  · set C' := L * (2 / P.μ) + A * (2 / P.μ)
    have hC' : 0 ≤ C' := by positivity
    have hmono : MonotoneOn (fun ϑ => Fs ϑ + C' * ϑ + B * Real.log (P.μ - ϑ))
        (Set.Ioo (P.μ / 2) P.μ) := by
      refine affRuinF_monoOn_Ioo (h' := fun ϑ => F P ϑ + C' + B * (-1 / (P.μ - ϑ))) ?_ ?_
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hne : P.μ - x ≠ 0 := by linarith [hx.2]
        have := ((hFd x hx0 (by linarith [hx.2])).add
          ((hasDerivAt_id' x).const_mul C')).add
          ((((hasDerivAt_id' x).const_sub P.μ).log hne).const_mul B)
        exact this.congr_deriv (by ring)
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hx1 : P.μ / 2 < x := hx.1
        have h2 : 1 / x ≤ 2 / P.μ := by
          rw [div_le_div_iff₀ hx0 hμ]; linarith
        have := (hq x hx0).2
        have hk := key x
        rw [neg_div]
        nlinarith [mul_le_mul_of_nonneg_left (this.trans h2) hL.le,
          mul_le_mul_of_nonneg_left h2 hA.le]
    set x0 := 3 * P.μ / 4
    have hx0 : x0 ∈ Set.Ioo (P.μ / 2) P.μ := ⟨by simp only [x0]; linarith,
      by simp only [x0]; linarith⟩
    refine ⟨(Fs x0 + C' * x0 + B * Real.log (P.μ - x0)) - C' * P.μ, fun ϑ hϑ => ?_⟩
    have hm := hmono hx0 ⟨lt_of_lt_of_le hx0.1 hϑ.1, hϑ.2⟩ hϑ.1
    simp only at hm
    nlinarith [hϑ.2]
  · set C := P.p / P.r
    have hmono : MonotoneOn (fun ϑ => -Fs ϑ + C * ϑ - B * Real.log (ϑ - P.μ))
        (Set.Ioo P.μ (2 * P.μ)) := by
      refine affRuinF_monoOn_Ioo (h' := fun ϑ => -F P ϑ + C - B * (1 / (ϑ - P.μ))) ?_ ?_
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hne : x - P.μ ≠ 0 := by linarith [hx.1]
        have := ((hFd x hx0 (by linarith [hx.1])).neg.add
          ((hasDerivAt_id' x).const_mul C)).sub
          ((((hasDerivAt_id' x).sub_const P.μ).log hne).const_mul B)
        exact this.congr_deriv (by ring)
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hx1 : P.μ < x := hx.1
        have h2 : 1 / (P.μ - x) = -(1 / (x - P.μ)) := by
          rw [← neg_sub, div_neg]
        have := (hq x hx0).1
        have hk := key x
        have h3 : 0 ≤ 1 / x := by positivity
        rw [h2] at hk
        nlinarith [mul_nonneg hL.le this, mul_nonneg hA.le h3]
    set x0 := 3 * P.μ / 2
    have hx0 : x0 ∈ Set.Ioo P.μ (2 * P.μ) := ⟨by simp only [x0]; linarith,
      by simp only [x0]; linarith⟩
    refine ⟨-(-Fs x0 + C * x0 - B * Real.log (x0 - P.μ)), fun ϑ hϑ => ?_⟩
    have hm := hmono ⟨hϑ.1, lt_of_le_of_lt hϑ.2 hx0.2⟩ hx0 hϑ.2
    simp only at hm
    nlinarith [hϑ.1, hpr]
  · have hev : ∀ᶠ ϑ in atTop, P.p / P.r / 2 < F P ϑ :=
      h1.eventually (lt_mem_nhds (by linarith))
    obtain ⟨c, hc⟩ := eventually_atTop.mp hev
    set c' := max c (2 * P.μ + 1)
    have hc'μ : 2 * P.μ + 1 ≤ c' := le_max_right _ _
    have hmono : MonotoneOn (fun ϑ => Fs ϑ - P.p / P.r / 2 * ϑ) (Set.Ioi c') := by
      refine affRuinF_monoOn_Ioi (h' := fun ϑ => F P ϑ - P.p / P.r / 2) ?_ ?_
      · intro x hx
        have hx' : c' < x := hx
        have := hFd x (by linarith) (by linarith)
        exact (this.sub ((hasDerivAt_id' x).const_mul (P.p / P.r / 2))).congr_deriv (by ring)
      · intro x hx
        have hx' : c' < x := hx
        have := hc x (le_trans (le_max_left _ _) hx'.le)
        linarith
    set x0 := c' + 1
    have hx0 : x0 ∈ Set.Ioi c' := by simp [x0]
    refine ⟨x0, Fs x0 - P.p / P.r / 2 * x0, by simp only [x0]; linarith,
      by simp only [x0]; linarith, by simp only [x0]; linarith, fun ϑ hϑ => ?_⟩
    have := hmono hx0 (show ϑ ∈ Set.Ioi c' from lt_of_lt_of_le hx0 hϑ) hϑ
    simp only at this; linarith

lemma affRuin3_piece {f g : ℝ → ℝ} {S U : Set ℝ} (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hf : ContinuousOn f U) (hg : IntegrableOn g S) (hb : ∀ x ∈ S, |f x| ≤ g x) :
    IntegrableOn f S := by
  refine Integrable.mono' hg ((hf.mono hSU).aestronglyMeasurable hS) ?_
  exact (ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall fun x hx => by
    rw [Real.norm_eq_abs]; exact hb x hx)

lemma affRuin3_exp_le (F c A t : ℝ) (ht : 0 < t) (h : c - A * Real.log t ≤ F) :
    Real.exp (-F) ≤ Real.exp (-c) * t ^ A := by
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

lemma affRuin3_rpow_int (a s : ℝ) (ha : 0 ≤ a) (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s) (Set.Ioc 0 a) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp (intervalIntegral.intervalIntegrable_rpow' hs)

/-- The key integrability: `(1 + 1/ϑ + 1/|μ-ϑ|) e^{-F⋆(ϑ)}` is integrable on `(0, ∞)`. -/
lemma affRuin3_HE (P : Params) (hS : P.Standing) (Fs : ℝ → ℝ) (hF : IsPrimitiveF P Fs) :
    IntegrableOn (fun ϑ => (1 + 1 / ϑ + 1 / |P.μ - ϑ|) * Real.exp (-(Fs ϑ))) (Set.Ioi 0) := by
  obtain ⟨hp, hr, hlp, hlm, hμ, hν, hα, -⟩ := id hS
  have hA : 0 < (P.α + P.ν) / P.r := div_pos (by linarith) hr
  have hB : 0 < P.lamPlus / P.r := div_pos hlp hr
  have hpr : 0 < P.p / P.r / 2 := by positivity
  obtain ⟨⟨c0, h0⟩, ⟨c1, h1⟩, ⟨c2, h2⟩, ⟨x1, c3, hx1a, hx1b, hx1c, h3⟩⟩ :=
    affRuin3_Fs_quant P hS Fs hF
  set A := (P.α + P.ν) / P.r
  set B := P.lamPlus / P.r
  set f := fun ϑ => (1 + 1 / ϑ + 1 / |P.μ - ϑ|) * Real.exp (-(Fs ϑ)) with hf_def
  set U := Set.Ioi (0:ℝ) \ {P.μ} with hU
  have hmemU : ∀ x, 0 < x → x ≠ P.μ → x ∈ U := fun x h0 h1 => ⟨h0, h1⟩
  have hfc : ContinuousOn f U := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxμ : x ≠ P.μ := hx.2
    have hFc : ContinuousAt Fs x := (hF x hx0 hxμ).continuousAt
    have : ContinuousAt f x := by
      have hμx : |P.μ - x| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hxμ))
      refine ContinuousAt.mul ?_ (Real.continuous_exp.continuousAt.comp hFc.neg)
      refine (continuousAt_const.add (continuousAt_const.div continuousAt_id hx0.ne')).add
        (continuousAt_const.div (continuous_abs.continuousAt.comp
          (continuousAt_const.sub continuousAt_id)) hμx)
    exact this.continuousWithinAt
  have hE : ∀ x, 0 ≤ Real.exp (-(Fs x)) := fun x => (Real.exp_pos _).le
  -- piece 1: (0, μ/4]
  have p1 : IntegrableOn f (Set.Ioc 0 (P.μ / 4)) := by
    set K := 1 + 2 / P.μ
    refine affRuin3_piece (g := fun x => Real.exp (-c0) * (K * x ^ A + x ^ (A - 1)))
      measurableSet_Ioc (fun x hx => hmemU x hx.1 (by linarith [hx.2])) hfc ?_ ?_
    · exact (((affRuin3_rpow_int _ A (by positivity) (by linarith)).const_mul K).add
        (affRuin3_rpow_int _ (A - 1) (by positivity) (by linarith))).const_mul _
    · intro x hx
      have hx0 : 0 < x := hx.1
      have hE1 := affRuin3_exp_le (Fs x) c0 A x hx0 (h0 x hx)
      have hμx : P.μ / 2 ≤ |P.μ - x| := by
        rw [abs_of_pos (by linarith [hx.2])]; linarith [hx.2]
      have hH : 1 + 1 / x + 1 / |P.μ - x| ≤ K + 1 / x := by
        have : 1 / |P.μ - x| ≤ 2 / P.μ := by
          rw [div_le_div_iff₀ (by linarith) hμ]; linarith
        simp only [K]; linarith
      have hHnn : 0 ≤ 1 + 1 / x + 1 / |P.μ - x| := by positivity
      have hrp : x ^ (A - 1) = x ^ A * (1 / x) := by
        rw [Real.rpow_sub_one hx0.ne', div_eq_mul_one_div]
      rw [hf_def, abs_mul, abs_of_nonneg hHnn, abs_of_nonneg (hE x), hrp]
      have hxA : 0 ≤ x ^ A := Real.rpow_nonneg hx0.le A
      calc (1 + 1 / x + 1 / |P.μ - x|) * Real.exp (-(Fs x))
          ≤ (K + 1 / x) * (Real.exp (-c0) * x ^ A) :=
            mul_le_mul hH hE1 (hE x) (by positivity)
        _ = Real.exp (-c0) * (K * x ^ A + x ^ A * (1 / x)) := by ring
  -- piece 2: [μ/4, 3μ/4]
  have p2 : IntegrableOn f (Set.Icc (P.μ / 4) (3 * P.μ / 4)) :=
    (hfc.mono fun x hx => hmemU x (by linarith [hx.1]) (by linarith [hx.2])).integrableOn_compact
      isCompact_Icc
  -- piece 3: [3μ/4, μ)
  have p3 : IntegrableOn f (Set.Ico (3 * P.μ / 4) P.μ) := by
    set K := 1 + 4 / (3 * P.μ)
    have hint : ∀ s : ℝ, (-1 : ℝ) < s → IntegrableOn (fun x : ℝ => (P.μ - x) ^ s) (Set.Ico (3 * P.μ / 4) P.μ) := by
      intro s hs
      have h := (intervalIntegral.intervalIntegrable_rpow' (r := s) (a := 0) (b := P.μ / 4) hs).comp_sub_left P.μ
      rw [sub_zero, show P.μ - P.μ / 4 = 3 * P.μ / 4 by ring] at h
      have := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp h.symm
      exact ((integrableOn_Icc_iff_integrableOn_Ioc).mpr this).mono_set Set.Ico_subset_Icc_self
    refine affRuin3_piece (g := fun x => Real.exp (-c1) * (K * (P.μ - x) ^ B + (P.μ - x) ^ (B - 1)))
      measurableSet_Ico (fun x hx => hmemU x (by linarith [hx.1]) (ne_of_lt hx.2)) hfc ?_ ?_
    · exact (((hint B (by linarith)).const_mul K).add (hint (B - 1) (by linarith))).const_mul _
    · intro x hx
      have hx0 : 0 < P.μ - x := by linarith [hx.2]
      have hE1 := affRuin3_exp_le (Fs x) c1 B (P.μ - x) hx0 (h1 x hx)
      have hH : 1 + 1 / x + 1 / |P.μ - x| ≤ K + 1 / (P.μ - x) := by
        have : 1 / x ≤ 4 / (3 * P.μ) := by
          rw [div_le_div_iff₀ (by linarith [hx.1]) (by linarith)]; linarith [hx.1]
        rw [abs_of_pos hx0]; simp only [K]; linarith
      have hHnn : 0 ≤ 1 + 1 / x + 1 / |P.μ - x| := by
        have : 0 < x := by linarith [hx.1]
        positivity
      have hrp : (P.μ - x) ^ (B - 1) = (P.μ - x) ^ B * (1 / (P.μ - x)) := by
        rw [Real.rpow_sub_one hx0.ne', div_eq_mul_one_div]
      rw [hf_def, abs_mul, abs_of_nonneg hHnn, abs_of_nonneg (hE x), hrp]
      have hxB : 0 ≤ (P.μ - x) ^ B := Real.rpow_nonneg hx0.le B
      calc (1 + 1 / x + 1 / |P.μ - x|) * Real.exp (-(Fs x))
          ≤ (K + 1 / (P.μ - x)) * (Real.exp (-c1) * (P.μ - x) ^ B) :=
            mul_le_mul hH hE1 (hE x) (by positivity)
        _ = _ := by ring
  -- piece 4: (μ, 3μ/2]
  have p4 : IntegrableOn f (Set.Ioc P.μ (3 * P.μ / 2)) := by
    set K := 1 + 1 / P.μ
    have hint : ∀ s : ℝ, (-1 : ℝ) < s → IntegrableOn (fun x : ℝ => (x - P.μ) ^ s) (Set.Ioc P.μ (3 * P.μ / 2)) := by
      intro s hs
      have h := (intervalIntegral.intervalIntegrable_rpow' (r := s) (a := 0) (b := P.μ / 2) hs).comp_sub_right P.μ
      rw [zero_add, show P.μ / 2 + P.μ = 3 * P.μ / 2 by ring] at h
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp h
    refine affRuin3_piece (g := fun x => Real.exp (-c2) * (K * (x - P.μ) ^ B + (x - P.μ) ^ (B - 1)))
      measurableSet_Ioc (fun x hx => hmemU x (by linarith [hx.1]) (ne_of_gt hx.1)) hfc ?_ ?_
    · exact (((hint B (by linarith)).const_mul K).add (hint (B - 1) (by linarith))).const_mul _
    · intro x hx
      have hx0 : 0 < x - P.μ := by linarith [hx.1]
      have hE1 := affRuin3_exp_le (Fs x) c2 B (x - P.μ) hx0 (h2 x hx)
      have hH : 1 + 1 / x + 1 / |P.μ - x| ≤ K + 1 / (x - P.μ) := by
        have : 1 / x ≤ 1 / P.μ := one_div_le_one_div_of_le hμ hx.1.le
        rw [abs_sub_comm, abs_of_pos hx0]; simp only [K]; linarith
      have hHnn : 0 ≤ 1 + 1 / x + 1 / |P.μ - x| := by
        have : 0 < x := by linarith [hx.1]
        positivity
      have hrp : (x - P.μ) ^ (B - 1) = (x - P.μ) ^ B * (1 / (x - P.μ)) := by
        rw [Real.rpow_sub_one hx0.ne', div_eq_mul_one_div]
      rw [hf_def, abs_mul, abs_of_nonneg hHnn, abs_of_nonneg (hE x), hrp]
      have hxB : 0 ≤ (x - P.μ) ^ B := Real.rpow_nonneg hx0.le B
      calc (1 + 1 / x + 1 / |P.μ - x|) * Real.exp (-(Fs x))
          ≤ (K + 1 / (x - P.μ)) * (Real.exp (-c2) * (x - P.μ) ^ B) :=
            mul_le_mul hH hE1 (hE x) (by positivity)
        _ = _ := by ring
  -- piece 5: [3μ/2, x1]
  have p5 : IntegrableOn f (Set.Icc (3 * P.μ / 2) x1) :=
    (hfc.mono fun x hx => hmemU x (by linarith [hx.1]) (by linarith [hx.1])).integrableOn_compact
      isCompact_Icc
  -- piece 6: [x1, ∞)
  have p6 : IntegrableOn f (Set.Ici x1) := by
    refine affRuin3_piece (g := fun x => 3 * Real.exp (-c3) * Real.exp (-(P.p / P.r / 2) * x))
      measurableSet_Ici (fun x hx => hmemU x (by linarith [hx.out]) (by linarith [hx.out])) hfc ?_ ?_
    · refine (integrableOn_Ici_iff_integrableOn_Ioi).mpr ?_
      exact (exp_neg_integrableOn_Ioi x1 hpr).const_mul _
    · intro x hx
      have hx' : x1 ≤ x := hx
      have hE1 : Real.exp (-(Fs x)) ≤ Real.exp (-c3) * Real.exp (-(P.p / P.r / 2) * x) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [h3 x hx'])
      have hH : 1 + 1 / x + 1 / |P.μ - x| ≤ 3 := by
        have a1 : 1 / x ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        have a2 : 1 / |P.μ - x| ≤ 1 := by
          rw [abs_sub_comm, abs_of_pos (by linarith), div_le_one (by linarith)]; linarith
        linarith
      have hHnn : 0 ≤ 1 + 1 / x + 1 / |P.μ - x| := by
        have : 0 < x := by linarith
        positivity
      rw [hf_def, abs_mul, abs_of_nonneg hHnn, abs_of_nonneg (hE x)]
      calc (1 + 1 / x + 1 / |P.μ - x|) * Real.exp (-(Fs x))
          ≤ 3 * (Real.exp (-c3) * Real.exp (-(P.p / P.r / 2) * x)) :=
            mul_le_mul hH hE1 (hE x) (by norm_num)
        _ = _ := by ring
  have p0 : IntegrableOn f {P.μ} := IntegrableOn.of_measure_zero (Real.volume_singleton)
  have hall := ((((((p1.union p2).union p3).union p0).union p4).union p5).union p6)
  refine hall.mono_set fun x hx => ?_
  have hx0 : 0 < x := hx
  simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Icc, Set.mem_Ico, Set.mem_singleton_iff,
    Set.mem_Ici]
  by_cases a1 : x ≤ P.μ / 4
  · left; left; left; left; left; left; exact ⟨hx0, a1⟩
  by_cases a2 : x ≤ 3 * P.μ / 4
  · left; left; left; left; left; right; exact ⟨by linarith, a2⟩
  by_cases a3 : x < P.μ
  · left; left; left; left; right; exact ⟨by linarith, a3⟩
  by_cases a4 : x = P.μ
  · left; left; left; right; exact a4
  by_cases a5 : x ≤ 3 * P.μ / 2
  · left; left; right; exact ⟨lt_of_le_of_ne (not_lt.mp a3) (Ne.symm a4), a5⟩
  by_cases a6 : x ≤ x1
  · left; right; exact ⟨by linarith, a6⟩
  · right; linarith

theorem solution (P : Params) (hS : P.Standing) (Fs : ℝ → ℝ)
    (hF : IsPrimitiveF P Fs) :
    IntegrableOn (fun η => G1 P η * Real.exp (-(Fs η))) (Set.Ioi 0) ∧
    IntegrableOn (fun η => G2 P η * Real.exp (-(Fs η))) (Set.Ioi 0) ∧
    IntegrableOn (fun η => G3 P η * Real.exp (-(Fs η))) (Set.Ioi 0) := by
  obtain ⟨hp, hr, hlp, hlm, hμ, hν, hα, hβ, -⟩ := id hS
  have hHE := affRuin3_HE P hS Fs hF
  set H := fun ϑ : ℝ => 1 + 1 / ϑ + 1 / |P.μ - ϑ| with hH_def
  set CG := P.p / P.r + P.lamPlus / P.r + P.lamMinus / P.r * (1 + 1 / P.β) with hCG
  have hCG0 : 0 ≤ CG := by positivity
  set U := Set.Ioi (0:ℝ) \ {P.μ} with hU
  have hUae : U =ᵐ[volume] Set.Ioi (0:ℝ) := sdiff_null_ae_eq_self Real.volume_singleton
  have hrestr : volume.restrict U = volume.restrict (Set.Ioi (0:ℝ)) := Measure.restrict_congr_set hUae
  have hUm : MeasurableSet U := measurableSet_Ioi.diff (measurableSet_singleton _)
  have hFc : ContinuousOn Fs U := fun x hx => (hF x hx.1 hx.2).continuousAt.continuousWithinAt
  have hEc : ContinuousOn (fun x => Real.exp (-(Fs x))) U :=
    Real.continuous_exp.comp_continuousOn hFc.neg
  have hEm : AEStronglyMeasurable (fun x => Real.exp (-(Fs x))) (volume.restrict (Set.Ioi 0)) := by
    rw [← hrestr]; exact hEc.aestronglyMeasurable hUm
  have hH1 : ∀ x ∈ U, 1 ≤ H x ∧ 1 / x ≤ H x ∧ 1 / |P.μ - x| ≤ H x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have a : 0 ≤ 1 / x := by positivity
    have b : 0 ≤ 1 / |P.μ - x| := by positivity
    simp only [hH_def]
    exact ⟨by linarith, by linarith, by linarith⟩
  -- generic conclusion from a pointwise bound `|g| ≤ CG * H` on `U`
  have concl : ∀ g : ℝ → ℝ,
      AEStronglyMeasurable (fun η => g η * Real.exp (-(Fs η))) (volume.restrict (Set.Ioi 0)) →
      (∀ x ∈ U, |g x| ≤ CG * H x) →
      IntegrableOn (fun η => g η * Real.exp (-(Fs η))) (Set.Ioi 0) := by
    intro g hgm hgb
    refine Integrable.mono' (hHE.const_mul CG) hgm ?_
    rw [← hrestr]
    refine (ae_restrict_iff' hUm).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := hgb x hx
    calc |g x| * Real.exp (-(Fs x)) ≤ CG * H x * Real.exp (-(Fs x)) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = CG * ((1 + 1 / x + 1 / |P.μ - x|) * Real.exp (-(Fs x))) := by
          simp only [hH_def]; ring
  have hlr : 0 < P.lamPlus / P.r := div_pos hlp hr
  have hmr : 0 < P.lamMinus / P.r := div_pos hlm hr
  have hpr : 0 < P.p / P.r := div_pos hp hr
  have hβi : 0 ≤ 1 / P.β := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine concl _ (by
      have : AEStronglyMeasurable (G1 P) (volume.restrict (Set.Ioi 0)) := by
        unfold G1; exact aestronglyMeasurable_const
      exact this.mul hEm) fun x hx => ?_
    obtain ⟨h1, -, -⟩ := hH1 x hx
    simp only [G1, abs_neg, abs_of_pos hpr]
    have : P.p / P.r ≤ CG := by
      simp only [hCG]; have : 0 ≤ P.lamMinus / P.r * (1 + 1 / P.β) := by positivity
      linarith
    nlinarith
  · refine concl _ (by
      have : ContinuousOn (G2 P) U := by
        intro x hx
        have : P.μ - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx.2)
        unfold G2
        exact (continuousAt_const.mul (continuousAt_const.div
          (continuousAt_const.sub continuousAt_id) this)).continuousWithinAt
      rw [← hrestr]
      exact (this.mul hEc).aestronglyMeasurable hUm) fun x hx => ?_
    obtain ⟨h1, -, h3⟩ := hH1 x hx
    simp only [G2, abs_mul, abs_neg, abs_of_pos hlr, abs_div, abs_one]
    have : P.lamPlus / P.r ≤ CG := by
      simp only [hCG]; have : 0 ≤ P.lamMinus / P.r * (1 + 1 / P.β) := by positivity
      linarith
    have hnn : 0 ≤ 1 / |P.μ - x| := by positivity
    calc P.lamPlus / P.r * (1 / |P.μ - x|) ≤ P.lamPlus / P.r * H x :=
          mul_le_mul_of_nonneg_left h3 hlr.le
      _ ≤ CG * H x := mul_le_mul_of_nonneg_right this (by linarith)
  · refine concl _ ((affRuin3_G3_measurable P hS).aestronglyMeasurable.mul hEm) fun x hx => ?_
    obtain ⟨h1, h2, -⟩ := hH1 x hx
    have hb := affRuin3_G3_bound P hS x hx.1
    have : 1 / x + 1 / P.β ≤ (1 + 1 / P.β) * H x := by nlinarith
    have : P.lamMinus / P.r * (1 + 1 / P.β) ≤ CG := by simp only [hCG]; linarith
    calc |G3 P x| ≤ P.lamMinus / P.r * (1 / x + 1 / P.β) := hb
      _ ≤ P.lamMinus / P.r * ((1 + 1 / P.β) * H x) := mul_le_mul_of_nonneg_left (by assumption) hmr.le
      _ = (P.lamMinus / P.r * (1 + 1 / P.β)) * H x := by ring
      _ ≤ CG * H x := mul_le_mul_of_nonneg_right this (by linarith)

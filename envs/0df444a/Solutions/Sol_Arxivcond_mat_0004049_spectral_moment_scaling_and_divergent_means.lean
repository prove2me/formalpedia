-- Prove2me | solution 1 for Arxivcond_mat_0004049.spectral_moment_scaling_and_divergent_means
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T18:07:51.627599+00:00
-- url     : https://prove2.me/submissions/f1a871f1-9d6f-4e56-91a6-145bbf4f23af

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

/-!
Eq. (15): the spectral-moment density has divergent means and a most probable point on the
scale `B₁ ∼ γN`, `B₂ ∼ γ²N³`.
-/

open MeasureTheory Filter Topology Set


namespace Arxivcond_mat_0004049.M5Means

/-- `x ↦ c / x` has infinite lower integral on `[a, ∞)`. -/
lemma lintegral_Ici_div_eq_top {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ x, (Ici a).indicator (fun x => ENNReal.ofReal (c / x)) x = ⊤ := by
  rw [lintegral_indicator measurableSet_Ici]
  by_contra h
  apply not_integrableOn_Ioi_inv (a := a)
  have hnn : 0 ≤ᵐ[volume.restrict (Ici a)] fun x => c / x :=
    ae_restrict_of_forall_mem measurableSet_Ici fun x hx => div_nonneg hc.le (ha.le.trans hx)
  have hint : IntegrableOn (fun x => c / x) (Ici a) :=
    ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 h)⟩
  refine IntegrableOn.congr_fun ((hint.mono_set Ioi_subset_Ici_self).const_mul c⁻¹)
    (fun x _ => ?_) measurableSet_Ioi
  rw [mul_div_assoc', inv_mul_cancel₀ hc.ne', one_div]

/-- `Ei` is nonpositive at nonpositive arguments. -/
lemma expIntegralEi_nonpos {x : ℝ} (hx : x ≤ 0) : expIntegralEi x ≤ 0 := by
  unfold expIntegralEi
  have : 0 ≤ ∫ t in Ioi (-x), Real.exp (-t) / t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      div_nonneg (Real.exp_pos _).le (by have : -x < t := ht; linarith)
  linarith

/-- On the region `γN ≤ B₁`, `N B₁²/8 ≤ B₂ ≤ N B₁²/4` the density is at least `64 e^{-10} γ / B₁⁴`. -/
lemma density_lower {N : ℕ} (hN : 1 ≤ N) {γ : ℝ} (hγ : 0 < γ) {B1 B2 : ℝ}
    (h1 : γ * N ≤ B1) (h2 : N * B1 ^ 2 / 8 ≤ B2) (h3 : B2 ≤ N * B1 ^ 2 / 4) :
    64 * Real.exp (-10) * γ / B1 ^ 4 ≤ eq15Density N γ B1 B2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hB1 : 0 < B1 := (mul_pos hγ hn).trans_le h1
  have hB2 : 0 < B2 := lt_of_lt_of_le (by positivity) h2
  unfold eq15Density
  rw [if_pos ⟨hB1, hB2⟩]
  have hE1 : Real.exp (-8) ≤ Real.exp (-(N : ℝ) * B1 ^ 2 / B2) := by
    apply Real.exp_le_exp.2
    rw [neg_mul, neg_div, neg_le_neg_iff, div_le_iff₀ hB2]
    linarith
  have hE2 : Real.exp (-2) ≤ Real.exp (-2 * γ * (N : ℝ) / B1) := by
    apply Real.exp_le_exp.2
    rw [le_div_iff₀ hB1]
    linarith
  have hEi : expIntegralEi (-2 * γ * (N : ℝ) / B1) ≤ 0 :=
    expIntegralEi_nonpos (div_nonpos_of_nonpos_of_nonneg (by nlinarith) hB1.le)
  have hpoly : 0 ≤ 2 * B2 ^ 2 - 4 * B1 ^ 2 * B2 * (N : ℝ) + B1 ^ 4 * (N : ℝ) ^ 2 := by
    have hs : 0 ≤ (N : ℝ) * B1 ^ 2 - 4 * B2 := by linarith
    nlinarith [mul_nonneg hs (by positivity : (0 : ℝ) ≤ N * B1 ^ 2), sq_nonneg B2]
  have hT : γ ^ 3 * (N : ℝ) ^ 5 / (4 * B2 ^ 5) *
      (2 * B2 ^ 2 - 4 * B1 ^ 2 * B2 * (N : ℝ) + B1 ^ 4 * (N : ℝ) ^ 2) *
      expIntegralEi (-2 * γ * (N : ℝ) / B1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) hpoly) hEi
  have hP : 64 * γ / B1 ^ 4 ≤ B1 ^ 2 * γ * (N : ℝ) ^ 3 / B2 ^ 4 * (B2 + γ * (N : ℝ) ^ 2 * B1) := by
    calc 64 * γ / B1 ^ 4 ≤ B1 ^ 2 * γ * (N : ℝ) ^ 3 / B2 ^ 3 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          calc 64 * γ * B2 ^ 3 ≤ 64 * γ * ((N : ℝ) * B1 ^ 2 / 4) ^ 3 := by gcongr
            _ = B1 ^ 2 * γ * (N : ℝ) ^ 3 * B1 ^ 4 := by ring
      _ = B1 ^ 2 * γ * (N : ℝ) ^ 3 / B2 ^ 4 * B2 := by field_simp
      _ ≤ B1 ^ 2 * γ * (N : ℝ) ^ 3 / B2 ^ 4 * (B2 + γ * (N : ℝ) ^ 2 * B1) := by
          gcongr; exact le_add_of_nonneg_right (by positivity)
  have hF : 64 * γ / B1 ^ 4 * Real.exp (-2) ≤
      B1 ^ 2 * γ * (N : ℝ) ^ 3 / B2 ^ 4 * (B2 + γ * (N : ℝ) ^ 2 * B1) *
        Real.exp (-2 * γ * (N : ℝ) / B1) := by
    gcongr
  calc 64 * Real.exp (-10) * γ / B1 ^ 4 = Real.exp (-8) * (64 * γ / B1 ^ 4 * Real.exp (-2)) := by
        rw [show (-10 : ℝ) = -8 + -2 by norm_num, Real.exp_add]; ring
    _ ≤ _ := mul_le_mul hE1 (by linarith) (by positivity) (Real.exp_pos _).le

/-- Any `f` bounded below by `k / B₁³` on the region has infinite lower integral. -/
lemma lintegral_eq_top_of_region {a n k : ℝ} (ha : 0 < a) (hn : 0 < n) (hk : 0 < k)
    (f : ℝ × ℝ → ℝ)
    (hf : ∀ B : ℝ × ℝ, a ≤ B.1 → n * B.1 ^ 2 / 8 ≤ B.2 → B.2 ≤ n * B.1 ^ 2 / 4 →
      k / B.1 ^ 3 ≤ f B) :
    ∫⁻ B : ℝ × ℝ, ENNReal.ofReal (f B) = ⊤ := by
  set S : Set (ℝ × ℝ) := {B | a ≤ B.1} ∩ ({B | n * B.1 ^ 2 / 8 ≤ B.2} ∩ {B | B.2 ≤ n * B.1 ^ 2 / 4})
    with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le (by fun_prop) measurable_snd).inter
        (measurableSet_le measurable_snd (by fun_prop)))
  set g : ℝ × ℝ → ENNReal := fun B => ENNReal.ofReal (k / B.1 ^ 3) with hgdef
  have hmeas : Measurable (S.indicator g) :=
    (Measurable.ennreal_ofReal (by fun_prop)).indicator hS
  have hle : ∀ B, S.indicator g B ≤ ENNReal.ofReal (f B) := by
    intro B
    by_cases hB : B ∈ S
    · rw [indicator_of_mem hB]
      exact ENNReal.ofReal_le_ofReal (hf B hB.1 hB.2.1 hB.2.2)
    · rw [indicator_of_notMem hB]; positivity
  apply eq_top_iff.2
  calc (⊤ : ENNReal) = ∫⁻ x, (Ici a).indicator (fun x => ENNReal.ofReal (k * n / 8 / x)) x :=
        (lintegral_Ici_div_eq_top ha (by positivity)).symm
    _ ≤ ∫⁻ x, ∫⁻ y, S.indicator g (x, y) := lintegral_mono fun x => ?_
    _ = ∫⁻ B, S.indicator g B := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
    _ ≤ ∫⁻ B, ENNReal.ofReal (f B) := lintegral_mono hle
  by_cases hx : a ≤ x
  · rw [indicator_of_mem (show x ∈ Ici a from hx)]
    have hx0 : 0 < x := ha.trans_le hx
    have hfun : (fun y => S.indicator g (x, y)) =
        (Icc (n * x ^ 2 / 8) (n * x ^ 2 / 4)).indicator (fun _ => ENNReal.ofReal (k / x ^ 3)) := by
      funext y
      by_cases hy : y ∈ Icc (n * x ^ 2 / 8) (n * x ^ 2 / 4)
      · rw [indicator_of_mem hy, indicator_of_mem (show (x, y) ∈ S from ⟨hx, hy.1, hy.2⟩)]
      · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy ⟨h.2.1, h.2.2⟩)]
    rw [hfun, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal (le_of_eq _)
    field_simp
    ring
  · rw [indicator_of_notMem (show x ∉ Ici a from hx)]; positivity

end Arxivcond_mat_0004049.M5Means

open Arxivcond_mat_0004049 Arxivcond_mat_0004049.M5Means in
theorem M5Means.means : ∀ N : ℕ, 1 ≤ N → ∀ γ : ℝ, 0 < γ →
    ∫⁻ B : ℝ × ℝ, ENNReal.ofReal (B.1 * eq15Density N γ B.1 B.2) = ⊤ ∧
    ∫⁻ B : ℝ × ℝ, ENNReal.ofReal (B.2 * eq15Density N γ B.1 B.2) = ⊤ := by
  intro N hN γ hγ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < γ * N := mul_pos hγ hNpos
  have hc : 0 < 64 * Real.exp (-10) * γ := by positivity
  constructor
  · refine lintegral_eq_top_of_region ha hNpos hc _ ?_
    intro B h1 h2 h3
    have hB1 : 0 < B.1 := ha.trans_le h1
    have hd := density_lower hN hγ h1 h2 h3
    calc 64 * Real.exp (-10) * γ / B.1 ^ 3
        = B.1 * (64 * Real.exp (-10) * γ / B.1 ^ 4) := by field_simp
      _ ≤ B.1 * eq15Density N γ B.1 B.2 := by gcongr
  · refine lintegral_eq_top_of_region ha hNpos
      (mul_pos (mul_pos (by positivity : (0:ℝ) < N / 8) hc) ha) _ ?_
    intro B h1 h2 h3
    have hB1 : 0 < B.1 := ha.trans_le h1
    have hd := density_lower hN hγ h1 h2 h3
    have hdn : 0 ≤ 64 * Real.exp (-10) * γ / B.1 ^ 4 := by positivity
    have hB2 : 0 ≤ B.2 := le_trans (by positivity) h2
    calc N / 8 * (64 * Real.exp (-10) * γ) * (γ * N) / B.1 ^ 3
        ≤ N / 8 * (64 * Real.exp (-10) * γ) * B.1 / B.1 ^ 3 := by gcongr
      _ = N * B.1 ^ 2 / 8 * (64 * Real.exp (-10) * γ / B.1 ^ 4) := by field_simp
      _ ≤ B.2 * eq15Density N γ B.1 B.2 := by gcongr

open Arxivcond_mat_0004049

namespace M5Mode

/-- `E₁(z) = ∫_z^∞ e^{-t}/t dt`, so that `Ei(-z) = -E₁(z)`. -/
noncomputable def E1 (z : ℝ) : ℝ := ∫ t in Ioi z, Real.exp (-t) / t

/-- Eq. (15) in the variables `x = B₁/(γN)`, `t = B₂/(N B₁²)`, times `γ³N⁴`. -/
noncomputable def G (x t : ℝ) : ℝ :=
  Real.exp (-1 / t) * ((1 / (x ^ 5 * t ^ 4) + 1 / (x ^ 4 * t ^ 3)) * Real.exp (-2 / x) +
    (1 - 4 * t + 2 * t ^ 2) / (4 * x ^ 6 * t ^ 5) * E1 (2 / x))

/-- `e^{-c/s}/s^k`, the shape of every factor of `G`. -/
noncomputable def V (c : ℝ) (k : ℕ) (s : ℝ) : ℝ := Real.exp (-c / s) / s ^ k

lemma E1_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ E1 z := by
  unfold E1
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have : 0 < t := lt_of_le_of_lt hz ht
  positivity

lemma E1_le {z : ℝ} (hz : 0 < z) : E1 z ≤ Real.exp (-z) / z := by
  unfold E1
  calc ∫ t in Ioi z, Real.exp (-t) / t ≤ ∫ t in Ioi z, Real.exp (-t) / z := by
        refine integral_mono_of_nonneg ?_ ((integrableOn_exp_neg_Ioi z).div_const z) ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have : 0 < t := lt_trans hz ht
          positivity
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht' : z < t := ht
          gcongr
    _ = Real.exp (-z) / z := by rw [integral_div, integral_exp_neg_Ioi]

lemma f_integrableOn {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t => Real.exp (-t) / t) (Ioi z) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi z).div_const z) ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ => Real.exp (-t) / t).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : z < t := ht
    have : 0 < t := lt_trans hz ht'
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    gcongr

lemma E1_continuousOn : ContinuousOn E1 (Ioi 0) := by
  intro z0 hz0
  have hz0' : 0 < z0 := hz0
  apply ContinuousAt.continuousWithinAt
  have heq : (fun z => (∫ t in z..1, Real.exp (-t) / t) + E1 1) =ᶠ[𝓝 z0] E1 := by
    filter_upwards [Ioi_mem_nhds hz0'] with z hz
    exact intervalIntegral.integral_interval_add_Ioi (f_integrableOn hz) (f_integrableOn one_pos)
  refine ContinuousAt.congr (ContinuousAt.add ?_ continuousAt_const) heq
  have hf : ContinuousAt (fun t => Real.exp (-t) / t) z0 :=
    ContinuousAt.div (by fun_prop) continuousAt_id hz0'.ne'
  have hm : 0 < min z0 1 / 2 := by positivity
  have hii : IntervalIntegrable (fun t => Real.exp (-t) / t) volume z0 1 := by
    refine IntegrableOn.intervalIntegrable ((f_integrableOn hm).mono_set fun t ht => ?_)
    simp only [mem_Ioi]
    have h1 : min z0 1 ≤ t := by
      rcases le_total z0 1 with h | h
      · simpa [uIcc_of_le h, min_eq_left h] using ht.1
      · simpa [uIcc_of_ge h, min_eq_right h] using ht.1
    linarith [lt_min hz0' one_pos]
  exact (intervalIntegral.integral_hasDerivAt_left hii
    ((by fun_prop : Measurable fun t : ℝ => Real.exp (-t) / t).stronglyMeasurable.stronglyMeasurableAtFilter)
    hf).continuousAt

lemma expIntegralEi_neg (z : ℝ) : expIntegralEi (-z) = -E1 z := by
  simp [expIntegralEi, E1]

lemma eq15_scale (N : ℕ) (hN : 1 ≤ N) (γ : ℝ) (hγ : 0 < γ) (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    eq15Density N γ (γ * N * x) (γ ^ 2 * (N : ℝ) ^ 3 * (x ^ 2 * t)) = G x t / (γ ^ 3 * (N : ℝ) ^ 4) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold eq15Density
  rw [if_pos ⟨by positivity, by positivity⟩]
  have e1 : -(N : ℝ) * (γ * N * x) ^ 2 / (γ ^ 2 * (N : ℝ) ^ 3 * (x ^ 2 * t)) = -1 / t := by
    field_simp
  have e2 : -2 * γ * (N : ℝ) / (γ * N * x) = -2 / x := by
    field_simp
  have hEi : expIntegralEi (-2 / x) = -E1 (2 / x) := by
    rw [neg_div]; exact expIntegralEi_neg _
  rw [e1, e2, hEi]
  unfold G
  field_simp
  ring

lemma V_nonneg (c : ℝ) (k : ℕ) {s : ℝ} (hs : 0 < s) : 0 ≤ V c k s := by
  unfold V; positivity

lemma V_le (c : ℝ) (hc : 0 < c) (k : ℕ) {s : ℝ} (hs : 0 < s) : V c k s ≤ k.factorial / c ^ k := by
  unfold V
  have h := Real.pow_div_factorial_le_exp (c / s) (by positivity) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hE : 0 < Real.exp (c / s) := Real.exp_pos _
  rw [neg_div, Real.exp_neg, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
  calc (Real.exp (c / s))⁻¹ * c ^ k ≤ (Real.exp (c / s))⁻¹ * (Real.exp (c / s) * (s ^ k * k.factorial)) := by
        gcongr
    _ = k.factorial * s ^ k := by field_simp

lemma V_tendsto_zero (c : ℝ) (hc : 0 < c) (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (V c k) (𝓝[>] 0 ⊔ atTop) (𝓝 0) := by
  refine Tendsto.sup ?_ ?_
  · have hu : Tendsto (fun s : ℝ => c * s⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop hc
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hu).const_mul (c ^ k)⁻¹
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    simp only [Function.comp, V]
    field_simp
    rw [div_pow, div_mul_cancel₀ _ (by positivity)]
  · have hk' : k ≠ 0 := by omega
    have hup : Tendsto (fun s : ℝ => (s ^ k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop hk')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs using V_nonneg c k hs
    · filter_upwards [eventually_gt_atTop 0] with s hs
      unfold V
      rw [div_eq_mul_inv]
      have : Real.exp (-c / s) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 < c / s := by positivity
        rw [neg_div]; linarith)
      have : 0 ≤ (s ^ k)⁻¹ := by positivity
      nlinarith

/-- The `t`-factor of the bound on `G`. -/
noncomputable def A (t : ℝ) : ℝ := 2 * (V 1 3 t + V 1 4 t + V 1 5 t)

/-- The `x`-factor of the bound on `G`. -/
noncomputable def B (x : ℝ) : ℝ := V 2 4 x + V 2 5 x

lemma G_le (x t : ℝ) (hx : 0 < x) (ht : 0 < t) : G x t ≤ A t * B x := by
  have hE0 := E1_nonneg (show (0 : ℝ) ≤ 2 / x by positivity)
  have hE1 : E1 (2 / x) ≤ Real.exp (-2 / x) * x / 2 := by
    have := E1_le (show (0 : ℝ) < 2 / x by positivity)
    rw [neg_div]
    calc E1 (2 / x) ≤ Real.exp (-(2 / x)) / (2 / x) := this
      _ = Real.exp (-(2 / x)) * x / 2 := by field_simp
  set et := Real.exp (-1 / t) with het
  set ex := Real.exp (-2 / x) with hex
  have het0 : 0 < et := Real.exp_pos _
  have hex0 : 0 < ex := Real.exp_pos _
  have step : (1 - 4 * t + 2 * t ^ 2) / (4 * x ^ 6 * t ^ 5) * E1 (2 / x) ≤
      (1 + 4 * t + 2 * t ^ 2) / (4 * x ^ 6 * t ^ 5) * (ex * x / 2) := by
    calc (1 - 4 * t + 2 * t ^ 2) / (4 * x ^ 6 * t ^ 5) * E1 (2 / x)
        ≤ (1 + 4 * t + 2 * t ^ 2) / (4 * x ^ 6 * t ^ 5) * E1 (2 / x) := by
          gcongr; linarith
      _ ≤ (1 + 4 * t + 2 * t ^ 2) / (4 * x ^ 6 * t ^ 5) * (ex * x / 2) := by gcongr
  have hG : G x t ≤ et * ((1 / (x ^ 5 * t ^ 4) + 1 / (x ^ 4 * t ^ 3)) * ex +
      (1 + 4 * t + 2 * t ^ 2) / (4 * x ^ 6 * t ^ 5) * (ex * x / 2)) := by
    unfold G; rw [← het, ← hex]; gcongr
  refine hG.trans (le_of_sub_nonneg ?_)
  have key : A t * B x - et * ((1 / (x ^ 5 * t ^ 4) + 1 / (x ^ 4 * t ^ 3)) * ex +
      (1 + 4 * t + 2 * t ^ 2) / (4 * x ^ 6 * t ^ 5) * (ex * x / 2)) =
      et * ex * (16 * (x * t ^ 2 + x * t + x + t ^ 2 + t + 1) -
        (1 + 12 * t + 2 * t ^ 2 + 8 * x * t ^ 2)) / (8 * x ^ 5 * t ^ 5) := by
    unfold A B V
    rw [← het, ← hex]
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (by positivity)
  nlinarith [mul_pos hx ht, mul_pos (mul_pos hx ht) ht]

lemma G_continuousOn : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Ioi 0 ×ˢ Ioi 0) := by
  rintro p ⟨hx, ht⟩
  have hx' : 0 < p.1 := hx
  have ht' : 0 < p.2 := ht
  apply ContinuousAt.continuousWithinAt
  have hE : ContinuousAt (fun q : ℝ × ℝ => E1 (2 / q.1)) p := by
    have h1 : ContinuousAt E1 (2 / p.1) :=
      E1_continuousOn.continuousAt (Ioi_mem_nhds (by positivity))
    exact h1.comp (f := fun q : ℝ × ℝ => 2 / q.1)
      (continuousAt_const.div continuousAt_fst hx'.ne')
  unfold G
  fun_prop (disch := positivity)

lemma G_pos_quarter : 0 < G 1 (1 / 4) := by
  have hE := E1_nonneg (show (0 : ℝ) ≤ 2 / 1 by norm_num)
  unfold G
  norm_num at hE ⊢
  positivity

/-- A product of two factors that are bounded and vanish at both ends of `(0, ∞)` is small outside
a compact box. -/
lemma box (a b : ℝ → ℝ) (Ma Mb : ℝ) (ha0 : ∀ s, 0 < s → 0 ≤ a s) (hb0 : ∀ s, 0 < s → 0 ≤ b s)
    (haM : ∀ s, 0 < s → a s ≤ Ma) (hbM : ∀ s, 0 < s → b s ≤ Mb)
    (ha : Tendsto a (𝓝[>] 0 ⊔ atTop) (𝓝 0)) (hb : Tendsto b (𝓝[>] 0 ⊔ atTop) (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ l L l' L' : ℝ, 0 < l ∧ 0 < l' ∧ ∀ x t, 0 < x → 0 < t →
      (x ∉ Icc l L ∨ t ∉ Icc l' L') → a t * b x < ε := by
  set Ma' := max Ma 1
  set Mb' := max Mb 1
  have hMa : 0 < Ma' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMb : 0 < Mb' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb' : ∀ᶠ x in 𝓝[>] 0 ⊔ atTop, b x < ε / Ma' := hb (Iio_mem_nhds (by positivity))
  have ha' : ∀ᶠ t in 𝓝[>] 0 ⊔ atTop, a t < ε / Mb' := ha (Iio_mem_nhds (by positivity))
  rw [eventually_sup] at hb' ha'
  obtain ⟨l, hl, hbl⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hb'.1
  obtain ⟨L, hbL⟩ := eventually_atTop.mp hb'.2
  obtain ⟨l', hl', hal⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp ha'.1
  obtain ⟨L', haL⟩ := eventually_atTop.mp ha'.2
  refine ⟨l, L, l', L', hl, hl', fun x t hx ht h => ?_⟩
  rcases h with h | h
  · have hbx : b x < ε / Ma' := by
      rw [mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · exact hbl ⟨hx, h⟩
      · exact hbL x h.le
    have hat : a t ≤ Ma' := (haM t ht).trans (le_max_left _ _)
    calc a t * b x ≤ Ma' * b x := mul_le_mul_of_nonneg_right hat (hb0 x hx)
      _ < Ma' * (ε / Ma') := mul_lt_mul_of_pos_left hbx hMa
      _ = ε := by field_simp
  · have hat : a t < ε / Mb' := by
      rw [mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · exact hal ⟨ht, h⟩
      · exact haL t h.le
    have hbx : b x ≤ Mb' := (hbM x hx).trans (le_max_left _ _)
    calc a t * b x ≤ a t * Mb' := mul_le_mul_of_nonneg_left hbx (ha0 t ht)
      _ < ε / Mb' * Mb' := mul_lt_mul_of_pos_right hat hMb
      _ = ε := by field_simp

lemma G_max : ∃ x₀ t₀ : ℝ, 0 < x₀ ∧ 0 < t₀ ∧ 0 < G x₀ t₀ ∧
    ∀ x t, 0 < x → 0 < t → G x t ≤ G x₀ t₀ := by
  have hA0 : ∀ s, 0 < s → 0 ≤ A s := fun s hs => by
    unfold A; have := V_nonneg 1 3 hs; have := V_nonneg 1 4 hs; have := V_nonneg 1 5 hs; positivity
  have hB0 : ∀ s, 0 < s → 0 ≤ B s := fun s hs => by
    unfold B; have := V_nonneg 2 4 hs; have := V_nonneg 2 5 hs; positivity
  have hAM : ∀ s, 0 < s → A s ≤ 2 * ((3 : ℕ).factorial / 1 ^ 3 + (4 : ℕ).factorial / 1 ^ 4 +
      (5 : ℕ).factorial / 1 ^ 5) := fun s hs => by
    unfold A
    have := V_le 1 one_pos 3 hs; have := V_le 1 one_pos 4 hs; have := V_le 1 one_pos 5 hs
    gcongr
  have hBM : ∀ s, 0 < s → B s ≤ (4 : ℕ).factorial / 2 ^ 4 + (5 : ℕ).factorial / 2 ^ 5 := fun s hs => by
    unfold B
    have := V_le 2 two_pos 4 hs; have := V_le 2 two_pos 5 hs
    gcongr
  have hAt : Tendsto A (𝓝[>] 0 ⊔ atTop) (𝓝 0) := by
    unfold A
    have := (((V_tendsto_zero 1 one_pos 3 (by norm_num)).add
      (V_tendsto_zero 1 one_pos 4 (by norm_num))).add
      (V_tendsto_zero 1 one_pos 5 (by norm_num))).const_mul 2
    simpa using this
  have hBt : Tendsto B (𝓝[>] 0 ⊔ atTop) (𝓝 0) := by
    unfold B
    have := (V_tendsto_zero 2 two_pos 4 (by norm_num)).add (V_tendsto_zero 2 two_pos 5 (by norm_num))
    simpa using this
  obtain ⟨l, L, l', L', hl, hl', hbox⟩ :=
    box A B _ _ hA0 hB0 hAM hBM hAt hBt (G 1 (1 / 4)) G_pos_quarter
  have hout : ∀ x t, 0 < x → 0 < t → (x ∉ Icc l L ∨ t ∉ Icc l' L') → G x t < G 1 (1 / 4) :=
    fun x t hx ht h => (G_le x t hx ht).trans_lt (hbox x t hx ht h)
  have hK : IsCompact (Icc l L ×ˢ Icc l' L') := isCompact_Icc.prod isCompact_Icc
  have hmem : ((1 : ℝ), (1 : ℝ) / 4) ∈ Icc l L ×ˢ Icc l' L' := by
    by_contra h
    rw [Set.mem_prod, not_and_or] at h
    exact lt_irrefl _ (hout 1 (1 / 4) one_pos (by norm_num) h)
  have hsub : Icc l L ×ˢ Icc l' L' ⊆ Ioi 0 ×ˢ Ioi 0 := fun p hp =>
    ⟨lt_of_lt_of_le hl hp.1.1, lt_of_lt_of_le hl' hp.2.1⟩
  obtain ⟨p, hp, hpmax⟩ := hK.exists_isMaxOn ⟨_, hmem⟩ (G_continuousOn.mono hsub)
  have hpm : G 1 (1 / 4) ≤ G p.1 p.2 := hpmax hmem
  refine ⟨p.1, p.2, (hsub hp).1, (hsub hp).2, lt_of_lt_of_le G_pos_quarter hpm, fun x t hx ht => ?_⟩
  by_cases hin : x ∈ Icc l L ∧ t ∈ Icc l' L'
  · exact hpmax (show (x, t) ∈ Icc l L ×ˢ Icc l' L' from hin)
  · rw [not_and_or] at hin
    exact (hout x t hx ht hin).le.trans hpm

end M5Mode

open M5Mode in
theorem M5Mode.mode : ∃ b1 b2 : ℝ, 0 < b1 ∧ 0 < b2 ∧ ∀ N : ℕ, 1 ≤ N → ∀ γ : ℝ, 0 < γ → ∀ B1 B2 : ℝ,
    eq15Density N γ B1 B2 ≤ eq15Density N γ (γ * N * b1) (γ ^ 2 * (N : ℝ) ^ 3 * b2) := by
  obtain ⟨x₀, t₀, hx₀, ht₀, hpos, hmax⟩ := G_max
  refine ⟨x₀, x₀ ^ 2 * t₀, hx₀, by positivity, fun N hN γ hγ B1 B2 => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [eq15_scale N hN γ hγ x₀ t₀ hx₀ ht₀]
  by_cases hB : 0 < B1 ∧ 0 < B2
  · obtain ⟨h1, h2⟩ := hB
    have hx : 0 < B1 / (γ * N) := by positivity
    have ht : 0 < B2 / (N * B1 ^ 2) := by positivity
    have e1 : B1 = γ * N * (B1 / (γ * N)) := by field_simp
    have e2 : B2 = γ ^ 2 * (N : ℝ) ^ 3 * ((B1 / (γ * N)) ^ 2 * (B2 / (N * B1 ^ 2))) := by
      field_simp
    have key := eq15_scale N hN γ hγ _ _ hx ht
    rw [← e2, ← e1] at key
    rw [key]
    gcongr
    exact hmax _ _ hx ht
  · have : eq15Density N γ B1 B2 = 0 := by unfold eq15Density; rw [if_neg hB]
    rw [this]; positivity

open Arxivcond_mat_0004049 in
theorem solution :
    (∀ N : ℕ, 1 ≤ N → ∀ γ : ℝ, 0 < γ →
      ∫⁻ B : ℝ × ℝ, ENNReal.ofReal (B.1 * eq15Density N γ B.1 B.2) = ⊤ ∧
      ∫⁻ B : ℝ × ℝ, ENNReal.ofReal (B.2 * eq15Density N γ B.1 B.2) = ⊤) ∧
    ∃ b1 b2 : ℝ, 0 < b1 ∧ 0 < b2 ∧ ∀ N : ℕ, 1 ≤ N → ∀ γ : ℝ, 0 < γ → ∀ B1 B2 : ℝ,
      eq15Density N γ B1 B2 ≤ eq15Density N γ (γ * N * b1) (γ ^ 2 * (N : ℝ) ^ 3 * b2) :=
  ⟨M5Means.means, M5Mode.mode⟩

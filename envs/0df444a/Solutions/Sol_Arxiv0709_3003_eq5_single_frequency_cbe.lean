-- Prove2me | solution 1 for Arxiv0709_3003.eq5_single_frequency_cbe
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T18:31:26.987382+00:00
-- url     : https://prove2.me/submissions/b1093bbd-3b0e-4156-a3c5-bde9dd07f87e

import Definitions.Def_Arxiv0709_3003_Basic
import Theorems.Thm_Arxiv0709_3003_eq4_mode_expansion_as_proved

open MeasureTheory ProbabilityTheory Filter Topology Arxiv0709_3003

private lemma modeTerm_eq (s ρ : ℝ) (hs : 0 < s) (hρ : |ρ| ≤ s) :
    modeTerm s ρ = 3 * s ^ 2 * (s ^ 2 + 2 * ρ ^ 2) := by
  have : IsProbabilityMeasure (modeLaw s ρ) := by unfold modeLaw; infer_instance
  have h := eq4_mode_expansion_as_proved (modeLaw s ρ) 1 s ρ hs hρ
    (fun _ => id) (fun _ => HasLaw.id)
    (fun n m hnm => absurd (Subsingleton.elim n m) hnm)
  simpa [modeTerm] using h

private lemma abs_besselJ0_le_one (x : ℝ) : |besselJ0 x| ≤ 1 := by
  rw [besselJ0, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  have h1 : |∫ θ in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin θ)| ≤
      ∫ θ in (0 : ℝ)..Real.pi, |Real.cos (x * Real.sin θ)| :=
    intervalIntegral.abs_integral_le_integral_abs Real.pi_pos.le
  have h2 : ∫ θ in (0 : ℝ)..Real.pi, |Real.cos (x * Real.sin θ)| ≤
      ∫ _θ in (0 : ℝ)..Real.pi, (1 : ℝ) := by
    refine intervalIntegral.integral_mono_on Real.pi_pos.le ?_ intervalIntegrable_const ?_
    · exact (Continuous.abs (Real.continuous_cos.comp
        (continuous_const.mul Real.continuous_sin))).intervalIntegrable _ _
    · intro θ _
      exact Real.abs_cos_le_one _
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  calc (1 / Real.pi) * |∫ θ in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin θ)|
      ≤ (1 / Real.pi) * Real.pi := by gcongr; exact h1.trans h2
    _ = 1 := one_div_mul_cancel hpi.ne'

private lemma besselJ0_eq_half_interval (x : ℝ) :
    besselJ0 x = (2 / Real.pi) * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (x * Real.sin θ) := by
  rw [besselJ0]
  have hcont : Continuous (fun θ : ℝ => Real.cos (x * Real.sin θ)) :=
    Real.continuous_cos.comp (continuous_const.mul Real.continuous_sin)
  have hsplit : ∫ θ in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin θ) =
      (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (x * Real.sin θ)) +
      (∫ θ in (Real.pi / 2)..Real.pi, Real.cos (x * Real.sin θ)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hsym : ∫ θ in (Real.pi / 2)..Real.pi, Real.cos (x * Real.sin θ) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (x * Real.sin θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => Real.cos (x * Real.sin θ)) Real.pi (a := 0) (b := Real.pi / 2)
    have hsub : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
    rw [sub_zero, hsub] at h
    have hsin : (fun θ : ℝ => Real.cos (x * Real.sin (Real.pi - θ))) =
        fun θ => Real.cos (x * Real.sin θ) := by
      ext θ; rw [Real.sin_pi_sub]
    rw [hsin] at h
    exact h.symm
  rw [hsplit, hsym]
  ring

private lemma tendsto_half_besselJ0_atTop :
    Tendsto (fun x : ℝ => ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (x * Real.sin θ))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := min (ε / 2) (Real.pi / 4)
  have hδ_pos : 0 < δ := lt_min (half_pos hε) (by positivity)
  have hδ_le_eps : δ ≤ ε / 2 := min_le_left _ _
  have hδ_le_pi4 : δ ≤ Real.pi / 4 := min_le_right _ _
  have hδ_lt_pi2 : δ < Real.pi / 2 := lt_of_le_of_lt hδ_le_pi4 (by linarith [Real.pi_pos])
  set a : ℝ := Real.pi / 2 - δ
  have ha_pos : 0 < a := sub_pos.mpr hδ_lt_pi2
  have ha_le : a ≤ Real.pi / 2 := sub_le_self _ hδ_pos.le
  have hsin_pos : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ_pos (lt_trans hδ_lt_pi2 (by linarith [Real.pi_pos]))
  have hcos_ge : ∀ θ ∈ Set.Icc (0 : ℝ) a, Real.sin δ ≤ Real.cos θ := by
    intro θ hθ
    rw [← Real.cos_pi_div_two_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos]) hθ.2
  have hcos_pos : ∀ θ ∈ Set.Icc (0 : ℝ) a, 0 < Real.cos θ :=
    fun θ hθ => lt_of_lt_of_le hsin_pos (hcos_ge θ hθ)
  have hcos_ne : ∀ θ ∈ Set.uIcc (0 : ℝ) a, Real.cos θ ≠ 0 := by
    intro θ hθ
    rw [Set.uIcc_of_le ha_pos.le] at hθ
    exact (hcos_pos θ hθ).ne'
  refine ⟨max 1 (4 / (ε * Real.sin δ) + 1), fun x hx => ?_⟩
  have hx_pos : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hx)
  have hx_big : 4 / (ε * Real.sin δ) < x :=
    lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hx)
  rw [Real.dist_eq, sub_zero]
  have hcont : Continuous (fun θ : ℝ => Real.cos (x * Real.sin θ)) :=
    Real.continuous_cos.comp (continuous_const.mul Real.continuous_sin)
  have hsplit : ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (x * Real.sin θ) =
      (∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)) +
      (∫ θ in a..(Real.pi / 2), Real.cos (x * Real.sin θ)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have htail : |∫ θ in a..(Real.pi / 2), Real.cos (x * Real.sin θ)| ≤ δ := by
    have h1 : |∫ θ in a..(Real.pi / 2), Real.cos (x * Real.sin θ)| ≤
        ∫ θ in a..(Real.pi / 2), |Real.cos (x * Real.sin θ)| :=
      intervalIntegral.abs_integral_le_integral_abs ha_le
    have h2 : ∫ θ in a..(Real.pi / 2), |Real.cos (x * Real.sin θ)| ≤
        ∫ _θ in a..(Real.pi / 2), (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on ha_le
        ((Continuous.abs hcont).intervalIntegrable _ _) intervalIntegrable_const ?_
      intro θ _; exact Real.abs_cos_le_one _
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
    have hsub : Real.pi / 2 - a = δ := by dsimp [a]; ring
    linarith
  -- Integration by parts on [0, a]
  let u : ℝ → ℝ := fun θ => (Real.cos θ)⁻¹
  let u' : ℝ → ℝ := fun θ => Real.sin θ / (Real.cos θ) ^ 2
  let v : ℝ → ℝ := fun θ => Real.sin (x * Real.sin θ)
  let v' : ℝ → ℝ := fun θ => x * Real.cos θ * Real.cos (x * Real.sin θ)
  have hu : ∀ θ ∈ Set.uIcc (0 : ℝ) a, HasDerivAt u (u' θ) θ := by
    intro θ hθ
    have h : HasDerivAt u (-(-Real.sin θ) / Real.cos θ ^ 2) θ :=
      (Real.hasDerivAt_cos θ).inv (hcos_ne θ hθ)
    simpa [u', neg_neg] using h
  have hv : ∀ θ ∈ Set.uIcc (0 : ℝ) a, HasDerivAt v (v' θ) θ := by
    intro θ _
    have h := ((Real.hasDerivAt_sin θ).const_mul x).sin
    convert h using 1
    ring
  have hu'_cont : ContinuousOn u' (Set.uIcc (0 : ℝ) a) := by
    refine ContinuousOn.div Real.continuous_sin.continuousOn
      (Real.continuous_cos.pow 2).continuousOn ?_
    intro θ hθ
    exact pow_ne_zero 2 (hcos_ne θ hθ)
  have hv'_cont : ContinuousOn v' (Set.uIcc (0 : ℝ) a) :=
    ((continuous_const.mul Real.continuous_cos).mul hcont).continuousOn
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hu'_cont.intervalIntegrable) (hv'_cont.intervalIntegrable)
  have hmul : ∫ θ in (0 : ℝ)..a, u θ * v' θ =
      x * ∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    dsimp [u, v']
    have hne : Real.cos θ ≠ 0 := hcos_ne θ hθ
    field_simp [hne]
  have hsec_int : ∫ θ in (0 : ℝ)..a, u' θ = (Real.sin δ)⁻¹ - 1 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hu (hu'_cont.intervalIntegrable)
    rw [hftc]
    simp [u, a, Real.cos_pi_div_two_sub]
  have hibp_bound : |∫ θ in (0 : ℝ)..a, u' θ * v θ| ≤ (Real.sin δ)⁻¹ - 1 := by
    have h1 : |∫ θ in (0 : ℝ)..a, u' θ * v θ| ≤
        ∫ θ in (0 : ℝ)..a, |u' θ * v θ| :=
      intervalIntegral.abs_integral_le_integral_abs ha_pos.le
    have h2 : ∫ θ in (0 : ℝ)..a, |u' θ * v θ| ≤ ∫ θ in (0 : ℝ)..a, u' θ := by
      refine intervalIntegral.integral_mono_on ha_pos.le ?_
        (hu'_cont.intervalIntegrable) ?_
      · exact (hu'_cont.mul (Real.continuous_sin.comp
          (continuous_const.mul Real.continuous_sin)).continuousOn).abs.intervalIntegrable
      · intro θ hθ
        have hsin_nn : 0 ≤ Real.sin θ :=
          Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (le_trans hθ.2 (by linarith [Real.pi_pos]))
        have hu'_nn : 0 ≤ u' θ := div_nonneg hsin_nn (sq_nonneg _)
        rw [abs_mul, abs_of_nonneg hu'_nn]
        calc u' θ * |v θ| ≤ u' θ * 1 := by
              gcongr; exact Real.abs_sin_le_one _
          _ = u' θ := mul_one _
    linarith
  have hmain : |∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)| ≤ 2 / (x * Real.sin δ) := by
    have hxv : x * ∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ) =
        u a * v a - ∫ θ in (0 : ℝ)..a, u' θ * v θ := by
      rw [← hmul, hibp]
      simp [v]
    have hua : |u a * v a| ≤ (Real.sin δ)⁻¹ := by
      rw [abs_mul]
      have h1 : |u a| = (Real.sin δ)⁻¹ := by
        simp only [u, a, Real.cos_pi_div_two_sub, abs_inv, abs_of_pos hsin_pos]
      rw [h1]
      calc (Real.sin δ)⁻¹ * |v a| ≤ (Real.sin δ)⁻¹ * 1 := by
            gcongr; exact Real.abs_sin_le_one _
        _ = (Real.sin δ)⁻¹ := mul_one _
    have habs : x * |∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)| ≤ 2 * (Real.sin δ)⁻¹ := by
      calc x * |∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)|
          = |x| * |∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)| := by rw [abs_of_pos hx_pos]
        _ = |x * ∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)| := (abs_mul _ _).symm
        _ = |u a * v a - ∫ θ in (0 : ℝ)..a, u' θ * v θ| := by rw [hxv]
        _ ≤ |u a * v a| + |∫ θ in (0 : ℝ)..a, u' θ * v θ| := abs_sub _ _
        _ ≤ 2 * (Real.sin δ)⁻¹ := by linarith
    rw [le_div_iff₀ (mul_pos hx_pos hsin_pos)]
    have hmul' : |∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)| * (x * Real.sin δ) =
        (x * |∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)|) * Real.sin δ := by ring
    rw [hmul']
    calc (x * |∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)|) * Real.sin δ
        ≤ (2 * (Real.sin δ)⁻¹) * Real.sin δ := by gcongr
      _ = 2 := by field_simp [hsin_pos.ne']
  have hlt : 2 / (x * Real.sin δ) < ε / 2 := by
    rw [div_lt_iff₀ (mul_pos hx_pos hsin_pos)]
    have h4 : 4 < x * (ε * Real.sin δ) := (div_lt_iff₀ (mul_pos hε hsin_pos)).mp hx_big
    linarith
  rw [hsplit]
  calc |(∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)) +
        (∫ θ in a..(Real.pi / 2), Real.cos (x * Real.sin θ))|
      ≤ |∫ θ in (0 : ℝ)..a, Real.cos (x * Real.sin θ)| +
        |∫ θ in a..(Real.pi / 2), Real.cos (x * Real.sin θ)| := abs_add_le _ _
    _ ≤ 2 / (x * Real.sin δ) + δ := add_le_add hmain htail
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hlt hδ_le_eps
    _ = ε := add_halves ε

private lemma tendsto_besselJ0_atTop : Tendsto besselJ0 atTop (𝓝 0) := by
  have h := tendsto_half_besselJ0_atTop.const_mul (2 / Real.pi)
  rw [mul_zero] at h
  exact h.congr (fun x => (besselJ0_eq_half_interval x).symm)

theorem solution (N : ℕ) (hN : 0 < N) (s c f r : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hf : 0 < f) :
    Tendsto (fun r' => meanSqCorr N s c f r') atTop (𝓝 (3 * N * s ^ 4)) ∧
      cbeSpatial N s c f r = 1 + 2 * besselJ0 (2 * Real.pi * f * r / c) ^ 2 := by
  have hmean : ∀ r' : ℝ, meanSqCorr N s c f r' =
      3 * (N : ℝ) * s ^ 4 * (1 + 2 * besselJ0 (2 * Real.pi * f * r' / c) ^ 2) := by
    intro r'
    have hρ : |s * besselJ0 (2 * Real.pi * f * r' / c)| ≤ s := by
      rw [abs_mul, abs_of_pos hs]
      calc s * |besselJ0 (2 * Real.pi * f * r' / c)| ≤ s * 1 := by
            gcongr; exact abs_besselJ0_le_one _
        _ = s := mul_one s
    rw [meanSqCorr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      modeTerm_eq s _ hs hρ]
    ring
  have hlim : Tendsto (fun r' => meanSqCorr N s c f r') atTop (𝓝 (3 * N * s ^ 4)) := by
    have hk : 0 < 2 * Real.pi * f / c := by positivity
    have hlin : Tendsto (fun r' : ℝ => 2 * Real.pi * f * r' / c) atTop atTop := by
      have h1 : (fun r' : ℝ => 2 * Real.pi * f * r' / c) =
          fun r' => (2 * Real.pi * f / c) * r' := by ext r'; ring
      rw [h1]
      exact Filter.Tendsto.const_mul_atTop hk tendsto_id
    have hj0 : Tendsto (fun r' : ℝ => besselJ0 (2 * Real.pi * f * r' / c)) atTop (𝓝 0) :=
      tendsto_besselJ0_atTop.comp hlin
    have hpoly : Tendsto (fun r' : ℝ =>
        3 * (N : ℝ) * s ^ 4 * (1 + 2 * besselJ0 (2 * Real.pi * f * r' / c) ^ 2))
        atTop (𝓝 (3 * (N : ℝ) * s ^ 4 * (1 + 2 * (0 : ℝ) ^ 2))) := by
      exact ((hj0.pow 2).const_mul 2).const_add 1 |>.const_mul (3 * (N : ℝ) * s ^ 4)
    have hval : 3 * (N : ℝ) * s ^ 4 * (1 + 2 * (0 : ℝ) ^ 2) = 3 * (N : ℝ) * s ^ 4 := by ring
    rw [hval] at hpoly
    exact hpoly.congr (fun r' => (hmean r').symm)
  refine ⟨hlim, ?_⟩
  rw [cbeSpatial, hlim.limUnder_eq, hmean r]
  have hden : 3 * (N : ℝ) * s ^ 4 ≠ 0 := by positivity
  exact mul_div_cancel_left₀ _ hden

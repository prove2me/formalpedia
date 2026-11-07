-- Prove2me | solution 1 for AsyncSA.Contraction.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:27:42.852945+00:00
-- url     : https://prove2.me/submissions/854c8132-75b7-422d-b418-7f26a33dd759

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model

open MeasureTheory Filter Topology
open AsyncSA.Contraction

namespace AsyncSA.Contraction.Lem1Aux

lemma prod_le_exp (a : ℕ → ℝ) (ha : ∀ s, a s ∈ Set.Icc (0:ℝ) 1) (S : Finset ℕ) :
    ∏ s ∈ S, (1 - a s) ≤ Real.exp (-∑ s ∈ S, a s) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro s _; linarith [(ha s).2]
  · intro s _; have := Real.add_one_le_exp (-a s); linarith

lemma eventually_prod_small (a : ℕ → ℝ) (ha : ∀ s, a s ∈ Set.Icc (0:ℝ) 1)
    (hdiv : Tendsto (fun T => ∑ t ∈ Finset.range T, a t) atTop atTop) (t0 : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, ∏ s ∈ Finset.Ico t0 t, (1 - a s) < η := by
  have h1 : Tendsto (fun t => ∑ s ∈ Finset.Ico t0 t, a s) atTop atTop := by
    have := tendsto_atTop_add_const_right _ (-(∑ t ∈ Finset.range t0, a t)) hdiv
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop t0] with t ht
    rw [Finset.sum_Ico_eq_sub _ ht, sub_eq_add_neg]
  have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).eventually (gt_mem_nhds hη)
  filter_upwards [h2] with t ht
  exact lt_of_le_of_lt (prod_le_exp a ha _) ht

/-- Deterministic averaging: `U(t+1) = (1-a)U(t) + a e(t)` with `e → 0`, `Σ a = ∞`. -/
lemma det_conv (a e U : ℕ → ℝ) (ha : ∀ t, a t ∈ Set.Icc (0:ℝ) 1)
    (hdiv : Tendsto (fun T => ∑ t ∈ Finset.range T, a t) atTop atTop)
    (he : Tendsto e atTop (𝓝 0))
    (hU : ∀ t, U (t + 1) = (1 - a t) * U t + a t * e t) :
    Tendsto U atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.1 he (ε / 2) (by positivity)
  set V : ℕ → ℝ := fun t => max (|U t| - ε / 2) 0 with hV
  have hstep : ∀ t ≥ T, V (t + 1) ≤ (1 - a t) * V t := by
    intro t ht
    have het : |e t| < ε / 2 := by simpa [Real.dist_eq] using hT t ht
    have h0 : 0 ≤ 1 - a t := by linarith [(ha t).2]
    have ha0 : 0 ≤ a t := (ha t).1
    have hU1 : |U (t + 1)| ≤ (1 - a t) * |U t| + a t * (ε / 2) := by
      rw [hU t]
      calc |(1 - a t) * U t + a t * e t| ≤ |(1 - a t) * U t| + |a t * e t| := abs_add_le _ _
        _ = (1 - a t) * |U t| + a t * |e t| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg ha0]
        _ ≤ _ := by gcongr
    have hVt : |U t| - ε / 2 ≤ V t := le_max_left _ _
    have hV0 : 0 ≤ V t := le_max_right _ _
    apply max_le
    · nlinarith
    · exact mul_nonneg h0 hV0
  have hiter : ∀ k, V (T + k) ≤ (∏ s ∈ Finset.Ico T (T + k), (1 - a s)) * V T := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, Finset.prod_Ico_succ_top (Nat.le_add_right T k)]
      calc V (T + k + 1) ≤ (1 - a (T + k)) * V (T + k) := hstep _ (Nat.le_add_right T k)
        _ ≤ (1 - a (T + k)) * ((∏ s ∈ Finset.Ico T (T + k), (1 - a s)) * V T) := by
          gcongr
          linarith [(ha (T + k)).2]
        _ = _ := by ring
  have hVT : 0 ≤ V T := le_max_right _ _
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 ((eventually_prod_small a ha hdiv T
    (η := ε / 4 / (V T + 1)) (by positivity)).and (eventually_ge_atTop T))
  refine ⟨T₁, fun t ht => ?_⟩
  obtain ⟨hp, htT⟩ := hT₁ t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htT
  have h1 := hiter k
  have hp0 : 0 ≤ ∏ s ∈ Finset.Ico T (T + k), (1 - a s) :=
    Finset.prod_nonneg fun s _ => by linarith [(ha s).2]
  have h2 : (∏ s ∈ Finset.Ico T (T + k), (1 - a s)) * V T ≤ ε / 4 / (V T + 1) * (V T + 1) := by
    calc _ ≤ (∏ s ∈ Finset.Ico T (T + k), (1 - a s)) * (V T + 1) := by gcongr; linarith
      _ ≤ _ := by gcongr
  rw [div_mul_cancel₀ _ (by linarith)] at h2
  have h3 : |U (T + k)| - ε / 2 ≤ V (T + k) := le_max_left _ _
  rw [Real.dist_eq, sub_zero]
  linarith

/-- Weighted form of the conditional second-moment bound. -/
lemma wsq {Ω : Type*} (m : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω] (hm : m ≤ m₀)
    (P : Measure Ω) (f h : Ω → ℝ) (hf : Measurable f) (hh : Measurable h)
    (H : ∀ S, MeasurableSet[m] S →
      ∫⁻ ω in S, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ∫⁻ ω in S, ENNReal.ofReal (h ω) ∂P)
    (g : Ω → ENNReal) (hg : Measurable[m] g) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) * g ω ∂P ≤ ∫⁻ ω, ENNReal.ofReal (h ω) * g ω ∂P := by
  have m1 : Measurable fun ω => ENNReal.ofReal (f ω ^ 2) := (hf.pow_const 2).ennreal_ofReal
  have m2 : Measurable fun ω => ENNReal.ofReal (h ω) := hh.ennreal_ofReal
  have hle : (P.withDensity fun ω => ENNReal.ofReal (f ω ^ 2)).trim hm ≤
      (P.withDensity fun ω => ENNReal.ofReal (h ω)).trim hm := by
    refine Measure.le_intro fun S hS _ => ?_
    rw [trim_measurableSet_eq hm hS, trim_measurableSet_eq hm hS,
      withDensity_apply _ (hm _ hS), withDensity_apply _ (hm _ hS)]
    exact H S hS
  have := lintegral_mono' hle (le_refl g)
  rw [lintegral_trim hm hg, lintegral_trim hm hg,
    lintegral_withDensity_eq_lintegral_mul _ m1 (hg.mono hm le_rfl),
    lintegral_withDensity_eq_lintegral_mul _ m2 (hg.mono hm le_rfl)] at this
  simpa [Pi.mul_apply] using this


/-- An `L²`-bounded sum of martingale differences converges almost surely. -/
lemma mart_conv {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m₀) (d : ℕ → Ω → ℝ)
    (hdm : ∀ s, StronglyMeasurable[𝓕 (s + 1)] (d s))
    (hdL : ∀ s, MemLp (d s) 2 P)
    (hdc : ∀ s, P[d s | 𝓕 s] =ᵐ[P] 0)
    (R : ℝ) (hR : ∀ t, ∑ s ∈ Finset.range t, ∫ ω, d s ω ^ 2 ∂P ≤ R) :
    ∀ᵐ ω ∂P, ∃ L : ℝ, Tendsto (fun t => ∑ s ∈ Finset.range t, d s ω) atTop (𝓝 L) := by
  set M : ℕ → Ω → ℝ := fun t ω => ∑ s ∈ Finset.range t, d s ω with hM
  have hML : ∀ t, MemLp (M t) 2 P := fun t =>
    memLp_finsetSum (Finset.range t) fun s _ => hdL s
  have hMm : ∀ t, StronglyMeasurable[𝓕 t] (M t) := by
    intro t
    refine Finset.stronglyMeasurable_fun_sum (f := d) (Finset.range t) fun s hs => ?_
    exact (hdm s).mono (𝓕.mono (Finset.mem_range.1 hs))
  have hdiff : ∀ t, M (t + 1) - M t = d t := by
    intro t; funext ω; simp [hM, Finset.sum_range_succ]
  have hmart : Martingale M 𝓕 P := by
    refine martingale_of_condExp_sub_eq_zero_nat (fun t => hMm t)
      (fun t => (hML t).integrable one_le_two) fun t => ?_
    rw [hdiff t]; exact hdc t
  have hcross : ∀ t, ∫ ω, M t ω * d t ω ∂P = 0 := by
    intro t
    have hint : Integrable (M t * d t) P := (hML t).integrable_mul (hdL t)
    rw [← integral_condExp (𝓕.le t)]
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 t) (μ := P) (hMm t) hint
      ((hdL t).integrable one_le_two)
    have h2 : (M t * P[d t | 𝓕 t]) =ᵐ[P] 0 := by
      filter_upwards [hdc t] with ω hω
      simp [hω]
    calc ∫ ω, (P[M t * d t | 𝓕 t]) ω ∂P = ∫ ω, (0 : Ω → ℝ) ω ∂P :=
          integral_congr_ae (h1.trans h2)
      _ = 0 := by simp
  have hsq : ∀ t, ∫ ω, M t ω ^ 2 ∂P = ∑ s ∈ Finset.range t, ∫ ω, d s ω ^ 2 ∂P := by
    intro t
    induction t with
    | zero => simp [hM]
    | succ t ih =>
      have e : ∀ ω, M (t + 1) ω ^ 2 = M t ω ^ 2 + 2 * (M t ω * d t ω) + d t ω ^ 2 := by
        intro ω; simp only [hM, Finset.sum_range_succ]; ring
      simp_rw [e]
      have i1 := (hML t).integrable_sq
      have i2 : Integrable (fun ω => 2 * (M t ω * d t ω)) P :=
        ((hML t).integrable_mul (hdL t)).const_mul 2
      have i3 := (hdL t).integrable_sq
      have i12 : Integrable (fun ω => M t ω ^ 2 + 2 * (M t ω * d t ω)) P := i1.add i2
      rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, hcross t, ih,
        Finset.sum_range_succ]
      ring
  have hbdd : ∀ t, eLpNorm (M t) 1 P ≤ (((R + 1) / 2).toNNReal : ENNReal) := by
    intro t
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hi : Integrable (fun ω => (M t ω ^ 2 + 1) / 2) P :=
      ((hML t).integrable_sq.add (integrable_const 1)).div_const 2
    calc ∫⁻ ω, ‖M t ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal ((M t ω ^ 2 + 1) / 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [sq_nonneg (|M t ω| - 1), sq_abs (M t ω)]
      _ = ENNReal.ofReal (∫ ω, (M t ω ^ 2 + 1) / 2 ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hi
            (ae_of_all _ fun ω => by positivity)).symm
      _ ≤ ENNReal.ofReal ((R + 1) / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_div, integral_add (hML t).integrable_sq (integrable_const 1), hsq t]
          simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
          linarith [hR t]
      _ = _ := rfl
  filter_upwards [hmart.submartingale.ae_tendsto_limitProcess hbdd] with ω hω
  exact ⟨_, hω⟩

end AsyncSA.Contraction.Lem1Aux

open AsyncSA.Contraction.Lem1Aux in
theorem solution {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m₀) (α w B W : ℕ → Ω → ℝ) (C : ℝ)
    (hαmeas : ∀ t, Measurable[𝓕 t] (α t))
    (hwmeas : ∀ t, Measurable[𝓕 (t + 1)] (w t))
    (hBmeas : ∀ t, Measurable[𝓕 t] (B t))
    (hmean : ∀ t, CondMeanZero m₀ (𝓕 t) P (w t))
    (hsq : ∀ t, CondSqLe m₀ (𝓕 t) P (w t) (B t))
    (hαmem : ∀ᵐ ω ∂P, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hdiv : ∀ᵐ ω ∂P,
      Tendsto (fun T => ∑ t ∈ Finset.range T, α t ω) atTop atTop)
    (hsum : ∀ᵐ ω ∂P,
      ∀ T, ∑ t ∈ Finset.range T, α t ω ^ 2 ≤ C)
    (hBbound : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ t, |B t ω| ≤ K)
    (hW : ∀ t ω, W (t + 1) ω =
      (1 - α t ω) * W t ω + α t ω * w t ω) :
    ∀ᵐ ω ∂P, Tendsto (fun t => W t ω) atTop (𝓝 0) := by
  classical
  -- clipping of the step sizes to `[0,1]` (harmless: they lie there almost surely)
  set clip : ℝ → ℝ := fun x => max 0 (min x 1) with hclip
  have clip_abs : ∀ x, |clip x| ≤ 1 := by
    intro x
    have h0 : 0 ≤ clip x := le_max_left _ _
    have h1 : clip x ≤ 1 := max_le zero_le_one (min_le_right _ _)
    rw [abs_of_nonneg h0]; exact h1
  have clip_eq : ∀ x ∈ Set.Icc (0:ℝ) 1, clip x = x := fun x hx => by
    simp only [hclip, min_eq_left hx.2, max_eq_right hx.1]
  have clip_cont : Continuous clip := continuous_const.max (continuous_id.min continuous_const)
  have hαm' : ∀ s, Measurable[𝓕 s] (fun ω => clip (α s ω)) :=
    fun s => clip_cont.measurable.comp (hαmeas s)
  -- truncation events `A K t = {|B r| ≤ K for all r ≤ t}`
  let A : ℕ → ℕ → Set Ω := fun K t => {ω | ∀ r ∈ Finset.range (t + 1), |B r ω| ≤ K}
  have hA : ∀ K t, MeasurableSet[𝓕 t] (A K t) := by
    intro K t
    have e : A K t = ⋂ r ∈ Finset.range (t + 1), {ω | |B r ω| ≤ (K : ℝ)} := by
      ext ω; simp [A]
    rw [e]
    refine Finset.measurableSet_biInter _ fun r hr => ?_
    have hBr : Measurable[𝓕 t] (B r) :=
      (hBmeas r).mono (𝓕.mono (Nat.lt_succ_iff.mp (Finset.mem_range.1 hr))) le_rfl
    exact measurableSet_le (continuous_abs.measurable.comp hBr) measurable_const
  -- weighted second-moment bound for truncated noise
  have key : ∀ (K s : ℕ) (c : Ω → ℝ), Measurable[𝓕 s] c →
      ∫⁻ ω, ENNReal.ofReal ((c ω * (A K s).indicator (w s) ω) ^ 2) ∂P ≤
        ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (c ω ^ 2) ∂P := by
    intro K s c hc
    obtain ⟨_, hle⟩ := hsq s
    have hg : Measurable[𝓕 s]
        (fun ω => ENNReal.ofReal ((A K s).indicator (fun ω => c ω ^ 2) ω)) :=
      ((hc.pow_const 2).indicator (hA K s)).ennreal_ofReal
    have hw0 : Measurable (w s) := (hwmeas s).mono (𝓕.le (s + 1)) le_rfl
    have hB0 : Measurable (B s) := (hBmeas s).mono (𝓕.le s) le_rfl
    have h := wsq (𝓕 s) (𝓕.le s) P (w s) (B s) hw0 hB0 hle _ hg
    calc ∫⁻ ω, ENNReal.ofReal ((c ω * (A K s).indicator (w s) ω) ^ 2) ∂P
        = ∫⁻ ω, ENNReal.ofReal (w s ω ^ 2) *
            ENNReal.ofReal ((A K s).indicator (fun ω => c ω ^ 2) ω) ∂P := by
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ A K s
          · simp only [Set.indicator_of_mem hω]
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; ring
          · simp [Set.indicator_of_notMem hω]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (B s ω) *
            ENNReal.ofReal ((A K s).indicator (fun ω => c ω ^ 2) ω) ∂P := h
      _ ≤ ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal (c ω ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ A K s
          · simp only [Set.indicator_of_mem hω]
            gcongr
            exact le_trans (le_abs_self _) (hω s (Finset.self_mem_range_succ s))
          · simp [Set.indicator_of_notMem hω]
      _ = _ := lintegral_const_mul _ ((hc.mono (𝓕.le s) le_rfl).pow_const 2).ennreal_ofReal
  have memL : ∀ (K s : ℕ) (c : Ω → ℝ), Measurable[𝓕 s] c → (∀ ω, |c ω| ≤ 1) →
      MemLp (fun ω => c ω * (A K s).indicator (w s) ω) 2 P := by
    intro K s c hc hc1
    have hmeas : Measurable (fun ω => c ω * (A K s).indicator (w s) ω) :=
      (hc.mono (𝓕.le s) le_rfl).mul
        (((hwmeas s).mono (𝓕.le _) le_rfl).indicator ((𝓕.le s) _ (hA K s)))
    rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
    refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg _)]
    refine lt_of_le_of_lt (key K s c hc) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    refine lt_of_le_of_lt (lintegral_mono (g := fun _ => 1) fun ω => ?_) (by simp)
    have := abs_le.1 (hc1 ω)
    exact ENNReal.ofReal_le_one.2 (by nlinarith)
  have hu : ∀ K s, Integrable ((A K s).indicator (w s)) P := by
    intro K s
    have := (memL K s (fun _ => 1) measurable_const (fun _ => by simp)).integrable one_le_two
    simpa using this
  have hu_ce : ∀ K s, P[(A K s).indicator (w s) | 𝓕 s] =ᵐ[P] 0 := by
    intro K s
    refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hu K s)
      (fun S _ _ => integrableOn_zero) (fun S hS _ => ?_)
      stronglyMeasurable_zero.aestronglyMeasurable).symm
    rw [setIntegral_indicator ((𝓕.le s) _ (hA K s))]
    simp only [integral_zero]
    symm
    apply hmean s (S ∩ A K s) (hS.inter (hA K s))
    calc ∫⁻ ω in S ∩ A K s, ‖w s ω‖ₑ ∂P
        = ∫⁻ ω in S ∩ A K s, ‖(A K s).indicator (w s) ω‖ₑ ∂P := by
          refine setLIntegral_congr_fun ((𝓕.le s) _ (hS.inter (hA K s))) fun ω hω => ?_
          rw [Set.indicator_of_mem hω.2]
      _ ≤ ∫⁻ ω, ‖(A K s).indicator (w s) ω‖ₑ ∂P := setLIntegral_le_lintegral _ _
      _ < ⊤ := (hu K s).2
  -- the truncated martingale differences
  let d : ℕ → ℕ → Ω → ℝ := fun K s ω => clip (α s ω) * (A K s).indicator (w s) ω
  have hdL : ∀ K s, MemLp (d K s) 2 P := fun K s => memL K s _ (hαm' s) (fun ω => clip_abs _)
  have hdm : ∀ K s, StronglyMeasurable[𝓕 (s + 1)] (d K s) := by
    intro K s
    exact (((hαm' s).mono (𝓕.mono (Nat.le_succ s)) le_rfl).mul
      ((hwmeas s).indicator ((𝓕.mono (Nat.le_succ s)) _ (hA K s)))).stronglyMeasurable
  have hd_ce : ∀ K s, P[d K s | 𝓕 s] =ᵐ[P] 0 := by
    intro K s
    have e : d K s = (fun ω => clip (α s ω)) * (A K s).indicator (w s) := rfl
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 s) (μ := P)
      (hαm' s).stronglyMeasurable (by rw [← e]; exact (hdL K s).integrable one_le_two) (hu K s)
    rw [e]
    filter_upwards [h1, hu_ce K s] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    simp
  have hclipint : ∀ s, Integrable (fun ω => clip (α s ω) ^ 2) P := by
    intro s
    refine Integrable.mono' (integrable_const 1)
      (((hαm' s).mono (𝓕.le s) le_rfl).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have := abs_le.1 (clip_abs (α s ω))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hd2 : ∀ K s, ∫ ω, d K s ω ^ 2 ∂P ≤ K * ∫ ω, clip (α s ω) ^ 2 ∂P := by
    intro K s
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    have i1 := (hdL K s).integrable_sq
    rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (integral_nonneg fun ω => sq_nonneg _)),
      ofReal_integral_eq_lintegral_ofReal i1 (ae_of_all _ fun ω => sq_nonneg _),
      ENNReal.ofReal_mul hK,
      ofReal_integral_eq_lintegral_ofReal (hclipint s) (ae_of_all _ fun ω => sq_nonneg _)]
    exact key K s _ (hαm' s)
  have hR : ∀ K t, ∑ s ∈ Finset.range t, ∫ ω, d K s ω ^ 2 ∂P ≤ K * C := by
    intro K t
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    calc ∑ s ∈ Finset.range t, ∫ ω, d K s ω ^ 2 ∂P
        ≤ ∑ s ∈ Finset.range t, K * ∫ ω, clip (α s ω) ^ 2 ∂P :=
          Finset.sum_le_sum fun s _ => hd2 K s
      _ = K * ∫ ω, ∑ s ∈ Finset.range t, clip (α s ω) ^ 2 ∂P := by
          rw [← Finset.mul_sum, integral_finsetSum _ fun s _ => hclipint s]
      _ ≤ K * ∫ ω, C ∂P := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          refine integral_mono_ae (integrable_finsetSum _ fun s _ => hclipint s)
            (integrable_const C) ?_
          filter_upwards [hαmem, hsum] with ω h1 h2
          calc ∑ s ∈ Finset.range t, clip (α s ω) ^ 2
              = ∑ s ∈ Finset.range t, α s ω ^ 2 :=
                Finset.sum_congr rfl fun s _ => by rw [clip_eq _ (h1 s)]
            _ ≤ C := h2 t
      _ = K * C := by simp
  have hconv : ∀ K : ℕ, ∀ᵐ ω ∂P, ∃ L : ℝ,
      Tendsto (fun t => ∑ s ∈ Finset.range t, d K s ω) atTop (𝓝 L) :=
    fun K => mart_conv P 𝓕 (d K) (hdm K) (hdL K) (hd_ce K) (K * C) (hR K)
  filter_upwards [ae_all_iff.2 hconv, hαmem, hdiv, hBbound] with ω hc hα hd hB
  obtain ⟨K0, hK0⟩ := hB
  set K := ⌈K0⌉₊
  obtain ⟨L, hL⟩ := hc K
  have hdω : ∀ s, d K s ω = α s ω * w s ω := by
    intro s
    have hmem : ω ∈ A K s := fun r _ => le_trans (hK0 r) (Nat.le_ceil K0)
    simp only [d, Set.indicator_of_mem hmem, clip_eq _ (hα s)]
  set Mω : ℕ → ℝ := fun t => ∑ s ∈ Finset.range t, α s ω * w s ω with hMω
  have hML : Tendsto Mω atTop (𝓝 L) := by
    refine hL.congr fun t => ?_
    simp only [hMω, hdω]
  have he : Tendsto (fun t => L - Mω t) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := L)).sub hML
    simpa using this
  have hU := det_conv (fun t => α t ω) (fun t => L - Mω t) (fun t => W t ω - Mω t + L) hα hd he
    (fun t => by
      simp only [hMω, Finset.sum_range_succ, hW t ω]
      ring)
  have := hU.add ((hML.sub (tendsto_const_nhds (x := L))))
  simp only [sub_self, add_zero] at this
  refine this.congr fun t => ?_
  ring

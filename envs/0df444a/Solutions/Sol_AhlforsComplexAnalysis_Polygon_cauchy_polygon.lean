-- Prove2me | solution 1 for AhlforsComplexAnalysis.Polygon.cauchy_polygon
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:37:20.689156+00:00
-- url     : https://prove2.me/submissions/195c85a4-decd-4e56-9f69-07493e55c6c8

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_windInt_locallyConstant
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_windInt_tendsto_zero

set_option autoImplicit false

/-!
# Cauchy's theorem for polygons (Dixon's proof)

Helpers live in `AhlforsComplexAnalysis.Polygon.Dixon`.
-/

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

namespace Dixon

open Metric
open scoped Interval

lemma lineMap_mem_segment {a b : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    a + (t : ℂ) * (b - a) ∈ segment ℝ a b := by
  rw [segment_eq_image']
  exact ⟨t, ht, by simp [Complex.real_smul]⟩

lemma segInt_congr {g g' : ℂ → ℂ} {a b : ℂ} (h : ∀ w ∈ segment ℝ a b, g w = g' w) :
    segInt g a b = segInt g' a b := by
  unfold segInt
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only [h _ (lineMap_mem_segment ht)]

lemma polyInt_congr {g g' : ℂ → ℂ} :
    ∀ {l : List ℂ}, (∀ w ∈ polyTrace l, g w = g' w) → polyInt g l = polyInt g' l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    simp only [polyInt]
    rw [segInt_congr (fun w hw => h w (Or.inl hw)),
      polyInt_congr (fun w hw => h w (Or.inr hw))]

lemma segInt_integrand_intervalIntegrable {k : ℂ → ℂ} {a b : ℂ}
    (hk : ContinuousOn k (segment ℝ a b)) :
    IntervalIntegrable (fun t : ℝ => k (a + (t : ℂ) * (b - a)) * (b - a)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  refine ContinuousOn.mul (hk.comp (by fun_prop) (fun t ht => lineMap_mem_segment ht))
    continuousOn_const

lemma segInt_sub {g g' : ℂ → ℂ} {a b : ℂ} (hg : ContinuousOn g (segment ℝ a b))
    (hg' : ContinuousOn g' (segment ℝ a b)) :
    segInt (fun w => g w - g' w) a b = segInt g a b - segInt g' a b := by
  unfold segInt
  rw [← intervalIntegral.integral_sub (segInt_integrand_intervalIntegrable hg)
    (segInt_integrand_intervalIntegrable hg')]
  congr 1
  ext t
  ring

lemma polyInt_sub {g g' : ℂ → ℂ} :
    ∀ {l : List ℂ}, ContinuousOn g (polyTrace l) → ContinuousOn g' (polyTrace l) →
      polyInt (fun w => g w - g' w) l = polyInt g l - polyInt g' l
  | [], _, _ => by simp [polyInt]
  | [_], _, _ => by simp [polyInt]
  | a :: b :: rest, hg, hg' => by
    simp only [polyInt]
    rw [segInt_sub (hg.mono fun _ h => Or.inl h) (hg'.mono fun _ h => Or.inl h),
      polyInt_sub (hg.mono fun _ h => Or.inr h) (hg'.mono fun _ h => Or.inr h)]
    ring

lemma segInt_const_mul (c : ℂ) (g : ℂ → ℂ) (a b : ℂ) :
    segInt (fun w => c * g w) a b = c * segInt g a b := by
  simp only [segInt, mul_assoc, intervalIntegral.integral_const_mul]

lemma polyInt_const_mul (c : ℂ) (g : ℂ → ℂ) :
    ∀ l : List ℂ, polyInt (fun w => c * g w) l = c * polyInt g l
  | [] => by simp [polyInt]
  | [_] => by simp [polyInt]
  | a :: b :: rest => by
    simp only [polyInt]
    rw [segInt_const_mul, polyInt_const_mul c g (b :: rest), mul_add]

/-- Length of the polygonal path. -/
noncomputable def polyLength : List ℂ → ℝ
  | a :: b :: rest => ‖b - a‖ + polyLength (b :: rest)
  | _ => 0

lemma polyLength_nonneg : ∀ l : List ℂ, 0 ≤ polyLength l
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: rest => by
    simp only [polyLength]
    have := polyLength_nonneg (b :: rest)
    positivity

lemma norm_segInt_le {g : ℂ → ℂ} {a b : ℂ} {M : ℝ} (h : ∀ w ∈ segment ℝ a b, ‖g w‖ ≤ M) :
    ‖segInt g a b‖ ≤ M * ‖b - a‖ := by
  unfold segInt
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := M * ‖b - a‖) (f := fun t : ℝ => g (a + (t : ℂ) * (b - a)) * (b - a)) (fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (h _ (lineMap_mem_segment ⟨ht.1.le, ht.2⟩)) (norm_nonneg _))
  simpa using this

lemma norm_polyInt_le {g : ℂ → ℂ} {M : ℝ} :
    ∀ {l : List ℂ}, (∀ w ∈ polyTrace l, ‖g w‖ ≤ M) → ‖polyInt g l‖ ≤ M * polyLength l
  | [], _ => by simp [polyInt, polyLength]
  | [_], _ => by simp [polyInt, polyLength]
  | a :: b :: rest, h => by
    simp only [polyInt, polyLength]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_segInt_le (fun w hw => h w (Or.inl hw))
    have h2 := norm_polyInt_le (fun w hw => h w (Or.inr hw))
    nlinarith

/-! ### Differentiation under the integral sign -/

lemma differentiableOn_intervalIntegral_param {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℝ → ℂ}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => F z t) U)
    (hc : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2) (U ×ˢ Icc (0 : ℝ) 1)) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, F z t) U := by
  intro z₀ hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set r : ℝ := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsub : closedBall z₀ (2 * r) ⊆ U := by
    intro z hz
    apply hball
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.1 hz
    linarith
  obtain ⟨M, hM⟩ := ((isCompact_closedBall z₀ (2 * r)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    (hc.mono (prod_mono hsub subset_rfl))
  have hmemIcc : ∀ t ∈ Ι (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => by
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  have hFt : ∀ x ∈ U, ContinuousOn (F x) (Icc (0 : ℝ) 1) := fun x hx =>
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hx, ht⟩)
  have hcauchy : ∀ z ∈ ball z₀ r, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (fun w => F w t) z‖ ≤ M / r := by
    intro z hz t ht
    have hz' : dist z z₀ < r := Metric.mem_ball.1 hz
    have hcb : closedBall z r ⊆ closedBall z₀ (2 * r) := by
      intro w hw
      rw [Metric.mem_closedBall] at hw ⊢
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ 2 * r := by linarith
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      ((hd t ht).diffContOnCl_ball (hcb.trans hsub)) fun w hw => ?_
    exact hM (w, t) ⟨hcb (Metric.sphere_subset_closedBall hw), ht⟩
  have hdiffAt : ∀ x ∈ ball z₀ r, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun x => F x t) (deriv (fun w => F w t) x) x := by
    intro x hx t ht
    have hxU : x ∈ U := hsub (by
      have : dist x z₀ < r := Metric.mem_ball.1 hx
      rw [Metric.mem_closedBall]; linarith)
    exact ((hd t ht).differentiableAt (hU.mem_nhds hxU)).hasDerivAt
  have hF'meas : MeasureTheory.AEStronglyMeasurable (fun t => deriv (fun z => F z t) z₀)
      (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) := by
    set δ : ℕ → ℂ := fun n => (((r / 2) / ((n : ℝ) + 1) : ℝ) : ℂ) with hδdef
    have hδ0 : ∀ n, δ n ≠ 0 := fun n => by
      simp only [hδdef, ne_eq, Complex.ofReal_eq_zero]
      positivity
    have hδball : ∀ n, z₀ + δ n ∈ ball z₀ r := fun n => by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hδdef, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (r / 2) / ((n : ℝ) + 1) ≤ r / 2 := div_le_self (by positivity) (by simp)
        _ < r := by linarith
    have hδlim : Tendsto δ atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hδ0⟩
      have h1 : Tendsto δ atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
      rwa [Complex.ofReal_zero] at h1
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t => (δ n)⁻¹ • (F (z₀ + δ n) t - F z₀ t)) (fun n => ?_) ?_
    · have hz1 : z₀ + δ n ∈ U := hsub (by
        have : dist (z₀ + δ n) z₀ < r := Metric.mem_ball.1 (hδball n)
        rw [Metric.mem_closedBall]; linarith)
      have hc1 : ContinuousOn (fun t => (δ n)⁻¹ • (F (z₀ + δ n) t - F z₀ t)) (Icc (0 : ℝ) 1) :=
        by
          have h1 := hFt _ hz1
          have h2 := hFt z₀ hz₀
          fun_prop
      exact (hc1.mono hmemIcc).aestronglyMeasurable measurableSet_uIoc
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      refine Eventually.of_forall fun t ht => ?_
      have hder := hdiffAt z₀ (mem_ball_self hr0) t (hmemIcc t ht)
      exact hder.tendsto_slope_zero.comp hδlim |>.congr' (Eventually.of_forall fun n => rfl)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 1) (bound := fun _ => M / r) (F := F)
    (F' := fun z t => deriv (fun w => F w t) z) (x₀ := z₀) (s := ball z₀ r)
    (ball_mem_nhds z₀ hr0) ?_ ?_ hF'meas ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ball_mem_nhds z₀ hr0] with x hx
    have hxU : x ∈ U := hsub (by
      have : dist x z₀ < r := Metric.mem_ball.1 hx
      rw [Metric.mem_closedBall]; linarith)
    exact ((hFt x hxU).mono (fun t ht => hmemIcc t ht)).aestronglyMeasurable measurableSet_uIoc
  · exact (hFt z₀ hz₀).intervalIntegrable_of_Icc zero_le_one
  · exact Eventually.of_forall fun t ht z hz => hcauchy z hz t (hmemIcc t ht)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht z hz => hdiffAt z hz t (hmemIcc t ht)

/-- A parameter integral over a polygon is differentiable when the integrand is holomorphic in the
parameter and jointly continuous on the parameter set times the trace. -/
lemma differentiableOn_polyInt_param {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ → ℂ} :
    ∀ {l : List ℂ}, (∀ w ∈ polyTrace l, DifferentiableOn ℂ (fun z => g z w) U) →
      ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (U ×ˢ polyTrace l) →
      DifferentiableOn ℂ (fun z => polyInt (g z) l) U
  | [], _, _ => by simp only [polyInt]; exact differentiableOn_const _
  | [_], _, _ => by simp only [polyInt]; exact differentiableOn_const _
  | a :: b :: rest, hd, hc => by
    simp only [polyInt]
    refine DifferentiableOn.add ?_ (differentiableOn_polyInt_param hU
      (fun w hw => hd w (Or.inr hw)) (hc.mono (prod_mono subset_rfl fun _ h => Or.inr h)))
    have := differentiableOn_intervalIntegral_param hU
      (F := fun z t => g z (a + (t : ℂ) * (b - a)) * (b - a))
      (fun t ht => (hd _ (Or.inl (lineMap_mem_segment ht))).mul_const _) (by
        refine ContinuousOn.mul ?_ continuousOn_const
        refine hc.comp (continuous_fst.prodMk
          (by fun_prop : Continuous fun p : ℂ × ℝ => a + (p.2 : ℂ) * (b - a))).continuousOn ?_
        rintro ⟨z, t⟩ ⟨hz, ht⟩
        exact ⟨hz, Or.inl (lineMap_mem_segment ht)⟩)
    exact this

/-! ### Joint continuity of the difference quotient -/

lemma continuousOn_dslope_uncurry {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (Ω ×ˢ Ω) := by
  rintro ⟨w₀, z₀⟩ ⟨hw₀, hz₀⟩
  refine ContinuousAt.continuousWithinAt ?_
  by_cases hne : w₀ = z₀
  · subst hne
    rw [Metric.continuousAt_iff']
    intro ε hε
    have hder : ContinuousOn (deriv f) Ω := (hf.analyticOnNhd hΩ).deriv.continuousOn
    obtain ⟨ρ, hρ, hρΩ, hρε⟩ : ∃ ρ > 0, ball w₀ ρ ⊆ Ω ∧
        ∀ x ∈ ball w₀ ρ, ‖deriv f x - deriv f w₀‖ < ε / 2 := by
      obtain ⟨ρ₁, h₁, h₁Ω⟩ := Metric.isOpen_iff.1 hΩ w₀ hw₀
      obtain ⟨ρ₂, h₂, h₂ε⟩ := Metric.continuousAt_iff.1
        (hder.continuousAt (hΩ.mem_nhds hw₀)) (ε / 2) (by positivity)
      refine ⟨min ρ₁ ρ₂, lt_min h₁ h₂, (ball_subset_ball (min_le_left _ _)).trans h₁Ω, ?_⟩
      intro x hx
      have := h₂ε (ball_subset_ball (min_le_right _ _) hx)
      rwa [dist_eq_norm] at this
    have hnhds : ball w₀ ρ ×ˢ ball w₀ ρ ∈ 𝓝 (w₀, w₀) := prod_mem_nhds (ball_mem_nhds _ hρ) (ball_mem_nhds _ hρ)
    filter_upwards [hnhds] with p hp
    obtain ⟨hw, hz⟩ := hp
    rw [dist_eq_norm, dslope_same]
    by_cases hpe : p.1 = p.2
    · simp only [← hpe, dslope_same]
      exact (hρε _ hw).trans (by linarith)
    · set D := deriv f w₀ with hD
      have hg : ∀ x ∈ ball w₀ ρ, HasDerivWithinAt (fun x => f x - D * x) (deriv f x - D) (ball w₀ ρ) x := by
        intro x hx
        have h1 := ((hf.differentiableAt (hΩ.mem_nhds (hρΩ hx))).hasDerivAt).sub
          ((hasDerivAt_id' x).const_mul D)
        rw [mul_one] at h1
        exact h1.hasDerivWithinAt
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg
        (fun x hx => (hρε x hx).le) (convex_ball w₀ ρ) hw hz
      have hne' : p.2 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm hpe)
      rw [dslope_of_ne _ (Ne.symm hpe), slope_def_field]
      have : (f p.2 - f p.1) / (p.2 - p.1) - D
          = ((f p.2 - D * p.2) - (f p.1 - D * p.1)) / (p.2 - p.1) := by
        field_simp
        ring
      have hpos : 0 < ‖p.2 - p.1‖ := norm_pos_iff.2 hne'
      rw [this, norm_div]
      calc ‖f p.2 - D * p.2 - (f p.1 - D * p.1)‖ / ‖p.2 - p.1‖
          ≤ (ε / 2 * ‖p.2 - p.1‖) / ‖p.2 - p.1‖ := by gcongr
        _ = ε / 2 := mul_div_cancel_right₀ _ hpos.ne'
        _ < ε := by linarith
  · have hfw : ContinuousAt f w₀ := (hf.differentiableAt (hΩ.mem_nhds hw₀)).continuousAt
    have hfz : ContinuousAt f z₀ := (hf.differentiableAt (hΩ.mem_nhds hz₀)).continuousAt
    have h1 : ContinuousAt (fun p : ℂ × ℂ => (f p.2 - f p.1) / (p.2 - p.1)) (w₀, z₀) := by
      refine ContinuousAt.div ?_ (by fun_prop) (sub_ne_zero.2 (Ne.symm hne))
      exact (hfz.comp (f := Prod.snd) continuousAt_snd).sub (hfw.comp (f := Prod.fst) continuousAt_fst)
    refine h1.congr ?_
    filter_upwards [(isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hne] with p hp
    rw [dslope_of_ne _ (Ne.symm hp), slope_def_field]

/-! ### Decay at infinity -/

lemma tendsto_cauchyInt_zero {f : ℂ → ℂ} {l : List ℂ} (hf : ContinuousOn f (polyTrace l)) :
    Tendsto (fun z => polyInt (fun w => f w / (w - z)) l) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨C, hC⟩ := (polyTrace_isCompact l).exists_bound_of_continuousOn hf
  obtain ⟨R, hR⟩ := (polyTrace_isCompact l).isBounded.subset_closedBall (0 : ℂ)
  have hev : ∀ᶠ z in cocompact ℂ, ‖polyInt (fun w => f w / (w - z)) l‖ ≤
      2 * C / ‖z‖ * polyLength l := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_ge_atTop (2 * R + 1)] with z hz
    refine norm_polyInt_le (fun w hw => ?_)
    have hw0 : ‖w‖ ≤ R := by simpa using hR hw
    have hR0 : 0 ≤ R := (norm_nonneg w).trans hw0
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC w hw)
    have hzpos : 0 < ‖z‖ := by linarith
    have h1 : ‖z‖ / 2 ≤ ‖w - z‖ := by
      have := norm_sub_norm_le z w
      rw [norm_sub_rev] at this
      linarith
    rw [norm_div]
    calc ‖f w‖ / ‖w - z‖ ≤ C / (‖z‖ / 2) :=
          div_le_div₀ hC0 (hC w hw) (by positivity) h1
      _ = 2 * C / ‖z‖ := by field_simp
  refine squeeze_zero_norm' hev ?_
  have := ((tendsto_const_nhds (x := 2 * C)).div_atTop (tendsto_norm_cocompact_atTop (E := ℂ))).mul_const
    (polyLength l)
  simpa using this

lemma windInt_eq_zero_of_large {l : List ℂ} (hl : IsClosedPoly l) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : polyTrace l ⊆ closedBall 0 R) {z : ℂ} (hz : R < ‖z‖) : windInt l z = 0 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
    linarith
  set S : Set ℂ := (fun t : ℝ => (t : ℂ) * z) '' Ici 1 with hS
  have hSpc : IsPreconnected S :=
    isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * z).continuousOn
  have hSΓ : ∀ x ∈ S, x ∉ polyTrace l := by
    rintro _ ⟨t, ht, rfl⟩ hmem
    have h1 := hR hmem
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans ht)] at h1
    have : ‖z‖ ≤ t * ‖z‖ := le_mul_of_one_le_left (norm_nonneg _) ht
    linarith
  have hloc : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, windInt l y = windInt l x :=
    fun x hx => windInt_locallyConstant hl (hSΓ x hx)
  have hzS : z ∈ S := ⟨1, Set.mem_Ici.2 le_rfl, by simp⟩
  have hconst : ∀ x ∈ S, windInt l x = windInt l z := by
    set c := windInt l z with hc
    set u : Set ℂ := {x | ∀ᶠ y in 𝓝 x, windInt l y = c} with hu
    set v : Set ℂ := {x | ∀ᶠ y in 𝓝 x, windInt l y ≠ c} with hv
    have huo : IsOpen u := isOpen_setOfPred_eventually_nhds
    have hvo : IsOpen v := isOpen_setOfPred_eventually_nhds
    have huv : Disjoint u v := Set.disjoint_left.2 fun x hx1 hx2 => by
      obtain ⟨y, hy1, hy2⟩ := (hx1.and hx2).exists
      exact hy2 hy1
    have hcov : S ⊆ u ∪ v := fun x hx => by
      by_cases hxc : windInt l x = c
      · left
        filter_upwards [hloc x hx] with y hy
        rw [hy, hxc]
      · right
        filter_upwards [hloc x hx] with y hy
        rw [hy]
        exact hxc
    rcases hSpc.subset_or_subset huo hvo huv hcov with h | h
    · exact fun x hx => (h hx).self_of_nhds
    · exact absurd (h hzS).self_of_nhds (not_not.2 rfl)
  have hray : Tendsto (fun t : ℝ => (t : ℂ) * z) atTop (cocompact ℂ) := by
    rw [← cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    have : (fun t : ℝ => ‖(t : ℂ) * z‖) = fun t => |t| * ‖z‖ := by
      ext t
      simp
    rw [this]
    exact tendsto_abs_atTop_atTop.atTop_mul_const (norm_pos_iff.2 hz0)
  have htend : Tendsto (fun t : ℝ => windInt l ((t : ℂ) * z)) atTop (𝓝 0) :=
    (windInt_tendsto_zero l).comp hray
  have hev : (fun t : ℝ => windInt l ((t : ℂ) * z)) =ᶠ[atTop] fun _ => windInt l z :=
    (eventually_ge_atTop (1 : ℝ)).mono fun t ht => hconst _ ⟨t, ht, rfl⟩
  exact tendsto_nhds_unique tendsto_const_nhds (htend.congr' hev)

/-! ### Dixon's argument -/

lemma PolyIn.head_mem {U : Set ℂ} : ∀ {a : ℂ} {rest : List ℂ}, PolyIn U (a :: rest) → a ∈ U
  | _, [], h => h
  | _, _ :: _, h => h.1 (left_mem_segment ℝ _ _)

/-- Dixon's function `z ↦ ∫ (f w - f z)/(w - z) dw`. -/
noncomputable def dixonH (f : ℂ → ℂ) (l : List ℂ) (z : ℂ) : ℂ :=
  polyInt (fun w => dslope f w z) l

/-- The Cauchy-type integral `z ↦ ∫ f w/(w - z) dw`. -/
noncomputable def dixonH₁ (f : ℂ → ℂ) (l : List ℂ) (z : ℂ) : ℂ :=
  polyInt (fun w => f w / (w - z)) l

lemma dixonH_differentiableOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) {l : List ℂ} (hlΩ : PolyIn Ω l) :
    DifferentiableOn ℂ (dixonH f l) Ω := by
  have hΓΩ : polyTrace l ⊆ Ω := polyTrace_subset hlΩ
  have hd : ∀ w ∈ polyTrace l, DifferentiableOn ℂ (fun z => dslope f w z) Ω :=
    fun w hw => (Complex.differentiableOn_dslope (hΩ.mem_nhds (hΓΩ hw))).2 hf
  have h1 := continuousOn_dslope_uncurry hΩ hf
  have h2 : ContinuousOn (fun p : ℂ × ℂ => (p.2, p.1)) (Ω ×ˢ polyTrace l) :=
    (continuous_snd.prodMk continuous_fst).continuousOn
  have h3 : MapsTo (fun p : ℂ × ℂ => (p.2, p.1)) (Ω ×ˢ polyTrace l) (Ω ×ˢ Ω) :=
    fun p hp => ⟨hΓΩ hp.2, hp.1⟩
  have hc' := h1.comp h2 h3
  have hc : ContinuousOn (fun p : ℂ × ℂ => dslope f p.2 p.1) (Ω ×ˢ polyTrace l) := hc'
  show DifferentiableOn ℂ (fun z => polyInt (fun w => dslope f w z) l) Ω
  exact differentiableOn_polyInt_param (l := l) hΩ (g := fun z w => dslope f w z) hd hc

/-- The set `Ω₁` of Dixon's proof. -/
def dixonSet (l : List ℂ) : Set ℂ := {z | z ∉ polyTrace l ∧ windInt l z = 0}

lemma isOpen_dixonSet {l : List ℂ} (hl : IsClosedPoly l) : IsOpen (dixonSet l) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  filter_upwards [(polyTrace_isCompact l).isClosed.isOpen_compl.mem_nhds hz.1,
    windInt_locallyConstant hl hz.1] with b hb1 hb2
  exact ⟨hb1, hb2.trans hz.2⟩

lemma dixonH₁_differentiableOn {f : ℂ → ℂ} {l : List ℂ} (hfΓ : ContinuousOn f (polyTrace l))
    (hl : IsClosedPoly l) :
    DifferentiableOn ℂ (dixonH₁ f l) (dixonSet l) := by
  have hd : ∀ w ∈ polyTrace l, DifferentiableOn ℂ (fun z => f w / (w - z)) (dixonSet l) := by
    intro w hw
    refine (differentiableOn_const (f w)).div ((differentiableOn_const w).sub differentiableOn_id) ?_
    intro z hz
    exact sub_ne_zero.2 fun h => hz.1 (h ▸ hw)
  have hc : ContinuousOn (fun p : ℂ × ℂ => f p.2 / (p.2 - p.1)) (dixonSet l ×ˢ polyTrace l) := by
    refine (hfΓ.comp continuous_snd.continuousOn (fun p hp => hp.2)).div
      (continuous_snd.sub continuous_fst).continuousOn ?_
    intro p hp
    exact sub_ne_zero.2 fun h => hp.1.1 (h ▸ hp.2)
  exact differentiableOn_polyInt_param (isOpen_dixonSet hl) (g := fun z w => f w / (w - z)) hd hc

lemma dixonH_eq_dixonH₁ {f : ℂ → ℂ} {l : List ℂ} (hfΓ : ContinuousOn f (polyTrace l))
    {z : ℂ} (hz : z ∈ dixonSet l) : dixonH f l z = dixonH₁ f l z := by
  have hne : ∀ w ∈ polyTrace l, w - z ≠ 0 := fun w hw => sub_ne_zero.2 fun h => hz.1 (h ▸ hw)
  have hc1 : ContinuousOn (fun w => f w / (w - z)) (polyTrace l) :=
    hfΓ.div (continuousOn_id.sub continuousOn_const) hne
  have hc2 : ContinuousOn (fun w => f z * (w - z)⁻¹) (polyTrace l) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ hne)
  have hcongr : polyInt (fun w => dslope f w z) l
      = polyInt (fun w => f w / (w - z) - f z * (w - z)⁻¹) l := by
    refine polyInt_congr fun w hw => ?_
    have hwz : w - z ≠ 0 := hne w hw
    have hzw : z - w ≠ 0 := fun h' => hwz (by linear_combination -h')
    rw [dslope_of_ne _ (sub_ne_zero.1 hzw), slope_def_field]
    field_simp
    ring
  unfold dixonH dixonH₁
  rw [hcongr, polyInt_sub hc1 hc2, polyInt_const_mul]
  have : polyInt (fun w => (w - z)⁻¹) l = 0 := hz.2
  rw [this, mul_zero, sub_zero]

/-- Dixon: the entire function built from `∫ (f w - f z)/(w - z) dw` vanishes. -/
theorem dixon_dslope_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) {l : List ℂ} (hl : IsClosedPoly l) (hlΩ : PolyIn Ω l)
    (hw : ∀ a : ℂ, a ∉ Ω → windInt l a = 0) :
    ∀ z ∈ Ω, polyInt (fun w => dslope f w z) l = 0 := by
  classical
  have hΓc : IsCompact (polyTrace l) := polyTrace_isCompact l
  have hΓΩ : polyTrace l ⊆ Ω := polyTrace_subset hlΩ
  have hfΓ : ContinuousOn f (polyTrace l) := hf.continuousOn.mono hΓΩ
  have hΩ₁o : IsOpen (dixonSet l) := isOpen_dixonSet hl
  have hhd := dixonH_differentiableOn hΩ hf hlΩ
  have hh₁d := dixonH₁_differentiableOn hfΓ hl
  obtain ⟨E, hE⟩ : ∃ E : ℂ → ℂ, ∀ z, E z = if z ∈ Ω then dixonH f l z else dixonH₁ f l z :=
    ⟨_, fun _ => rfl⟩
  have hE1 : ∀ z ∈ dixonSet l, E z = dixonH₁ f l z := by
    intro z hz
    rw [hE]
    by_cases hzΩ : z ∈ Ω
    · rw [if_pos hzΩ]
      exact dixonH_eq_dixonH₁ hfΓ hz
    · rw [if_neg hzΩ]
  have hEd : Differentiable ℂ E := by
    intro z
    by_cases hzΩ : z ∈ Ω
    · refine (hhd.differentiableAt (hΩ.mem_nhds hzΩ)).congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hzΩ] with y hy
      rw [hE, if_pos hy]
    · have hz1 : z ∈ dixonSet l := ⟨fun hz => hzΩ (hΓΩ hz), hw z hzΩ⟩
      refine (hh₁d.differentiableAt (hΩ₁o.mem_nhds hz1)).congr_of_eventuallyEq ?_
      filter_upwards [hΩ₁o.mem_nhds hz1] with y hy
      exact hE1 y hy
  -- decay at infinity
  obtain ⟨R, hR⟩ := hΓc.isBounded.subset_closedBall (0 : ℂ)
  have hEtend : Tendsto E (cocompact ℂ) (𝓝 0) := by
    have hlim : Tendsto (dixonH₁ f l) (cocompact ℂ) (𝓝 0) := tendsto_cauchyInt_zero hfΓ
    refine hlim.congr' ?_
    have hbig : ∀ᶠ z in cocompact ℂ, z ∈ dixonSet l := by
      have h1 : ∀ᶠ z in cocompact ℂ, z ∉ polyTrace l := hΓc.compl_mem_cocompact
      have h2 : ∀ᶠ z in cocompact ℂ, windInt l z = 0 := by
        have hR' : polyTrace l ⊆ closedBall 0 (max R 0) :=
          hR.trans (closedBall_subset_closedBall (le_max_left _ _))
        filter_upwards [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_gt_atTop (max R 0)]
          with z hz
        exact windInt_eq_zero_of_large hl (le_max_right _ _) hR' hz
      filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩
    filter_upwards [hbig] with z hz
    exact (hE1 z hz).symm
  intro z hz
  have h0 := hEd.apply_eq_of_tendsto_cocompact z hEtend
  rw [hE, if_pos hz] at h0
  exact h0

end Dixon

end AhlforsComplexAnalysis.Polygon

open AhlforsComplexAnalysis.Polygon

/-- **Cauchy's theorem for polygons** (Dixon's proof). -/
theorem solution {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    {l : List ℂ} (hl : IsClosedPoly l) (hlΩ : PolyIn Ω l)
    (hw : ∀ a : ℂ, a ∉ Ω → windInt l a = 0) : polyInt f l = 0 := by
  obtain ⟨a, rest, hlcons⟩ : ∃ (a : ℂ) (rest : List ℂ), l = a :: rest := by
    cases l with
    | nil => exact absurd rfl hl.1
    | cons a rest => exact ⟨a, rest, rfl⟩
  have haΩ : a ∈ Ω := by
    rw [hlcons] at hlΩ
    exact Dixon.PolyIn.head_mem hlΩ
  have hfa : DifferentiableAt ℂ f a := hf.differentiableAt (hΩ.mem_nhds haΩ)
  have hFd : DifferentiableOn ℂ (fun w => (w - a) * f w) Ω :=
    (differentiableOn_id.sub_const a).mul hf
  have key := Dixon.dixon_dslope_zero hΩ hFd hl hlΩ hw a haΩ
  have hfeq : (fun w => dslope (fun w => (w - a) * f w) w a) = f := by
    funext w
    by_cases hwa : w = a
    · rw [hwa, dslope_same]
      have h1 : HasDerivAt (fun x => x - a) 1 a := (hasDerivAt_id a).sub_const a
      have h2 := h1.mul hfa.hasDerivAt
      exact (h2.congr_deriv (by simp)).deriv
    · rw [dslope_of_ne _ (Ne.symm hwa), slope_def_field]
      have h1 : a - w ≠ 0 := sub_ne_zero.2 (Ne.symm hwa)
      show ((a - a) * f a - (w - a) * f w) / (a - w) = f w
      field_simp
      ring
  rw [hfeq] at key
  exact key

#print axioms solution

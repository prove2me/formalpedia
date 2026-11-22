-- Prove2me | solution 1 for AdaptiveStepIPM.Probabilistic.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:59:14.209531+00:00
-- url     : https://prove2.me/submissions/2db3e79d-4b79-4dd0-9e37-baebb5e25745

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter AdaptiveStepIPM.Probabilistic
open scoped RealInnerProductSpace ENNReal NNReal Matrix

section GammaBeta

private lemma gammaPDF_ae_eq_zero_of_not_pos (a r : ℝ) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))ᶜ), gammaPDF a r x = 0 := by
  have hsub : (Set.Ioi (0 : ℝ))ᶜ = Set.Iio (0 : ℝ) ∪ {0} := by
    ext x; simp [le_iff_lt_or_eq]
  rw [hsub, ae_restrict_iff' (measurableSet_Iio.union (measurableSet_singleton 0))]
  have hzero : ∀ᵐ x ∂volume, x ≠ (0 : ℝ) := by
    rw [ae_iff]; simp
  filter_upwards [hzero] with x hx hmem
  rcases hmem with hlt | heq
  · exact gammaPDF_of_neg hlt
  · exact absurd heq hx

private lemma setLIntegral_Ioi_gammaPDF {a r : ℝ} (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, gammaPDF a r x * f x = ∫⁻ x in Set.Ioi 0, gammaPDF a r x * f x := by
  rw [← lintegral_add_compl _ measurableSet_Ioi]
  have h0 : ∫⁻ x in (Set.Ioi (0 : ℝ))ᶜ, gammaPDF a r x * f x = 0 := by
    have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))ᶜ), gammaPDF a r x * f x = 0 := by
      filter_upwards [gammaPDF_ae_eq_zero_of_not_pos a r] with x hx
      simp [hx]
    rw [lintegral_congr_ae hae, lintegral_zero]
  rw [h0, add_zero]

private lemma gamma_beta_pdf_mul_eq {α β r s t : ℝ} (hα : 0 < α) (hβ : 0 < β) (hr : 0 < r)
    (hs : 0 < s) (ht0 : 0 < t) (ht1 : t < 1) :
    s * (gammaPDFReal α r (s * t) * gammaPDFReal β r (s * (1 - t))) =
      gammaPDFReal (α + β) r s * betaPDFReal α β t := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  have hst : 0 < s * t := mul_pos hs ht0
  have hs1t : 0 < s * (1 - t) := mul_pos hs h1t
  simp only [gammaPDFReal, betaPDFReal, beta, if_pos hst.le, if_pos hs1t.le, if_pos hs.le,
    if_pos (And.intro ht0 ht1)]
  have hΓα : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have hΓβ : Real.Gamma β ≠ 0 := (Real.Gamma_pos_of_pos hβ).ne'
  have hΓαβ : Real.Gamma (α + β) ≠ 0 := (Real.Gamma_pos_of_pos (add_pos hα hβ)).ne'
  rw [Real.mul_rpow hs.le ht0.le, Real.mul_rpow hs.le h1t.le]
  have hrpow : r ^ (α + β) = r ^ α * r ^ β := Real.rpow_add hr α β
  have hspow : s ^ (α + β - 1) = s * (s ^ (α - 1) * s ^ (β - 1)) := by
    calc s ^ (α + β - 1)
        = s ^ (1 + ((α - 1) + (β - 1))) := by congr 1; ring
      _ = s ^ (1 : ℝ) * s ^ ((α - 1) + (β - 1)) := Real.rpow_add hs _ _
      _ = s * (s ^ (α - 1) * s ^ (β - 1)) := by rw [Real.rpow_one, Real.rpow_add hs]
  have hexp : Real.exp (-(r * s)) = Real.exp (-(r * (s * t))) * Real.exp (-(r * (s * (1 - t)))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hrpow, hspow, hexp]
  field_simp [hΓα, hΓβ, hΓαβ]

private lemma lintegral_gamma_prod_comp {α β r : ℝ} (hα : 0 < α) (hβ : 0 < β) (hr : 0 < r)
    {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f (p.1 + p.2, p.1 / (p.1 + p.2)) ∂((gammaMeasure α r).prod (gammaMeasure β r)) =
      ∫⁻ q, f q ∂((gammaMeasure (α + β) r).prod (betaMeasure α β)) := by
  have : IsProbabilityMeasure (gammaMeasure α r) := isProbabilityMeasure_gammaMeasure hα hr
  have : IsProbabilityMeasure (gammaMeasure β r) := isProbabilityMeasure_gammaMeasure hβ hr
  have : IsProbabilityMeasure (gammaMeasure (α + β) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos hα hβ) hr
  have : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have hmeas_gα : Measurable (gammaPDF α r) := (measurable_gammaPDFReal α r).ennreal_ofReal
  have hmeas_gβ : Measurable (gammaPDF β r) := (measurable_gammaPDFReal β r).ennreal_ofReal
  have hmeas_gαβ : Measurable (gammaPDF (α + β) r) :=
    (measurable_gammaPDFReal (α + β) r).ennreal_ofReal
  have hmeas_b : Measurable (betaPDF α β) := (measurable_betaPDFReal α β).ennreal_ofReal
  have h_beta_zero : ∀ (g : ℝ → ℝ≥0∞),
      ∫⁻ t, betaPDF α β t * g t = ∫⁻ t in Set.Ioo 0 1, betaPDF α β t * g t := by
    intro g
    rw [← lintegral_add_compl _ measurableSet_Ioo]
    have h0 : ∫⁻ t in (Set.Ioo (0 : ℝ) 1)ᶜ, betaPDF α β t * g t = 0 := by
      refine setLIntegral_eq_zero measurableSet_Ioo.compl fun t ht => ?_
      have : betaPDF α β t = 0 := by
        by_cases h1 : t ≤ 0
        · exact betaPDF_eq_zero_of_nonpos h1
        · push Not at h1
          have h2 : 1 ≤ t := by
            by_contra hlt; push Not at hlt; exact ht ⟨h1, hlt⟩
          exact betaPDF_eq_zero_of_one_le h2
      simp [this]
    rw [h0, add_zero]
  -- Expand LHS via Fubini and withDensity
  have hf_comp : Measurable (fun p : ℝ × ℝ => f (p.1 + p.2, p.1 / (p.1 + p.2))) :=
    hf.comp ((measurable_fst.add measurable_snd).prodMk
      (measurable_fst.div (measurable_fst.add measurable_snd)))
  rw [lintegral_prod _ hf_comp.aemeasurable]
  have hinnerL : ∀ x : ℝ, ∫⁻ y, f (x + y, x / (x + y)) ∂gammaMeasure β r =
      ∫⁻ y, gammaPDF β r y * f (x + y, x / (x + y)) := fun x => by
    have hm : Measurable (fun y : ℝ => f (x + y, x / (x + y))) :=
      hf.comp ((measurable_const.add measurable_id).prodMk
        (measurable_const.div (measurable_const.add measurable_id)))
    rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeas_gβ hm]
    simp only [Pi.mul_apply]
  simp_rw [hinnerL]
  have houterL_meas : Measurable (fun x : ℝ => ∫⁻ y, gammaPDF β r y * f (x + y, x / (x + y))) :=
    Measurable.lintegral_prod_right'
      ((hmeas_gβ.comp measurable_snd).mul hf_comp)
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeas_gα houterL_meas]
  simp only [Pi.mul_apply]
  rw [setLIntegral_Ioi_gammaPDF]
  simp_rw [setLIntegral_Ioi_gammaPDF]
  -- Change inner variable s = x + y on Ioi 0
  have hstep1 :
      ∫⁻ x in Set.Ioi (0 : ℝ), gammaPDF α r x *
        ∫⁻ y in Set.Ioi (0 : ℝ), gammaPDF β r y * f (x + y, x / (x + y)) =
      ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ s in Set.Ioi (0 : ℝ),
        (if x < s then gammaPDF α r x * gammaPDF β r (s - x) * f (s, x / s) else 0) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have himg : (fun y : ℝ => x + y) '' Set.Ioi 0 = Set.Ioi x := by
      ext s; constructor
      · rintro ⟨y, hy, rfl⟩; simp only [Set.mem_Ioi] at hy ⊢; linarith
      · intro hs; refine ⟨s - x, by simp only [Set.mem_Ioi] at hs ⊢; linarith, by ring⟩
    have hchg := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.Ioi (0 : ℝ))
      (f := fun y : ℝ => x + y) (f' := fun _ => (1 : ℝ)) measurableSet_Ioi
      (fun y _ => ((hasDerivAt_id y).const_add x).hasDerivWithinAt)
      (fun y₁ _ y₂ _ h => add_left_cancel h)
      (fun s => gammaPDF β r (s - x) * f (s, x / s))
    rw [himg] at hchg
    simp only [abs_one, ENNReal.ofReal_one, one_mul, add_sub_cancel_left] at hchg
    rw [← hchg, ← lintegral_const_mul _ (by fun_prop)]
    have hsub : Set.Ioi x ⊆ Set.Ioi (0 : ℝ) :=
      fun s hs => Set.mem_Ioi.mpr (lt_trans (Set.mem_Ioi.mp hx) (Set.mem_Ioi.mp hs))
    have hInd : ∀ s ∈ Set.Ioi (0 : ℝ),
        (Set.Ioi x).indicator (fun s => gammaPDF α r x * (gammaPDF β r (s - x) * f (s, x / s))) s =
        if x < s then gammaPDF α r x * gammaPDF β r (s - x) * f (s, x / s) else 0 := by
      intro s _
      by_cases hxs : x < s
      · simp [Set.indicator, hxs, mul_assoc]
      · simp [Set.indicator, hxs]
    rw [← setLIntegral_congr_fun measurableSet_Ioi hInd,
      setLIntegral_indicator measurableSet_Ioi, Set.inter_eq_left.mpr hsub]
  rw [hstep1]
  -- Swap integrals via Tonelli
  have hmeas_swap : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then gammaPDF α r p.1 * gammaPDF β r (p.2 - p.1) * f (p.2, p.1 / p.2) else 0) := by
    refine Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ measurable_const
    exact (((hmeas_gα.comp measurable_fst).mul
      (hmeas_gβ.comp (measurable_snd.sub measurable_fst))).mul
      (hf.comp (measurable_snd.prodMk (measurable_fst.div measurable_snd))))
  rw [lintegral_lintegral_swap hmeas_swap.aemeasurable]
  -- Change inner variable x = s * t on Ioo 0 1
  have hstep2 :
      ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ x in Set.Ioi (0 : ℝ),
        (if x < s then gammaPDF α r x * gammaPDF β r (s - x) * f (s, x / s) else 0) =
      ∫⁻ s in Set.Ioi (0 : ℝ), gammaPDF (α + β) r s *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1, betaPDF α β t * f (s, t) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs' : 0 < s := hs
    have hIoo : ∫⁻ x in Set.Ioi (0 : ℝ),
        (if x < s then gammaPDF α r x * gammaPDF β r (s - x) * f (s, x / s) else 0) =
        ∫⁻ x in Set.Ioo (0 : ℝ) s, gammaPDF α r x * gammaPDF β r (s - x) * f (s, x / s) := by
      have hInd : ∀ x ∈ Set.Ioi (0 : ℝ),
          (if x < s then gammaPDF α r x * gammaPDF β r (s - x) * f (s, x / s) else 0) =
          (Set.Iio s).indicator (fun x => gammaPDF α r x * gammaPDF β r (s - x) * f (s, x / s)) x := by
        intro x _
        by_cases hxs : x < s <;> simp [Set.indicator, hxs]
      rw [setLIntegral_congr_fun measurableSet_Ioi hInd,
        setLIntegral_indicator measurableSet_Iio, Set.Iio_inter_Ioi]
    rw [hIoo]
    have himg : (fun t : ℝ => s * t) '' Set.Ioo 0 1 = Set.Ioo 0 s := by
      ext x; constructor
      · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
        exact ⟨mul_pos hs' ht0, by nlinarith⟩
      · rintro ⟨hx0, hxs⟩
        refine ⟨x / s, ⟨div_pos hx0 hs', (div_lt_one hs').mpr hxs⟩, mul_div_cancel₀ x hs'.ne'⟩
    have hchg := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.Ioo (0 : ℝ) 1)
      (f := fun t : ℝ => s * t) (f' := fun _ => s) measurableSet_Ioo
      (fun t _ => by simpa using ((hasDerivAt_id t).const_mul s).hasDerivWithinAt)
      (fun t₁ _ t₂ _ h => mul_left_cancel₀ hs'.ne' h)
      (fun x => gammaPDF α r x * gammaPDF β r (s - x) * f (s, x / s))
    rw [himg] at hchg
    rw [hchg, ← lintegral_const_mul _ (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ⟨ht0, ht1⟩ => ?_
    rw [abs_of_pos hs', mul_div_cancel_left₀ t hs'.ne',
      show s - s * t = s * (1 - t) by ring]
    have hpdf : ENNReal.ofReal s * (gammaPDF α r (s * t) * gammaPDF β r (s * (1 - t))) =
        gammaPDF (α + β) r s * betaPDF α β t := by
      simp only [gammaPDF, betaPDF]
      rw [← ENNReal.ofReal_mul (gammaPDFReal_nonneg hα hr _),
        ← ENNReal.ofReal_mul hs'.le,
        ← ENNReal.ofReal_mul (gammaPDFReal_nonneg (add_pos hα hβ) hr _),
        gamma_beta_pdf_mul_eq hα hβ hr hs' ht0 ht1]
    calc ENNReal.ofReal s * (gammaPDF α r (s * t) * gammaPDF β r (s * (1 - t)) * f (s, t))
        = (ENNReal.ofReal s * (gammaPDF α r (s * t) * gammaPDF β r (s * (1 - t)))) * f (s, t) := by
          ring
      _ = (gammaPDF (α + β) r s * betaPDF α β t) * f (s, t) := by rw [hpdf]
      _ = gammaPDF (α + β) r s * (betaPDF α β t * f (s, t)) := by ring
  rw [hstep2]
  -- Fold RHS back to product measure
  symm
  rw [lintegral_prod _ hf.aemeasurable]
  have hinnerR : ∀ s : ℝ, ∫⁻ t, f (s, t) ∂betaMeasure α β =
      ∫⁻ t, betaPDF α β t * f (s, t) := fun s => by
    have hm : Measurable (fun t : ℝ => f (s, t)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeas_b hm]
    simp only [Pi.mul_apply]
  simp_rw [hinnerR]
  have houterR_meas : Measurable (fun s : ℝ => ∫⁻ t, betaPDF α β t * f (s, t)) :=
    Measurable.lintegral_prod_right' ((hmeas_b.comp measurable_snd).mul hf)
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeas_gαβ houterR_meas]
  simp only [Pi.mul_apply]
  rw [setLIntegral_Ioi_gammaPDF]
  simp_rw [h_beta_zero]

private lemma gamma_add_gamma {α β r : ℝ} (hα : 0 < α) (hβ : 0 < β) (hr : 0 < r) :
    ((gammaMeasure α r).prod (gammaMeasure β r)).map (fun p : ℝ × ℝ => p.1 + p.2) =
      gammaMeasure (α + β) r := by
  have : IsProbabilityMeasure (gammaMeasure α r) := isProbabilityMeasure_gammaMeasure hα hr
  have : IsProbabilityMeasure (gammaMeasure β r) := isProbabilityMeasure_gammaMeasure hβ hr
  have : IsProbabilityMeasure (gammaMeasure (α + β) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos hα hβ) hr
  have : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, ← lintegral_indicator_one (hs.preimage (by fun_prop))]
  let f : ℝ × ℝ → ℝ≥0∞ := fun q => s.indicator 1 q.1
  have hf : Measurable f := (measurable_const.indicator hs).comp measurable_fst
  have h1 : ∫⁻ p, ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' s).indicator 1 p
      ∂((gammaMeasure α r).prod (gammaMeasure β r)) =
      ∫⁻ p, f (p.1 + p.2, p.1 / (p.1 + p.2))
      ∂((gammaMeasure α r).prod (gammaMeasure β r)) := by
    refine lintegral_congr fun p => ?_
    by_cases hp : p.1 + p.2 ∈ s <;> simp [f, Set.indicator, hp]
  rw [h1, lintegral_gamma_prod_comp hα hβ hr hf, lintegral_prod _ hf.aemeasurable]
  simp [f, lintegral_indicator_one hs]

private lemma gamma_div_add_gamma {α β r : ℝ} (hα : 0 < α) (hβ : 0 < β) (hr : 0 < r) :
    ((gammaMeasure α r).prod (gammaMeasure β r)).map (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) =
      betaMeasure α β := by
  have : IsProbabilityMeasure (gammaMeasure α r) := isProbabilityMeasure_gammaMeasure hα hr
  have : IsProbabilityMeasure (gammaMeasure β r) := isProbabilityMeasure_gammaMeasure hβ hr
  have : IsProbabilityMeasure (gammaMeasure (α + β) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos hα hβ) hr
  have : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, ← lintegral_indicator_one (hs.preimage (by fun_prop))]
  let f : ℝ × ℝ → ℝ≥0∞ := fun q => s.indicator 1 q.2
  have hf : Measurable f := (measurable_const.indicator hs).comp measurable_snd
  have h1 : ∫⁻ p, ((fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' s).indicator 1 p
      ∂((gammaMeasure α r).prod (gammaMeasure β r)) =
      ∫⁻ p, f (p.1 + p.2, p.1 / (p.1 + p.2))
      ∂((gammaMeasure α r).prod (gammaMeasure β r)) := by
    refine lintegral_congr fun p => ?_
    by_cases hp : p.1 / (p.1 + p.2) ∈ s <;> simp [f, Set.indicator, hp]
  rw [h1, lintegral_gamma_prod_comp hα hβ hr hf, lintegral_prod _ hf.aemeasurable]
  simp [f, lintegral_indicator_one hs]

private lemma gaussianReal_sq_eq_gamma :
    (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) = gammaMeasure (1 / 2) (1 / 2) := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    withDensity_apply _ (hs.preimage (by fun_prop)),
    ← lintegral_indicator (hs.preimage (by fun_prop))]
  have hind : ∀ x, ((fun x : ℝ => x ^ 2) ⁻¹' s).indicator (gaussianPDF 0 1) x =
      gaussianPDF 0 1 x * s.indicator 1 (x ^ 2) := by
    intro x; by_cases hx : x ^ 2 ∈ s <;> simp [Set.indicator, hx]
  simp_rw [hind]
  have hsplit : ∫⁻ x, gaussianPDF 0 1 x * s.indicator 1 (x ^ 2) =
      2 * ∫⁻ x in Set.Ioi (0 : ℝ), gaussianPDF 0 1 x * s.indicator 1 (x ^ 2) := by
    rw [← lintegral_add_compl _ measurableSet_Ioi]
    have hcompl : ∫⁻ x in (Set.Ioi (0 : ℝ))ᶜ, gaussianPDF 0 1 x * s.indicator 1 (x ^ 2) =
        ∫⁻ x in Set.Iio (0 : ℝ), gaussianPDF 0 1 x * s.indicator 1 (x ^ 2) := by
      have hsub : (Set.Ioi (0 : ℝ))ᶜ = Set.Iio (0 : ℝ) ∪ {0} := by
        ext x; simp [le_iff_lt_or_eq]
      rw [hsub, lintegral_union (measurableSet_singleton 0)
        (Set.disjoint_singleton_right.mpr (by simp)),
        Measure.restrict_eq_zero.mpr Real.volume_singleton, lintegral_zero_measure, add_zero]
    rw [hcompl]
    have hneg : ∫⁻ x in Set.Iio (0 : ℝ), gaussianPDF 0 1 x * s.indicator 1 (x ^ 2) =
        ∫⁻ x in Set.Ioi (0 : ℝ), gaussianPDF 0 1 x * s.indicator 1 (x ^ 2) := by
      have himg : (fun x : ℝ => -x) '' Set.Ioi 0 = Set.Iio 0 := by
        ext x; simp
      have hchg := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.Ioi (0 : ℝ))
        (f := fun x : ℝ => -x) (f' := fun _ => (-1 : ℝ)) measurableSet_Ioi
        (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt)
        (fun _ _ _ _ h => neg_injective h)
        (fun x => gaussianPDF 0 1 x * s.indicator 1 (x ^ 2))
      rw [himg] at hchg
      rw [hchg]
      refine setLIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp [gaussianPDF, gaussianPDFReal]
    rw [hneg, two_mul]
  rw [hsplit]
  symm
  rw [gammaMeasure, withDensity_apply _ hs, ← lintegral_indicator hs]
  have hind2 : ∀ t, s.indicator (gammaPDF (1 / 2) (1 / 2)) t =
      gammaPDF (1 / 2) (1 / 2) t * s.indicator 1 t := by
    intro t; by_cases ht : t ∈ s <;> simp [Set.indicator, ht]
  simp_rw [hind2]
  rw [setLIntegral_Ioi_gammaPDF]
  have himg : (fun x : ℝ => x ^ 2) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext t; constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : 0 < x := hx
      exact sq_pos_of_pos hx'
    · intro ht
      have ht' : 0 < t := ht
      exact ⟨Real.sqrt t, Real.sqrt_pos.mpr ht', Real.sq_sqrt ht'.le⟩
  have hchg := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.Ioi (0 : ℝ))
    (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x) measurableSet_Ioi
    (fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt)
    (fun x₁ hx₁ x₂ hx₂ h => by
      have hx1' : 0 ≤ x₁ := le_of_lt (Set.mem_Ioi.mp hx₁)
      have hx2' : 0 ≤ x₂ := le_of_lt (Set.mem_Ioi.mp hx₂)
      nlinarith)
    (fun t => gammaPDF (1 / 2) (1 / 2) t * s.indicator 1 t)
  rw [himg] at hchg
  rw [hchg, ← lintegral_const_mul _ (by fun_prop)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hxpos : 0 < x := hx
  have hpdf : ENNReal.ofReal |2 * x| * gammaPDF (1 / 2) (1 / 2) (x ^ 2) =
      2 * gaussianPDF 0 1 x := by
    rw [abs_of_pos (by positivity : 0 < 2 * x), gammaPDF, gaussianPDF,
      ← ENNReal.ofReal_mul (by positivity),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    simp only [gammaPDFReal, gaussianPDFReal, if_pos (sq_nonneg x),
      NNReal.coe_one, mul_one, sub_zero, Real.Gamma_one_half_eq]
    have hhalf : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
      rw [Real.sqrt_eq_rpow, one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    have hxpow : (x ^ 2) ^ ((1 / 2 : ℝ) - 1) = x⁻¹ := by
      have : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
      rw [this, Real.rpow_neg (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq hxpos.le]
    rw [hhalf, hxpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
    have hxne : x ≠ 0 := hxpos.ne'
    have hexp : -(1 / 2 * x ^ 2) = -x ^ 2 / 2 := by ring
    rw [hexp]
    field_simp [h2, hpi, hxne]
  calc ENNReal.ofReal |2 * x| * (gammaPDF (1 / 2) (1 / 2) (x ^ 2) * s.indicator 1 (x ^ 2))
      = (ENNReal.ofReal |2 * x| * gammaPDF (1 / 2) (1 / 2) (x ^ 2)) * s.indicator 1 (x ^ 2) := by
        ring
    _ = 2 * gaussianPDF 0 1 x * s.indicator 1 (x ^ 2) := by rw [hpdf]
    _ = 2 * (gaussianPDF 0 1 x * s.indicator 1 (x ^ 2)) := by ring

private lemma pi_gaussian_sum_sq_eq_gamma :
    ∀ k : ℕ, 1 ≤ k →
      (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).map (fun x : Fin k → ℝ => ∑ i, x i ^ 2) =
        gammaMeasure ((k : ℝ) / 2) (1 / 2) := by
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  induction m with
  | zero =>
    have hmp := measurePreserving_piUnique (fun _ : Fin 1 => gaussianReal 0 1)
    have hfun : (fun x : Fin 1 → ℝ => ∑ i, x i ^ 2) =
        (fun t : ℝ => t ^ 2) ∘ (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)) := by
      ext x; simp
    rw [hfun, ← Measure.map_map (by fun_prop) hmp.measurable, hmp.map_eq]
    simpa using gaussianReal_sq_eq_gamma
  | succ m ih =>
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1 + 1) => gaussianReal 0 1) 0
    have hfun : (fun x : Fin (m + 1 + 1) → ℝ => ∑ i, x i ^ 2) =
        (fun p : ℝ × ℝ => p.1 + p.2) ∘
        (Prod.map (fun t : ℝ => t ^ 2) (fun y : Fin (m + 1) → ℝ => ∑ i, y i ^ 2)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1 + 1) => ℝ) 0) := by
      ext x
      simp [Fin.sum_univ_succ, Fin.tail, MeasurableEquiv.piFinSuccAbove_apply]
    rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) hmp.measurable, hmp.map_eq]
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      gaussianReal_sq_eq_gamma, ih (Nat.succ_pos m),
      gamma_add_gamma (by positivity) (by positivity) (by positivity)]
    congr 1; push_cast; ring

private lemma stdGaussian_norm_sq_eq_gamma {k : ℕ} (hk : 1 ≤ k) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun y => ‖y‖ ^ 2) =
      gammaMeasure ((k : ℝ) / 2) (1 / 2) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ∘ WithLp.toLp 2 =
      fun x : Fin k → ℝ => ∑ i, x i ^ 2 := by
    ext x
    simp [EuclideanSpace.real_norm_sq_eq]
  rw [hfun]
  exact pi_gaussian_sum_sq_eq_gamma k hk

end GammaBeta

section GaussianSubspace

private instance isProbabilityMeasure_gaussianMatrix (m n : ℕ) :
    IsProbabilityMeasure (gaussianMatrix m n) := by
  unfold gaussianMatrix
  infer_instance

private lemma stdGaussian_proper_submodule_eq_zero {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hV : V ≠ ⊤) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) (V : Set (EuclideanSpace ℝ (Fin n))) = 0 := by
  have hbot : Vᗮ ≠ ⊥ := by
    intro h
    apply hV
    rw [← V.orthogonal_orthogonal, h, Submodule.bot_orthogonal_eq_top]
  obtain ⟨u, huV, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let u₀ : EuclideanSpace ℝ (Fin n) := ‖u‖⁻¹ • u
  have hu₀_norm : ‖u₀‖ = 1 := by
    simp [u₀, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)]
  have hu₀_mem : u₀ ∈ Vᗮ := Vᗮ.smul_mem _ huV
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := innerSL ℝ u₀
  have hmapL : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L = gaussianReal 0 1 := by
    apply Measure.ext_of_charFun
    ext t
    rw [charFun_apply_real, charFun_gaussianReal]
    have hint : ∫ x, Complex.exp (↑t * ↑x * Complex.I)
        ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).map L) =
        charFunDual (stdGaussian (EuclideanSpace ℝ (Fin n))) (t • L) := by
      rw [charFunDual_apply, integral_map (by fun_prop) (by fun_prop)]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp [mul_comm]
    rw [hint, charFunDual_stdGaussian]
    have hLnorm : ‖L‖ = 1 := by
      simp [L, hu₀_norm]
    simp only [norm_smul, Real.norm_eq_abs, hLnorm, mul_one, NNReal.coe_one, Complex.ofReal_zero,
      mul_zero, zero_mul, Complex.ofReal_one, one_mul, zero_sub, neg_div]
    rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  have hsub : (V : Set (EuclideanSpace ℝ (Fin n))) ⊆ L ⁻¹' ({0} : Set ℝ) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff, L, innerSL_apply_apply]
    exact (Submodule.mem_orthogonal' V u₀).mp hu₀_mem x hx
  have hzero : (gaussianReal 0 1) ({0} : Set ℝ) = 0 := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ (measurableSet_singleton 0),
      Measure.restrict_eq_zero.mpr Real.volume_singleton, lintegral_zero_measure]
  have hle : stdGaussian (EuclideanSpace ℝ (Fin n)) (V : Set _) ≤
      stdGaussian (EuclideanSpace ℝ (Fin n)) (L ⁻¹' {0}) := measure_mono hsub
  rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton 0), hmapL, hzero] at hle
  exact nonpos_iff_eq_zero.mp hle

private lemma stdGaussian_singleton_zero {k : ℕ} (hk : 1 ≤ k) :
    stdGaussian (EuclideanSpace ℝ (Fin k)) ({0} : Set (EuclideanSpace ℝ (Fin k))) = 0 := by
  have hne : (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin k))) ≠ ⊤ := by
    intro h
    have hdim := congr_arg (fun S : Submodule ℝ (EuclideanSpace ℝ (Fin k)) => Module.finrank ℝ S) h
    simp at hdim
    omega
  simpa using stdGaussian_proper_submodule_eq_zero (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin k))) hne

private lemma det_mul_transpose_ne_zero_iff_linearIndependent {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) ℝ) :
    (G * Gᵀ).det ≠ 0 ↔ LinearIndependent ℝ (fun i : Fin m => WithLp.toLp 2 (G i)) := by
  constructor
  · intro hdet
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hGt : Gᵀ *ᵥ c = 0 := by
      ext j
      have hj := congr_fun (congr_arg WithLp.ofLp hc) j
      simpa [Matrix.mulVec, dotProduct, mul_comm] using hj
    have hGGt : (G * Gᵀ) *ᵥ c = 0 := by
      rw [← Matrix.mulVec_mulVec, hGt, Matrix.mulVec_zero]
    have hunit : IsUnit (G * Gᵀ).det := isUnit_iff_ne_zero.mpr hdet
    have h1 : (G * Gᵀ)⁻¹ *ᵥ ((G * Gᵀ) *ᵥ c) = c := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
    rw [hGGt, Matrix.mulVec_zero] at h1
    intro i; exact congr_fun h1.symm i
  · intro hli
    by_contra hdet
    have hker : LinearMap.ker (G * Gᵀ).mulVecLin ≠ ⊥ := by
      intro hbot
      have hinj : Function.Injective (G * Gᵀ).mulVecLin := LinearMap.ker_eq_bot.mp hbot
      have hsurj : Function.Surjective (G * Gᵀ).mulVecLin :=
        LinearMap.injective_iff_surjective.mp hinj
      let e := LinearEquiv.ofBijective (G * Gᵀ).mulVecLin ⟨hinj, hsurj⟩
      let B : Matrix (Fin m) (Fin m) ℝ := LinearMap.toMatrix' e.symm.toLinearMap
      have hmul : B * (G * Gᵀ) = 1 := by
        apply Matrix.toLin'.injective
        rw [Matrix.toLin'_mul, Matrix.toLin'_one, LinearMap.ext_iff]
        intro v
        simp only [B, LinearMap.comp_apply, LinearMap.id_apply, Matrix.toLin'_toMatrix']
        exact e.symm_apply_apply v
      have h1 := congr_arg Matrix.det hmul
      rw [Matrix.det_mul, Matrix.det_one, hdet, mul_zero] at h1
      exact zero_ne_one h1
    obtain ⟨c, hc_mem, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hGGt : (G * Gᵀ) *ᵥ c = 0 := hc_mem
    have hdot : dotProduct (Gᵀ *ᵥ c) (Gᵀ *ᵥ c) = 0 := by
      calc dotProduct (Gᵀ *ᵥ c) (Gᵀ *ᵥ c)
          = dotProduct (c ᵥ* G) (Gᵀ *ᵥ c) := by rw [Matrix.mulVec_transpose]
        _ = dotProduct c (G *ᵥ (Gᵀ *ᵥ c)) := by rw [← Matrix.dotProduct_mulVec]
        _ = dotProduct c ((G * Gᵀ) *ᵥ c) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hGGt, dotProduct_zero]
    have hGt : Gᵀ *ᵥ c = 0 := by
      ext j
      have hsum : ∑ k : Fin n, (Gᵀ *ᵥ c) k * (Gᵀ *ᵥ c) k = 0 := hdot
      have hnonneg : ∀ k ∈ Finset.univ, 0 ≤ (Gᵀ *ᵥ c) k * (Gᵀ *ᵥ c) k := fun k _ => mul_self_nonneg _
      have hj := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum j (Finset.mem_univ j)
      exact mul_self_eq_zero.mp hj
    have hcomb : ∑ i : Fin m, c i • WithLp.toLp 2 (G i) = 0 := by
      ext j
      have hj := congr_fun hGt j
      simpa [Matrix.mulVec, dotProduct, mul_comm] using hj
    have hc0 : ∀ i, c i = 0 := (Fintype.linearIndependent_iff.mp hli) c hcomb
    exact hc_ne (funext hc0)

private lemma measurable_matrix_det {m : ℕ} :
    Measurable (fun A : Fin m → Fin m → ℝ => (Matrix.of A).det) := by
  have hcont : Continuous (fun A : Fin m → Fin m → ℝ => (Matrix.of A).det) := by
    simp_rw [Matrix.det_apply, Matrix.of_apply]
    fun_prop
  exact hcont.measurable

private lemma measurable_matrix_inv_entry {m : ℕ} (i j : Fin m) :
    Measurable (fun A : Fin m → Fin m → ℝ => (Matrix.of A)⁻¹ i j) := by
  have h : (fun A : Fin m → Fin m → ℝ => (Matrix.of A)⁻¹ i j) =
      fun A => ((Matrix.of A).det)⁻¹ * (Matrix.of A).adjugate i j := by
    ext A
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine (measurable_matrix_det.inv).mul ?_
  have hcont : Continuous (fun A : Fin m → Fin m → ℝ => (Matrix.of A).adjugate i j) := by
    simp_rw [Matrix.adjugate_apply, Matrix.det_apply, Matrix.updateRow_apply, Matrix.of_apply]
    refine continuous_finsetSum _ fun σ _ => Continuous.const_smul ?_ _
    refine continuous_finsetProd _ fun k _ => ?_
    by_cases hk : σ k = j
    · simp only [hk, ↓reduceIte]
      exact continuous_const
    · simp only [hk, ↓reduceIte]
      exact (continuous_apply k).comp (continuous_apply (σ k))
  exact hcont.measurable

private lemma measurable_gram {m n : ℕ} :
    Measurable (fun G : Fin m → Fin n → ℝ =>
      (fun i j : Fin m => (Matrix.of G * (Matrix.of G)ᵀ) i j)) := by
  rw [measurable_pi_iff]; intro i; rw [measurable_pi_iff]; intro j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  fun_prop

private lemma gaussianMatrix_ae_det_ne_zero {m n : ℕ} (hmn : m ≤ n) :
    ∀ᵐ G ∂gaussianMatrix m n, (Matrix.of G * (Matrix.of G)ᵀ).det ≠ 0 := by
  induction m with
  | zero =>
    refine ae_of_all _ fun G => ?_
    simp
  | succ m ih =>
    have hdet_meas : Measurable (fun G : Fin (m + 1) → Fin n → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ).det) :=
      measurable_matrix_det.comp measurable_gram
    have hmeas_set : MeasurableSet {G : Fin (m + 1) → Fin n → ℝ |
        (Matrix.of G * (Matrix.of G)ᵀ).det ≠ 0} :=
      (measurableSet_singleton (0 : ℝ)).compl.preimage hdet_meas
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin n → ℝ) 0
    have hmp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (m + 1) => Measure.pi (fun _ : Fin n => gaussianReal 0 1)) 0
    have hmap_eq : gaussianMatrix (m + 1) n =
        ((gaussianMatrix m n).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))).map
          (⇑e.symm ∘ Prod.swap) := by
      have hswap : ((gaussianMatrix m n).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))).map
          Prod.swap = (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussianMatrix m n) :=
        Measure.prod_swap
      rw [← Measure.map_map e.symm.measurable measurable_swap, hswap]
      unfold gaussianMatrix
      exact hmp.symm.map_eq.symm
    rw [hmap_eq]
    refine (ae_map_iff (e.symm.measurable.comp measurable_swap).aemeasurable hmeas_set).mpr ?_
    refine (Measure.ae_prod_iff_ae_ae
      (hmeas_set.preimage (e.symm.measurable.comp measurable_swap))).mpr ?_
    filter_upwards [ih (Nat.le_of_succ_le hmn)] with G' hG'
    have hliG' : LinearIndependent ℝ (fun i : Fin m => WithLp.toLp 2 (G' i)) :=
      (det_mul_transpose_ne_zero_iff_linearIndependent (Matrix.of G')).mp hG'
    let V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
      Submodule.span ℝ (Set.range (fun i : Fin m => WithLp.toLp 2 (G' i)))
    have hV_ne_top : V ≠ ⊤ := by
      intro htop
      have h1 : Module.finrank ℝ V ≤ m := by
        calc Module.finrank ℝ V
            ≤ (Set.range (fun i : Fin m => WithLp.toLp 2 (G' i))).toFinset.card :=
              finrank_span_le_card _
          _ ≤ Fintype.card (Fin m) := by
              rw [Set.toFinset_range]
              exact Finset.card_image_le
          _ = m := Fintype.card_fin m
      rw [htop, finrank_top, finrank_euclideanSpace_fin] at h1
      omega
    have hae_r : ∀ᵐ r ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1)),
        WithLp.toLp 2 r ∉ (V : Set (EuclideanSpace ℝ (Fin n))) := by
      have hzero : (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
          ((WithLp.toLp 2) ⁻¹' (V : Set (EuclideanSpace ℝ (Fin n)))) = 0 := by
        rw [← Measure.map_apply (by fun_prop) (V.closed_of_finiteDimensional.measurableSet),
          map_pi_eq_stdGaussian, stdGaussian_proper_submodule_eq_zero V hV_ne_top]
      rw [ae_iff]
      convert hzero using 2
      ext a
      simp
    filter_upwards [hae_r] with r hr
    show (Matrix.of (e.symm (r, G')) * (Matrix.of (e.symm (r, G')))ᵀ).det ≠ 0
    rw [det_mul_transpose_ne_zero_iff_linearIndependent]
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hcons : ∀ k : Fin (m + 1),
        Matrix.of (e.symm (r, G')) k = Fin.cons (α := fun _ => Fin n → ℝ) r G' k := by
      intro k
      funext j
      change e.symm (r, G') k j = Fin.cons (α := fun _ => Fin n → ℝ) r G' k j
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    have hc' : c 0 • WithLp.toLp 2 r + ∑ i : Fin m, c i.succ • WithLp.toLp 2 (G' i) = 0 := by
      rw [Fin.sum_univ_succ] at hc
      simpa [hcons] using hc
    have hc0 : c 0 = 0 := by
      by_contra hne
      have hmem : WithLp.toLp 2 r ∈ V := by
        have heq : WithLp.toLp 2 r =
            (-(c 0)⁻¹) • ∑ i : Fin m, c i.succ • WithLp.toLp 2 (G' i) := by
          have : c 0 • WithLp.toLp 2 r = -(∑ i : Fin m, c i.succ • WithLp.toLp 2 (G' i)) :=
            eq_neg_of_add_eq_zero_left hc'
          calc WithLp.toLp 2 r = (c 0)⁻¹ • (c 0 • WithLp.toLp 2 r) := by
                rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
            _ = (c 0)⁻¹ • (-(∑ i : Fin m, c i.succ • WithLp.toLp 2 (G' i))) := by rw [this]
            _ = (-(c 0)⁻¹) • ∑ i : Fin m, c i.succ • WithLp.toLp 2 (G' i) := by simp [smul_neg]
        rw [heq]
        refine V.smul_mem _ (V.sum_mem fun i _ => V.smul_mem _ ?_)
        exact Submodule.subset_span ⟨i, rfl⟩
      exact hr hmem
    have hrest : ∀ i : Fin m, c i.succ = 0 := by
      rw [hc0, zero_smul, zero_add] at hc'
      exact Fintype.linearIndependent_iff.mp hliG' (fun i => c i.succ) hc'
    intro k
    refine Fin.cases hc0 hrest k

private noncomputable def pAlg {m n : ℕ} (G : Fin m → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  let M : Matrix (Fin m) (Fin n) ℝ := Matrix.of G
  x - Matrix.toEuclideanLin (Mᵀ * (M * Mᵀ)⁻¹ * M) x

private lemma p_eq_pAlg_of_det_ne_zero {m n : ℕ} {G : Fin m → Fin n → ℝ}
    (hdet : (Matrix.of G * (Matrix.of G)ᵀ).det ≠ 0) (x : EuclideanSpace ℝ (Fin n)) :
    p m n G x = pAlg G x := by
  let M : Matrix (Fin m) (Fin n) ℝ := Matrix.of G
  have hunit : IsUnit (M * Mᵀ).det := isUnit_iff_ne_zero.mpr hdet
  have hmul : (M * Mᵀ) * (M * Mᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hmem : pAlg G x ∈ kernel m n G := by
    show Matrix.toEuclideanLin M (pAlg G x) = 0
    simp only [pAlg, M, map_sub]
    have h1 : Matrix.toEuclideanLin M (Matrix.toEuclideanLin (Mᵀ * (M * Mᵀ)⁻¹ * M) x) =
        Matrix.toEuclideanLin M x := by
      ext i
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
      have hmulvec : M *ᵥ ((Mᵀ * (M * Mᵀ)⁻¹ * M) *ᵥ x.ofLp) = M *ᵥ x.ofLp := by
        rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hmul, Matrix.one_mul]
      exact congr_fun hmulvec i
    rw [h1, sub_self]
  have horth : ∀ w ∈ kernel m n G, ⟪x - pAlg G x, w⟫ = 0 := by
    intro w hw
    have hMw : M *ᵥ w.ofLp = 0 := by
      ext i
      exact congr_fun (congr_arg WithLp.ofLp hw) i
    have hsub : x - pAlg G x = Matrix.toEuclideanLin (Mᵀ * (M * Mᵀ)⁻¹ * M) x := by
      simp [pAlg, M]
    rw [hsub, PiLp.inner_apply]
    have hinner : ∑ j : Fin n, ⟪(Matrix.toEuclideanLin (Mᵀ * (M * Mᵀ)⁻¹ * M) x) j, w j⟫ =
        dotProduct w.ofLp ((Mᵀ * ((M * Mᵀ)⁻¹ * M)) *ᵥ x.ofLp) := by
      simp only [RCLike.inner_apply, conj_trivial, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.mul_assoc, dotProduct]
    rw [hinner, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      hMw, zero_dotProduct]
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem horth

private lemma finrank_kernel_of_det_ne_zero {m n d : ℕ} (hdm : d + m = n)
    {G : Fin m → Fin n → ℝ} (hdet : (Matrix.of G * (Matrix.of G)ᵀ).det ≠ 0) :
    Module.finrank ℝ (kernel m n G) = d := by
  let M : Matrix (Fin m) (Fin n) ℝ := Matrix.of G
  have hunit : IsUnit (M * Mᵀ).det := isUnit_iff_ne_zero.mpr hdet
  have hmul : (M * Mᵀ) * (M * Mᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hsurj : Function.Surjective (Matrix.toEuclideanLin M) := by
    intro y
    refine ⟨Matrix.toEuclideanLin (Mᵀ * (M * Mᵀ)⁻¹) y, ?_⟩
    ext i
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    have hmv : M *ᵥ ((Mᵀ * (M * Mᵀ)⁻¹) *ᵥ y.ofLp) = y.ofLp := by
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hmul, Matrix.one_mulVec]
    exact congr_fun hmv i
  have hrange : LinearMap.range (Matrix.toEuclideanLin M) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin M)
  rw [hrange, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at hrn
  change m + Module.finrank ℝ (kernel m n G) = n at hrn
  omega

private lemma measurable_pAlg {m n : ℕ} :
    Measurable (fun q : (Fin m → Fin n → ℝ) × EuclideanSpace ℝ (Fin n) => pAlg q.1 q.2) := by
  have hcoord : ∀ j : Fin n,
      Measurable (fun q : (Fin m → Fin n → ℝ) × EuclideanSpace ℝ (Fin n) => (pAlg q.1 q.2) j) := by
    intro j
    have heq : (fun q : (Fin m → Fin n → ℝ) × EuclideanSpace ℝ (Fin n) => (pAlg q.1 q.2) j) =
        fun q => q.2 j - ∑ k : Fin n,
          (∑ b : Fin m, (∑ a : Fin m, q.1 a j * (Matrix.of q.1 * (Matrix.of q.1)ᵀ)⁻¹ a b) *
            q.1 b k) * q.2 k := by
      ext ⟨G, x⟩
      simp only [pAlg, PiLp.sub_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
        dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [heq]
    have hGGt_inv : ∀ a b : Fin m,
        Measurable (fun G : Fin m → Fin n → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ a b) :=
      fun a b => (measurable_matrix_inv_entry a b).comp measurable_gram
    have hx : ∀ k : Fin n, Measurable (fun q : (Fin m → Fin n → ℝ) × EuclideanSpace ℝ (Fin n) => q.2 k) :=
      fun k => (EuclideanSpace.proj k).continuous.measurable.comp measurable_snd
    refine (hx j).sub (Finset.measurable_sum _ fun k _ => ?_)
    refine (Finset.measurable_sum _ fun b _ => ?_).mul (hx k)
    have hG2 : Measurable (fun q : (Fin m → Fin n → ℝ) × EuclideanSpace ℝ (Fin n) => q.1 b k) :=
      (measurable_pi_apply k).comp ((measurable_pi_apply b).comp measurable_fst)
    refine (Finset.measurable_sum _ fun a _ => ?_).mul hG2
    have hG1 : Measurable (fun q : (Fin m → Fin n → ℝ) × EuclideanSpace ℝ (Fin n) => q.1 a j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply a).comp measurable_fst)
    exact hG1.mul ((hGGt_inv a b).comp measurable_fst)
  have htoLp : (fun q : (Fin m → Fin n → ℝ) × EuclideanSpace ℝ (Fin n) => pAlg q.1 q.2) =
      WithLp.toLp 2 ∘ (fun q j => (pAlg q.1 q.2) j) := by
    ext q j; rfl
  rw [htoLp]
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ hcoord)

end GaussianSubspace

section OrthogonalInvariance

private noncomputable def rightComp {m n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (G : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i => WithLp.ofLp (Q.symm (WithLp.toLp 2 (G i)))

private lemma measurePreserving_rightComp {m n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (rightComp (m := m) Q) (gaussianMatrix m n) (gaussianMatrix m n) := by
  let f : (Fin n → ℝ) → (Fin n → ℝ) := fun r => WithLp.ofLp (Q.symm (WithLp.toLp 2 r))
  have hf_meas : Measurable f :=
    (PiLp.continuous_ofLp 2 _).measurable.comp
      (Q.symm.continuous.measurable.comp (PiLp.continuous_toLp 2 _).measurable)
  have hf_mp : MeasurePreserving f
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    refine ⟨hf_meas, ?_⟩
    have h1 : (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map f =
        (((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (WithLp.toLp 2)).map Q.symm).map
          WithLp.ofLp := by
      rw [Measure.map_map (PiLp.continuous_ofLp 2 _).measurable Q.symm.continuous.measurable,
        Measure.map_map ((PiLp.continuous_ofLp 2 _).measurable.comp Q.symm.continuous.measurable)
          (PiLp.continuous_toLp 2 _).measurable]
      rfl
    rw [h1, map_pi_eq_stdGaussian, stdGaussian_map Q.symm, ← map_pi_eq_stdGaussian,
      Measure.map_map (PiLp.continuous_ofLp 2 _).measurable (PiLp.continuous_toLp 2 _).measurable]
    have hid : (WithLp.ofLp (p := 2) (V := Fin n → ℝ)) ∘ WithLp.toLp 2 = id := rfl
    rw [hid, Measure.map_id]
  exact measurePreserving_pi _ _ (fun _ => hf_mp)

private lemma toEuclideanLin_rightComp {m n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (G : Fin m → Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (Matrix.of (rightComp Q G)) x =
      Matrix.toEuclideanLin (Matrix.of G) (Q x) := by
  ext i
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply, rightComp]
  have h1 : ∑ j : Fin n, (Q.symm (WithLp.toLp 2 (G i))) j * x j =
      ⟪Q.symm (WithLp.toLp 2 (G i)), x⟫ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => by simp [mul_comm]
  have h2 : ∑ j : Fin n, G i j * (Q x) j = ⟪WithLp.toLp 2 (G i), Q x⟫ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => by simp [mul_comm]
  rw [h1, h2]
  simpa using (Q.inner_map_map (Q.symm (WithLp.toLp 2 (G i))) x).symm

private lemma p_rightComp {m n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (G : Fin m → Fin n → ℝ) (r : EuclideanSpace ℝ (Fin n)) :
    p m n (rightComp Q G) r = Q.symm (p m n G (Q r)) := by
  have hmem : Q.symm (p m n G (Q r)) ∈ kernel m n (rightComp Q G) := by
    show Matrix.toEuclideanLin (Matrix.of (rightComp Q G)) (Q.symm (p m n G (Q r))) = 0
    rw [toEuclideanLin_rightComp, LinearIsometryEquiv.apply_symm_apply]
    exact Submodule.coe_mem ((kernel m n G).orthogonalProjectionOnto (Q r))
  have horth : ∀ w ∈ kernel m n (rightComp Q G), ⟪r - Q.symm (p m n G (Q r)), w⟫ = 0 := by
    intro w hw
    have hQw : Q w ∈ kernel m n G := by
      show Matrix.toEuclideanLin (Matrix.of G) (Q w) = 0
      rw [← toEuclideanLin_rightComp]
      exact hw
    rw [← Q.inner_map_map, map_sub, LinearIsometryEquiv.apply_symm_apply]
    exact Submodule.starProjection_inner_eq_zero (Q r) (Q w) hQw
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem horth

end OrthogonalInvariance

section BetaLaw

private lemma stdGaussian_proj_ratio_eq_beta {n d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hdm : d + m = n) (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : Module.finrank ℝ K = d) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map
      (fun x => ‖K.starProjection x‖ ^ 2 / ‖x‖ ^ 2) =
      betaMeasure ((d : ℝ) / 2) ((m : ℝ) / 2) := by
  have hKorth : Module.finrank ℝ Kᗮ = m := by
    have hsum := Submodule.finrank_add_finrank_orthogonal K
    rw [hK, finrank_euclideanSpace_fin] at hsum
    omega
  let b₁ : OrthonormalBasis (Fin d) ℝ K := (stdOrthonormalBasis ℝ K).reindex (finCongr hK)
  let b₂ : OrthonormalBasis (Fin m) ℝ Kᗮ := (stdOrthonormalBasis ℝ Kᗮ).reindex (finCongr hKorth)
  let Φ : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
    fun p => (b₁.repr.symm p.1 : EuclideanSpace ℝ (Fin n)) +
      (b₂.repr.symm p.2 : EuclideanSpace ℝ (Fin n))
  have hΦ_meas : Measurable Φ := by
    have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin d) =>
        (b₁.repr.symm y : EuclideanSpace ℝ (Fin n))) :=
      continuous_subtype_val.comp b₁.repr.symm.continuous
    have h2 : Continuous (fun z : EuclideanSpace ℝ (Fin m) =>
        (b₂.repr.symm z : EuclideanSpace ℝ (Fin n))) :=
      continuous_subtype_val.comp b₂.repr.symm.continuous
    exact ((h1.comp continuous_fst).add (h2.comp continuous_snd)).measurable
  have hΦ_map :
      ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod (stdGaussian (EuclideanSpace ℝ (Fin m)))).map Φ =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    apply Measure.ext_of_charFun
    ext t
    rw [charFun_stdGaussian, charFun_apply, integral_map hΦ_meas.aemeasurable (by fun_prop)]
    have hinner : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m),
        ⟪Φ p, t⟫ =
          ⟪p.1, b₁.repr (K.orthogonalProjectionOnto t)⟫ +
          ⟪p.2, b₂.repr (Kᗮ.orthogonalProjectionOnto t)⟫ := by
      intro ⟨y, z⟩
      simp only [Φ, inner_add_left]
      congr 1
      · have h1 : ⟪(b₁.repr.symm y : EuclideanSpace ℝ (Fin n)), t⟫ =
            ⟪b₁.repr.symm y, K.orthogonalProjectionOnto t⟫ := by
          have h0 := Submodule.starProjection_inner_eq_zero t
            (b₁.repr.symm y : EuclideanSpace ℝ (Fin n)) (b₁.repr.symm y).2
          rw [inner_sub_left, sub_eq_zero] at h0
          rw [real_inner_comm, h0, real_inner_comm]
          rfl
        rw [h1, ← b₁.repr.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
      · have h2 : ⟪(b₂.repr.symm z : EuclideanSpace ℝ (Fin n)), t⟫ =
            ⟪b₂.repr.symm z, Kᗮ.orthogonalProjectionOnto t⟫ := by
          have h0 := Submodule.starProjection_inner_eq_zero t
            (b₂.repr.symm z : EuclideanSpace ℝ (Fin n)) (b₂.repr.symm z).2
          rw [inner_sub_left, sub_eq_zero] at h0
          rw [real_inner_comm, h0, real_inner_comm]
          rfl
        rw [h2, ← b₂.repr.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
    have hsplit : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) =>
        Complex.exp (↑⟪Φ p, t⟫ * Complex.I)) =
        fun p =>
          Complex.exp (↑⟪p.1, b₁.repr (K.orthogonalProjectionOnto t)⟫ * Complex.I) *
          Complex.exp (↑⟪p.2, b₂.repr (Kᗮ.orthogonalProjectionOnto t)⟫ * Complex.I) := by
      ext p
      rw [hinner p, Complex.ofReal_add, add_mul, Complex.exp_add]
    rw [hsplit]
    have hint_prod : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) =>
        Complex.exp (↑⟪p.1, b₁.repr (K.orthogonalProjectionOnto t)⟫ * Complex.I) *
        Complex.exp (↑⟪p.2, b₂.repr (Kᗮ.orthogonalProjectionOnto t)⟫ * Complex.I))
        ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod (stdGaussian (EuclideanSpace ℝ (Fin m)))) := by
      refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun p => ?_)
      simp [Complex.norm_exp_ofReal_mul_I]
    rw [integral_prod _ hint_prod]
    simp_rw [integral_const_mul, ← charFun_apply, integral_mul_const, ← charFun_apply,
      charFun_stdGaussian, ← Complex.exp_add]
    congr 1
    have hnorm1 : ‖b₁.repr (K.orthogonalProjectionOnto t)‖ = ‖K.starProjection t‖ :=
      b₁.repr.norm_map (K.orthogonalProjectionOnto t)
    have hnorm2 : ‖b₂.repr (Kᗮ.orthogonalProjectionOnto t)‖ = ‖Kᗮ.starProjection t‖ :=
      b₂.repr.norm_map (Kᗮ.orthogonalProjectionOnto t)
    have hpyth : ‖K.starProjection t‖ ^ 2 + ‖Kᗮ.starProjection t‖ ^ 2 = ‖t‖ ^ 2 := by
      have hsum : K.starProjection t + Kᗮ.starProjection t = t := by
        rw [Submodule.starProjection_orthogonal_val, add_sub_cancel]
      have horth : ⟪K.starProjection t, Kᗮ.starProjection t⟫ = 0 :=
        Submodule.inner_right_of_mem_orthogonal
          (Submodule.coe_mem (K.orthogonalProjectionOnto t))
          (Submodule.coe_mem (Kᗮ.orthogonalProjectionOnto t))
      calc ‖K.starProjection t‖ ^ 2 + ‖Kᗮ.starProjection t‖ ^ 2
          = ‖K.starProjection t + Kᗮ.starProjection t‖ ^ 2 := by
            rw [norm_add_sq_real, horth]; ring
        _ = ‖t‖ ^ 2 := by rw [hsum]
    rw [hnorm1, hnorm2]
    have hpythC : ((‖K.starProjection t‖ ^ 2 : ℝ) : ℂ) + ((‖Kᗮ.starProjection t‖ ^ 2 : ℝ) : ℂ) =
        ((‖t‖ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast hpyth
    push_cast at hpythC ⊢
    linear_combination -hpythC / 2
  rw [← hΦ_map, Measure.map_map (by fun_prop) hΦ_meas]
  have hcomp : (fun x => ‖K.starProjection x‖ ^ 2 / ‖x‖ ^ 2) ∘ Φ =
      (fun q : ℝ × ℝ => q.1 / (q.1 + q.2)) ∘
        Prod.map (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ 2)
                 (fun z : EuclideanSpace ℝ (Fin m) => ‖z‖ ^ 2) := by
    ext ⟨y, z⟩
    simp only [Function.comp_apply, Prod.map_apply]
    have hproj : K.starProjection (Φ (y, z)) = (b₁.repr.symm y : EuclideanSpace ℝ (Fin n)) :=
      Submodule.eq_starProjection_of_mem_orthogonal' (b₁.repr.symm y).2 (b₂.repr.symm z).2 rfl
    have horth : ⟪(b₁.repr.symm y : EuclideanSpace ℝ (Fin n)),
        (b₂.repr.symm z : EuclideanSpace ℝ (Fin n))⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (b₁.repr.symm y).2 (b₂.repr.symm z).2
    have hnormΦ : ‖Φ (y, z)‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
      simp only [Φ, norm_add_sq_real, horth, mul_zero, add_zero]
      change ‖b₁.repr.symm y‖ ^ 2 + ‖b₂.repr.symm z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2
      rw [b₁.repr.symm.norm_map, b₂.repr.symm.norm_map]
    rw [hproj, hnormΦ]
    change ‖b₁.repr.symm y‖ ^ 2 / (‖y‖ ^ 2 + ‖z‖ ^ 2) = ‖y‖ ^ 2 / (‖y‖ ^ 2 + ‖z‖ ^ 2)
    rw [b₁.repr.symm.norm_map]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    stdGaussian_norm_sq_eq_gamma hd, stdGaussian_norm_sq_eq_gamma hm,
    gamma_div_add_gamma (by positivity) (by positivity) (by positivity)]

private lemma half_one_add_zeta_eq_norm_sq {n m : ℕ} (F : Frame n) (G : Fin m → Fin n → ℝ) :
    (1 + zeta F G) / 2 = ‖p m n G F.g‖ ^ 2 := by
  have hp2 : p m n G (2 • F.g) = (2 : ℝ) • p m n G F.g := by
    simp only [p, show (2 : ℕ) • F.g = (2 : ℝ) • F.g by norm_cast, map_smul]
  have h1 : (1 + zeta F G) / 2 = ⟪p m n G F.g, F.g⟫ := by
    simp only [zeta, hp2, real_inner_smul_left]
    ring
  rw [h1]
  have horth : ⟪p m n G F.g, F.g - p m n G F.g⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero F.g (p m n G F.g)
      (Submodule.coe_mem ((kernel m n G).orthogonalProjectionOnto F.g))
  have hinner : ⟪p m n G F.g, F.g⟫ = ⟪p m n G F.g, p m n G F.g⟫ := by
    rw [inner_sub_right] at horth
    linarith
  rw [hinner, real_inner_self_eq_norm_sq]

private lemma beta_law_zeta {n d m : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hdm : d + m = n) (F : Frame n) :
    (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2) =
      betaMeasure ((d : ℝ) / 2) ((m : ℝ) / 2) := by
  have hmn : m ≤ n := by omega
  have hae_det := gaussianMatrix_ae_det_ne_zero (m := m) (n := n) hmn
  have hae_eq : (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2) =ᵐ[gaussianMatrix m n]
      (fun G => ‖pAlg G F.g‖ ^ 2) := by
    filter_upwards [hae_det] with G hdet
    rw [half_one_add_zeta_eq_norm_sq, p_eq_pAlg_of_det_ne_zero hdet]
  rw [Measure.map_congr hae_eq]
  ext A hA
  have hpAlg_g : Measurable (fun G : Fin m → Fin n → ℝ => ‖pAlg G F.g‖ ^ 2) :=
    (measurable_pAlg.comp (measurable_id.prodMk measurable_const)).norm.pow_const 2
  rw [Measure.map_apply hpAlg_g hA, ← lintegral_indicator_one (hA.preimage hpAlg_g)]
  have hLHS : ∫⁻ G, ((fun G => ‖pAlg G F.g‖ ^ 2) ⁻¹' A).indicator 1 G ∂gaussianMatrix m n =
      ∫⁻ G, A.indicator 1 (‖pAlg G F.g‖ ^ 2) ∂gaussianMatrix m n := by
    refine lintegral_congr fun G => ?_
    by_cases hG : ‖pAlg G F.g‖ ^ 2 ∈ A <;> simp [Set.indicator, hG]
  rw [hLHS]
  let φ : (Fin m → Fin n → ℝ) → EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun G x => A.indicator 1 (‖pAlg G x‖ ^ 2 / ‖x‖ ^ 2)
  have hφ_meas : Measurable (Function.uncurry φ) := by
    have h1 : Measurable (fun q : (Fin m → Fin n → ℝ) × EuclideanSpace ℝ (Fin n) =>
        ‖pAlg q.1 q.2‖ ^ 2 / ‖q.2‖ ^ 2) :=
      (measurable_pAlg.norm.pow_const 2).div (measurable_snd.norm.pow_const 2)
    exact (measurable_const.indicator hA).comp h1
  -- For every nonzero x, ∫⁻ G, φ G x = ∫⁻ G, A.indicator 1 (‖pAlg G F.g‖ ^ 2)
  have hconst_x : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      ∫⁻ G, φ G x ∂gaussianMatrix m n =
      ∫⁻ G, A.indicator 1 (‖pAlg G F.g‖ ^ 2) ∂gaussianMatrix m n := by
    intro x hx
    let u : EuclideanSpace ℝ (Fin n) := ‖x‖⁻¹ • x
    have hu_norm : ‖u‖ = 1 := by
      simp [u, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    let Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
      Submodule.reflection (ℝ ∙ (F.g - u))ᗮ
    have hQg : Q F.g = u := Submodule.reflection_sub (by rw [F.g_unit, hu_norm])
    have hmp := measurePreserving_rightComp (m := m) Q
    have hae_det_Q : ∀ᵐ G ∂gaussianMatrix m n,
        (Matrix.of (rightComp Q G) * (Matrix.of (rightComp Q G))ᵀ).det ≠ 0 := by
      have hmeas_det : MeasurableSet {G : Fin m → Fin n → ℝ |
          (Matrix.of G * (Matrix.of G)ᵀ).det ≠ 0} :=
        (measurableSet_singleton 0).compl.preimage (measurable_matrix_det.comp measurable_gram)
      have h := ae_map_iff (μ := gaussianMatrix m n) hmp.measurable.aemeasurable hmeas_det
      rw [hmp.map_eq] at h
      exact h.mp hae_det
    have hae_eq_x : (fun G => φ G x) =ᵐ[gaussianMatrix m n]
        (fun G => A.indicator 1 (‖pAlg (rightComp Q G) F.g‖ ^ 2)) := by
      filter_upwards [hae_det, hae_det_Q] with G hdet hdetQ
      simp only [φ]
      rw [← p_eq_pAlg_of_det_ne_zero hdet x, ← p_eq_pAlg_of_det_ne_zero hdetQ F.g,
        p_rightComp, hQg, LinearIsometryEquiv.norm_map]
      congr 1
      have hsmul : p m n G u = ‖x‖⁻¹ • p m n G x := by
        simp [p, u, map_smul]
      rw [hsmul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        mul_pow, inv_pow, div_eq_inv_mul]
    rw [lintegral_congr_ae hae_eq_x]
    have hmeas_g : Measurable (fun G : Fin m → Fin n → ℝ =>
        A.indicator (1 : ℝ → ℝ≥0∞) (‖pAlg G F.g‖ ^ 2)) :=
      (measurable_const.indicator hA).comp hpAlg_g
    exact hmp.lintegral_comp hmeas_g
  -- Integrate over x ~ stdGaussian (ℝ^n)
  have hae_x_ne : ∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ (Fin n)), x ≠ 0 := by
    rw [ae_iff]
    simpa using stdGaussian_singleton_zero (k := n) (by omega)
  have havg : ∫⁻ G, A.indicator 1 (‖pAlg G F.g‖ ^ 2) ∂gaussianMatrix m n =
      ∫⁻ x, (∫⁻ G, φ G x ∂gaussianMatrix m n) ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    have h1 : ∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ (Fin n)),
        ∫⁻ G, φ G x ∂gaussianMatrix m n =
        ∫⁻ G, A.indicator 1 (‖pAlg G F.g‖ ^ 2) ∂gaussianMatrix m n := by
      filter_upwards [hae_x_ne] with x hx
      exact hconst_x x hx
    rw [lintegral_congr_ae h1, lintegral_const, measure_univ, mul_one]
  rw [havg, ← lintegral_lintegral_swap hφ_meas.aemeasurable]
  -- Evaluate inner integral over x for a.e. G (with det (G * Gᵀ) ≠ 0)
  have hinner_G : ∀ᵐ G ∂gaussianMatrix m n,
      ∫⁻ x, φ G x ∂stdGaussian (EuclideanSpace ℝ (Fin n)) =
      betaMeasure ((d : ℝ) / 2) ((m : ℝ) / 2) A := by
    filter_upwards [hae_det] with G hdet
    have hK : Module.finrank ℝ (kernel m n G) = d := finrank_kernel_of_det_ne_zero hdm hdet
    have hfun : (fun x => φ G x) =
        fun x => ((fun x => ‖(kernel m n G).starProjection x‖ ^ 2 / ‖x‖ ^ 2) ⁻¹' A).indicator 1 x := by
      ext x
      have hpG : pAlg G x = (kernel m n G).starProjection x := (p_eq_pAlg_of_det_ne_zero hdet x).symm
      by_cases hxA : ‖(kernel m n G).starProjection x‖ ^ 2 / ‖x‖ ^ 2 ∈ A <;>
        simp [φ, hpG, Set.indicator, hxA]
    rw [hfun, lintegral_indicator_one (hA.preimage (by fun_prop)),
      ← Measure.map_apply (by fun_prop) hA,
      stdGaussian_proj_ratio_eq_beta hd hm hdm (kernel m n G) hK]
  rw [lintegral_congr_ae hinner_G, lintegral_const, measure_univ, mul_one]

end BetaLaw

section GeometryAndSphere

private lemma frame_coord_g {n : ℕ} (F : Frame n) : F.coordinates F.g = 0 := by
  have h := F.decomposition F.g
  have hgg : ⟪F.g, F.g⟫ = 1 := by rw [real_inner_self_eq_norm_sq, F.g_unit]; norm_num
  rw [hgg, one_smul] at h
  have hH : F.H (F.coordinates F.g) = 0 := by
    have := congr_arg (fun y => y - F.g) h
    simpa using this.symm
  have hzero : ‖F.coordinates F.g‖ = 0 := by
    rw [← F.H.norm_map, hH, norm_zero]
  exact norm_eq_zero.mp hzero

private lemma norm_sq_coord_p_eq {n m : ℕ} (F : Frame n) (G : Fin m → Fin n → ℝ) :
    ‖F.coordinates (p m n G (2 • F.g))‖ ^ 2 = 1 - zeta F G ^ 2 := by
  let p₀ := p m n G (2 • F.g)
  let w := F.coordinates p₀
  have hdecomp : p₀ = (1 + zeta F G) • F.g + F.H w := by
    have h := F.decomposition p₀
    have hcoeff : ⟪p₀, F.g⟫ = 1 + zeta F G := by simp [zeta, p₀]
    simpa [hcoeff, w] using h
  have hnorm_decomp : ‖p₀‖ ^ 2 = (1 + zeta F G) ^ 2 + ‖w‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real, real_inner_smul_left, F.g_orthogonal w, mul_zero,
      mul_zero, add_zero, norm_smul, F.g_unit, mul_one, Real.norm_eq_abs, sq_abs, F.H.norm_map]
  have horth : ⟪p₀, 2 • F.g - p₀⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero (2 • F.g) p₀
      (Submodule.coe_mem ((kernel m n G).orthogonalProjectionOnto (2 • F.g)))
  have hnorm_proj : ‖p₀‖ ^ 2 = 2 * (1 + zeta F G) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at horth
    have h2 : ⟪p₀, 2 • F.g⟫ = 2 * ⟪p₀, F.g⟫ := by
      rw [show (2 : ℕ) • F.g = (2 : ℝ) • F.g by norm_cast, real_inner_smul_right]
    have hzeta : ⟪p₀, F.g⟫ = 1 + zeta F G := by simp [zeta, p₀]
    linarith
  linarith

private lemma ae_geometric_decomp {n d m : ℕ} (F : Frame n)
    (hzeta_aem : AEMeasurable (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2) (gaussianMatrix m n))
    (hbeta : (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2) =
      betaMeasure ((d : ℝ) / 2) ((m : ℝ) / 2)) :
    ∀ᵐ G ∂gaussianMatrix m n,
      p m n G (2 • F.g) =
        (1 + zeta F G) • F.g + (eta F G) • F.H (v F G) ∧
      eta F G = Real.sqrt (1 - zeta F G ^ 2) ∧
      ‖v F G‖ = 1 := by
  have hS_meas : MeasurableSet ({(0 : ℝ), 1} : Set ℝ) :=
    (measurableSet_singleton 0).union (measurableSet_singleton 1)
  have hbeta_S : betaMeasure ((d : ℝ) / 2) ((m : ℝ) / 2) ({(0 : ℝ), 1} : Set ℝ) = 0 := by
    rw [betaMeasure, withDensity_apply _ hS_meas, Set.insert_eq,
      lintegral_union (measurableSet_singleton 1) (by simp),
      Measure.restrict_eq_zero.mpr Real.volume_singleton,
      Measure.restrict_eq_zero.mpr Real.volume_singleton]
    simp
  have hae_not_S : ∀ᵐ G : Fin m → Fin n → ℝ ∂gaussianMatrix m n,
      (1 + zeta F G) / 2 ∉ ({(0 : ℝ), 1} : Set ℝ) := by
    have h0 : gaussianMatrix m n
        ((fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2) ⁻¹' ({(0 : ℝ), 1} : Set ℝ)) = 0 := by
      rw [← Measure.map_apply_of_aemeasurable hzeta_aem hS_meas, hbeta, hbeta_S]
    rw [ae_iff]
    convert h0 using 2
    ext G
    simp [imp_iff_not_or]
  filter_upwards [hae_not_S] with G hG
  let p₀ := p m n G (2 • F.g)
  let w := F.coordinates p₀
  have hsq : ‖w‖ ^ 2 = 1 - zeta F G ^ 2 := norm_sq_coord_p_eq F G
  have heta_eq : eta F G = ‖w‖ := by
    rw [eta, ← hsq, Real.sqrt_sq (norm_nonneg w)]
  have hw_ne : ‖w‖ ≠ 0 := by
    intro h0
    rw [h0] at hsq
    have hprod : ((1 + zeta F G) / 2) * (1 - (1 + zeta F G) / 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h1 | h2
    · exact hG (Set.mem_insert_iff.mpr (Or.inl h1))
    · exact hG (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (by linarith)))
  have hv_norm : ‖v F G‖ = 1 := by
    simp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
      inv_mul_cancel₀ hw_ne]
  have hdecomp : p₀ = (1 + zeta F G) • F.g + (eta F G) • F.H (v F G) := by
    have h := F.decomposition p₀
    have hcoeff : ⟪p₀, F.g⟫ = 1 + zeta F G := by simp [zeta, p₀]
    rw [hcoeff] at h
    rw [h]
    congr 1
    simp only [v, p₀, w, heta_eq, map_smul, smul_smul, mul_inv_cancel₀ hw_ne, one_smul]
  exact ⟨hdecomp, rfl, hv_norm⟩

private noncomputable def liftFrame {n : ℕ} (F : Frame n)
    (R : EuclideanSpace ℝ (Fin (n - 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n - 1))) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  { toLinearEquiv :=
      { toFun := fun x => ⟪x, F.g⟫ • F.g + F.H (R (F.coordinates x))
        map_add' := fun x y => by
          simp only [inner_add_left, add_smul, map_add]
          abel
        map_smul' := fun c x => by
          simp only [real_inner_smul_left, smul_smul, map_smul, RingHom.id_apply, smul_add]
        invFun := fun x => ⟪x, F.g⟫ • F.g + F.H (R.symm (F.coordinates x))
        left_inv := fun x => by
          dsimp only
          have hinner : ⟪⟪x, F.g⟫ • F.g + F.H (R (F.coordinates x)), F.g⟫ = ⟪x, F.g⟫ := by
            simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, F.g_unit,
              one_pow, mul_one]
            rw [real_inner_comm F.g (F.H _), F.g_orthogonal, add_zero]
          have hcoord : F.coordinates (⟪x, F.g⟫ • F.g + F.H (R (F.coordinates x))) =
              R (F.coordinates x) := by
            simp only [map_add, map_smul, frame_coord_g, smul_zero, zero_add, F.coordinates_H]
          rw [hinner, hcoord, LinearIsometryEquiv.symm_apply_apply]
          exact (F.decomposition x).symm
        right_inv := fun x => by
          dsimp only
          have hinner : ⟪⟪x, F.g⟫ • F.g + F.H (R.symm (F.coordinates x)), F.g⟫ = ⟪x, F.g⟫ := by
            simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, F.g_unit,
              one_pow, mul_one]
            rw [real_inner_comm F.g (F.H _), F.g_orthogonal, add_zero]
          have hcoord : F.coordinates (⟪x, F.g⟫ • F.g + F.H (R.symm (F.coordinates x))) =
              R.symm (F.coordinates x) := by
            simp only [map_add, map_smul, frame_coord_g, smul_zero, zero_add, F.coordinates_H]
          rw [hinner, hcoord, LinearIsometryEquiv.apply_symm_apply]
          exact (F.decomposition x).symm }
    norm_map' := fun x => by
      change ‖⟪x, F.g⟫ • F.g + F.H (R (F.coordinates x))‖ = ‖x‖
      have h1 : ‖⟪x, F.g⟫ • F.g + F.H (R (F.coordinates x))‖ ^ 2 = ‖x‖ ^ 2 := by
        have hL : ‖⟪x, F.g⟫ • F.g + F.H (R (F.coordinates x))‖ ^ 2 =
            ⟪x, F.g⟫ ^ 2 + ‖F.coordinates x‖ ^ 2 := by
          simp only [norm_add_sq_real, real_inner_smul_left, F.g_orthogonal, mul_zero, add_zero,
            norm_smul, F.g_unit, mul_one, Real.norm_eq_abs, sq_abs, F.H.norm_map, R.norm_map]
        have hR : ‖x‖ ^ 2 = ⟪x, F.g⟫ ^ 2 + ‖F.coordinates x‖ ^ 2 := by
          conv_lhs => rw [F.decomposition x]
          simp only [norm_add_sq_real, real_inner_smul_left, F.g_orthogonal, mul_zero, add_zero,
            norm_smul, F.g_unit, mul_one, Real.norm_eq_abs, sq_abs, F.H.norm_map]
        linarith
      nlinarith [norm_nonneg (⟪x, F.g⟫ • F.g + F.H (R (F.coordinates x))), norm_nonneg x] }

private lemma liftFrame_apply {n : ℕ} (F : Frame n)
    (R : EuclideanSpace ℝ (Fin (n - 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n - 1)))
    (x : EuclideanSpace ℝ (Fin n)) :
    liftFrame F R x = ⟪x, F.g⟫ • F.g + F.H (R (F.coordinates x)) := rfl

private lemma liftFrame_g {n : ℕ} (F : Frame n)
    (R : EuclideanSpace ℝ (Fin (n - 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n - 1))) :
    liftFrame F R F.g = F.g := by
  rw [liftFrame_apply, frame_coord_g, map_zero, map_zero, add_zero,
    real_inner_self_eq_norm_sq, F.g_unit, one_pow, one_smul]

private lemma liftFrame_coordinates {n : ℕ} (F : Frame n)
    (R : EuclideanSpace ℝ (Fin (n - 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n - 1)))
    (x : EuclideanSpace ℝ (Fin n)) :
    F.coordinates (liftFrame F R x) = R (F.coordinates x) := by
  rw [liftFrame_apply, map_add, map_smul, frame_coord_g, smul_zero, zero_add, F.coordinates_H]

private lemma eq_sphereGaussian_of_orthogonal_invariant {k : ℕ} (hk : 1 ≤ k)
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ y ∂μ, ‖y‖ = 1)
    (hinv : ∀ Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k), μ.map Q = μ) :
    μ = sphereGaussian k := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin k))
  let Φ : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
    fun p => ‖p.2‖ • p.1
  have hΦ_meas : Measurable Φ := (measurable_snd.norm).smul measurable_fst
  have hprod_eq : (μ.prod γ).map Φ = γ := by
    apply Measure.ext_of_charFun
    ext t
    rw [charFun_stdGaussian, charFun_apply, integral_map hΦ_meas.aemeasurable (by fun_prop)]
    have hint1 : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        Complex.exp (↑⟪‖p.2‖ • p.1, t⟫ * Complex.I)) (μ.prod γ) := by
      refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun p => ?_)
      simp [Complex.norm_exp_ofReal_mul_I]
    rw [integral_prod_symm _ hint1]
    have hswap_inner : ∀ x : EuclideanSpace ℝ (Fin k),
        ∫ y, Complex.exp (↑⟪‖x‖ • y, t⟫ * Complex.I) ∂μ =
        ∫ y, Complex.exp (↑⟪y, ‖t‖ • x⟫ * Complex.I) ∂μ := by
      intro x
      let u : EuclideanSpace ℝ (Fin k) := ‖x‖ • t
      let w : EuclideanSpace ℝ (Fin k) := ‖t‖ • x
      have huw : ‖u‖ = ‖w‖ := by
        simp [u, w, norm_smul, mul_comm]
      let Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
        Submodule.reflection (ℝ ∙ (u - w))ᗮ
      have hQu : Q u = w := Submodule.reflection_sub huw
      have h1 : ∫ y, Complex.exp (↑⟪‖x‖ • y, t⟫ * Complex.I) ∂μ =
          ∫ y, Complex.exp (↑⟪y, u⟫ * Complex.I) ∂μ := by
        congr 1; ext y; simp [u, real_inner_smul_left, real_inner_smul_right]
      rw [h1]
      conv_lhs => rw [← hinv Q]
      rw [integral_map Q.continuous.measurable.aemeasurable (by fun_prop)]
      congr 1; ext y
      have hinnerQ : ⟪Q y, u⟫ = ⟪y, w⟫ := by
        calc ⟪Q y, u⟫ = ⟪Q (Q y), Q u⟫ := (Q.inner_map_map (Q y) u).symm
          _ = ⟪y, w⟫ := by rw [Submodule.reflection_reflection, hQu]
      rw [hinnerQ]
    simp_rw [hswap_inner]
    have hint2 : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        Complex.exp (↑⟪p.1, ‖t‖ • p.2⟫ * Complex.I)) (μ.prod γ) := by
      refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun p => ?_)
      simp [Complex.norm_exp_ofReal_mul_I]
    rw [← integral_prod_symm _ hint2, integral_prod _ hint2]
    have hinner_γ : ∀ y : EuclideanSpace ℝ (Fin k),
        ∫ x, Complex.exp (↑⟪y, ‖t‖ • x⟫ * Complex.I) ∂γ =
        Complex.exp (-((‖t‖ * ‖y‖ : ℝ) : ℂ) ^ 2 / 2) := by
      intro y
      have heq : (fun x => Complex.exp (↑⟪y, ‖t‖ • x⟫ * Complex.I)) =
          fun x => Complex.exp (↑⟪x, ‖t‖ • y⟫ * Complex.I) := by
        ext x
        rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]
      rw [heq, ← charFun_apply, charFun_stdGaussian]
      simp [norm_smul]
    simp_rw [hinner_γ]
    have hae_exp : (fun y => Complex.exp (-((‖t‖ * ‖y‖ : ℝ) : ℂ) ^ 2 / 2)) =ᵐ[μ]
        (fun _ => Complex.exp (-(‖t‖ : ℂ) ^ 2 / 2)) := by
      filter_upwards [hunit] with y hy
      simp [hy]
    rw [integral_congr_ae hae_exp, integral_const, probReal_univ, one_smul]
  -- Push forward by normalization map ψ z = ‖z‖⁻¹ • z
  let ψ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := fun z => ‖z‖⁻¹ • z
  have hψ_meas : Measurable ψ := (measurable_norm.inv).smul measurable_id
  have hstep : sphereGaussian k = (μ.prod γ).map (ψ ∘ Φ) := by
    calc sphereGaussian k = γ.map ψ := rfl
      _ = ((μ.prod γ).map Φ).map ψ := by rw [hprod_eq]
      _ = (μ.prod γ).map (ψ ∘ Φ) := Measure.map_map hψ_meas hΦ_meas
  have hae_γ : ∀ᵐ x ∂γ, x ≠ 0 := by
    rw [ae_iff]
    simpa [γ] using stdGaussian_singleton_zero hk
  have hae_comp : (ψ ∘ Φ) =ᵐ[μ.prod γ] Prod.fst := by
    have hprod_ae : ∀ᵐ p ∂(μ.prod γ), ‖p.1‖ = 1 ∧ p.2 ≠ 0 :=
      (Measure.quasiMeasurePreserving_fst.ae hunit).and
        (Measure.quasiMeasurePreserving_snd.ae hae_γ)
    filter_upwards [hprod_ae] with ⟨y, x⟩ ⟨hy, hx⟩
    have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp only [Function.comp_apply, ψ, Φ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x), hy, mul_one, smul_smul, inv_mul_cancel₀ hxnorm, one_smul]
  rw [hstep, Measure.map_congr hae_comp, Measure.map_fst_prod, measure_univ, one_smul]

end GeometryAndSphere

theorem solution {n d m : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hdm : d + m = n) (F : Frame n) :
    AEMeasurable (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2)
      (gaussianMatrix m n) ∧
    AEMeasurable (fun G : Fin m → Fin n → ℝ => v F G)
      (gaussianMatrix m n) ∧
    (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2) =
      betaMeasure ((d : ℝ) / 2) ((m : ℝ) / 2) ∧
    (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => v F G) =
      sphereGaussian (n - 1) ∧
    (∀ᵐ G ∂gaussianMatrix m n,
      p m n G (2 • F.g) =
        (1 + zeta F G) • F.g + (eta F G) • F.H (v F G) ∧
      eta F G = Real.sqrt (1 - zeta F G ^ 2) ∧
      ‖v F G‖ = 1) := by
  have hmn : m ≤ n := by omega
  have hae_det := gaussianMatrix_ae_det_ne_zero (m := m) (n := n) hmn
  -- 1. AEMeasurable of p m n · (2 • F.g), zeta, and v
  have hp_aem : AEMeasurable (fun G : Fin m → Fin n → ℝ => p m n G (2 • F.g))
      (gaussianMatrix m n) := by
    refine AEMeasurable.congr (f := fun G => pAlg G (2 • F.g)) ?_ ?_
    · exact (measurable_pAlg.comp (measurable_id.prodMk measurable_const)).aemeasurable
    · filter_upwards [hae_det] with G hdet
      exact (p_eq_pAlg_of_det_ne_zero hdet (2 • F.g)).symm
  have hzeta_aem : AEMeasurable (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2)
      (gaussianMatrix m n) := by
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (1 + (⟪x, F.g⟫ - 1)) / 2) := by
      fun_prop
    exact hcont.measurable.comp_aemeasurable hp_aem
  have hv_aem : AEMeasurable (fun G : Fin m → Fin n → ℝ => v F G) (gaussianMatrix m n) := by
    have hcoord_meas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => F.coordinates x) :=
      F.coordinates.continuous_of_finiteDimensional.measurable
    have hnorm_meas : Measurable (fun w : EuclideanSpace ℝ (Fin (n - 1)) => ‖w‖⁻¹ • w) :=
      (measurable_norm.inv).smul measurable_id
    exact (hnorm_meas.comp hcoord_meas).comp_aemeasurable hp_aem
  -- 2. Beta law
  have hbeta : (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2) =
      betaMeasure ((d : ℝ) / 2) ((m : ℝ) / 2) :=
    beta_law_zeta hn hd hm hdm F
  -- 3. Almost-sure geometric decomposition
  have hae_geom := ae_geometric_decomp F hzeta_aem hbeta
  -- 4. Uniform spherical law
  have hsphere : (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => v F G) =
      sphereGaussian (n - 1) := by
    let μ := (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => v F G)
    have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hv_aem
    have hunit : ∀ᵐ y ∂μ, ‖y‖ = 1 := by
      have hmeas_set : MeasurableSet {y : EuclideanSpace ℝ (Fin (n - 1)) | ‖y‖ = 1} :=
        (measurableSet_singleton (1 : ℝ)).preimage measurable_norm
      exact (ae_map_iff hv_aem hmeas_set).mpr (hae_geom.mono fun G hG => hG.2.2)
    have hinv : ∀ R : EuclideanSpace ℝ (Fin (n - 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n - 1)),
        μ.map R = μ := by
      intro R
      let Q := (liftFrame F R).symm
      have hmp := measurePreserving_rightComp (m := m) Q
      have hv_comp : (fun G : Fin m → Fin n → ℝ => R (v F G)) =
          fun G : Fin m → Fin n → ℝ => v F (rightComp Q G) := by
        ext G
        have hpQ : p m n (rightComp Q G) (2 • F.g) = liftFrame F R (p m n G (2 • F.g)) := by
          rw [p_rightComp]
          have hQg : Q (2 • F.g) = 2 • F.g := by
            have h1 : Q F.g = F.g := by
              apply (liftFrame F R).injective
              simp [Q, liftFrame_g]
            simp [map_nsmul, h1]
          rw [hQg]
          simp [Q]
        simp only [v, hpQ, liftFrame_coordinates, R.norm_map, map_smul]
      show ((gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => v F G)).map R =
        (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => v F G)
      rw [AEMeasurable.map_map_of_aemeasurable R.continuous.measurable.aemeasurable hv_aem]
      change (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => R (v F G)) =
        (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => v F G)
      rw [hv_comp]
      have hv_comp_map :
          (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => v F (rightComp Q G)) =
          ((gaussianMatrix m n).map (rightComp (m := m) Q)).map
            (fun G : Fin m → Fin n → ℝ => v F G) := by
        change (gaussianMatrix m n).map
          ((fun G : Fin m → Fin n → ℝ => v F G) ∘ rightComp (m := m) Q) = _
        exact (AEMeasurable.map_map_of_aemeasurable
          (by rw [hmp.map_eq]; exact hv_aem) hmp.measurable.aemeasurable).symm
      rw [hv_comp_map, hmp.map_eq]
    exact eq_sphereGaussian_of_orthogonal_invariant (by omega) μ hunit hinv
  exact ⟨hzeta_aem, hv_aem, hbeta, hsphere, hae_geom⟩

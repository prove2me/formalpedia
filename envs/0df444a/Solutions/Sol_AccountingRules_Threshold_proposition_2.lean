-- Prove2me | solution 1 for AccountingRules.Threshold.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T04:08:57.5864+00:00
-- url     : https://prove2.me/submissions/f31b3b08-a6fc-4e1d-bc4e-0a26252a438e

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Set

namespace AccProp2Sol

open AccountingRules.Threshold

lemma ae_mem (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) :
    ∀ᵐ θ ∂P, θ ∈ Icc θlo θhi := by
  rw [ae_iff]
  simpa [compl_def] using hS.supp_sub

lemma integrable_of_supp (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ)
    (h : μ (Icc a b)ᶜ = 0) : Integrable (fun θ : ℝ => θ) μ := by
  have hae : ∀ᵐ θ ∂μ, θ ∈ Icc a b := by
    rw [ae_iff]; simpa [compl_def] using h
  refine Integrable.mono' (integrable_const (|a| + |b|)) measurable_id.aestronglyMeasurable ?_
  filter_upwards [hae] with θ hθ
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := hθ.1; have := neg_abs_le a; have := abs_nonneg b; linarith
  · have := hθ.2; have := le_abs_self b; have := abs_nonneg a; linarith

lemma integrable_id (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) :
    Integrable (fun θ : ℝ => θ) P := by
  have := hS.prob
  exact integrable_of_supp P θlo θhi hS.supp_sub

lemma noAtoms (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) :
    NullSingletonClass P := ⟨fun x => hS.density (Real.volume_singleton)⟩

lemma pos_Iio (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (ht : θlo < t) (hlohi : θlo < θhi) : 0 < P (Iio t) := by
  have h := hS.supp_full θlo (min t θhi) le_rfl (lt_min ht hlohi) (min_le_right _ _)
  exact lt_of_lt_of_le h (measure_mono (fun x hx => lt_of_lt_of_le hx.2 (min_le_left _ _)))

lemma pos_Iic (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (ht : θlo < t) (hlohi : θlo < θhi) : 0 < P (Iic t) :=
  lt_of_lt_of_le (pos_Iio P θlo θhi M B hS t ht hlohi) (measure_mono Iio_subset_Iic_self)

lemma pos_Ioi (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (ht : t < θhi) (hlohi : θlo < θhi) : 0 < P (Ioi t) := by
  have h := hS.supp_full (max t θlo) θhi (le_max_right _ _) (max_lt ht hlohi) le_rfl
  exact lt_of_lt_of_le h (measure_mono (fun x hx => lt_of_le_of_lt (le_max_left _ _) hx.1))

/-- `G k t = ∫_{θ ≤ t} (θ - k) dP`. -/
noncomputable def G (P : Measure ℝ) (k t : ℝ) : ℝ := ∫ θ in Iic t, (θ - k) ∂P

lemma G_eq (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k t : ℝ) :
    G P k t = (∫ θ in Iic t, θ ∂P) - k * (P (Iic t)).toReal := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  unfold G
  rw [integral_sub hi.integrableOn (integrable_const k).integrableOn, setIntegral_const,
    smul_eq_mul, measureReal_def, mul_comm]

lemma condMean_id (P : Measure ℝ) (S : Set ℝ) :
    condMean P id S = (∫ θ in S, θ ∂P) / (P S).toReal := rfl

lemma condMean_eq_iff (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k t : ℝ)
    (hpos : 0 < P (Iic t)) : condMean P id (Iic t) = k ↔ G P k t = 0 := by
  have := hS.prob
  have hF : 0 < (P (Iic t)).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  rw [condMean_id, G_eq P θlo θhi M B hS, div_eq_iff hF.ne', sub_eq_zero]

lemma condMean_le_iff (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k t : ℝ)
    (hpos : 0 < P (Iic t)) : condMean P id (Iic t) ≤ k ↔ G P k t ≤ 0 := by
  have := hS.prob
  have hF : 0 < (P (Iic t)).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  rw [condMean_id, G_eq P θlo θhi M B hS, div_le_iff₀ hF, sub_nonpos]

lemma condMean_sub (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (hpos : 0 < P (Iic t)) :
    condMean P (fun θ => M - θ) (Iic t) = M - condMean P id (Iic t) := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hF : 0 < (P (Iic t)).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  unfold condMean
  rw [integral_sub (integrable_const M).integrableOn hi.integrableOn, setIntegral_const,
    smul_eq_mul, measureReal_def]
  simp only [id]
  field_simp

/-- Strictly below the lower end: `G k k < 0` when `θlo < k`. -/
lemma G_self_neg (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k : ℝ)
    (hk : θlo < k) (hlohi : θlo < θhi) : G P k k < 0 := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hint : IntegrableOn (fun θ => k - θ) (Iic k) P :=
    ((integrable_const k).sub hi).integrableOn
  have hpos : 0 < ∫ θ in Iic k, (k - θ) ∂P := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
    · refine lt_of_lt_of_le (pos_Iio P θlo θhi M B hS k hk hlohi) (measure_mono ?_)
      intro x hx
      refine ⟨?_, (show x < k from hx).le⟩
      simp only [Function.mem_support]
      have : x < k := hx
      linarith
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      simp only [Pi.zero_apply]
      have : x ≤ k := hx
      linarith
  have : G P k k = - ∫ θ in Iic k, (k - θ) ∂P := by
    unfold G
    rw [← integral_neg]
    congr 1; ext θ; ring
  linarith

/-- Strict monotonicity of `G k` on `[k, θhi]`. -/
lemma G_strictMono (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k : ℝ)
    (hk : θlo < k) (s t : ℝ) (hks : k ≤ s) (hst : s < t) (hth : t ≤ θhi) :
    G P k s < G P k t := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hfi : Integrable (fun θ => θ - k) P := hi.sub (integrable_const k)
  have hsplit : G P k t = G P k s + ∫ θ in Ioc s t, (θ - k) ∂P := by
    unfold G
    rw [← Iic_union_Ioc_eq_Iic hst.le, setIntegral_union (Iic_disjoint_Ioc le_rfl)
      measurableSet_Ioc hfi.integrableOn hfi.integrableOn]
  have hpos : 0 < ∫ θ in Ioc s t, (θ - k) ∂P := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hfi.integrableOn]
    · have h := hS.supp_full s t (by linarith) hst hth
      refine lt_of_lt_of_le h (measure_mono ?_)
      intro x hx
      refine ⟨?_, hx.1, hx.2.le⟩
      simp only [Function.mem_support]
      have := hx.1
      linarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      simp only [Pi.zero_apply]
      have := hx.1
      linarith
  linarith

lemma G_continuous (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k : ℝ) :
    Continuous (G P k) := by
  have := hS.prob
  have := noAtoms P θlo θhi M B hS
  have hi := integrable_id P θlo θhi M B hS
  have hfi : Integrable (fun θ => θ - k) P := hi.sub (integrable_const k)
  have heq : G P k = fun t => G P k 0 + ∫ θ in (0:ℝ)..t, (θ - k) ∂P := by
    funext t
    unfold G
    rw [← intervalIntegral.integral_Iic_sub_Iic hfi.integrableOn hfi.integrableOn]
    ring
  rw [heq]
  exact continuous_const.add (hfi.continuous_primitive 0)

lemma postMean_eq (μ : Measure ℝ) (h : Integrable (fun θ : ℝ => θ) μ) :
    postMean μ = ∫ θ, θ ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h]; rfl

lemma postMean_cond (P : Measure ℝ) [IsFiniteMeasure P] (hi : Integrable (fun θ : ℝ => θ) P)
    (S : Set ℝ) (hSm : MeasurableSet S) (hpos : 0 < P S) :
    postMean (P[|S]) = condMean P id S := by
  have hne : (P S)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hpos.ne'
  have hint : Integrable (fun θ : ℝ => θ) (P[|S]) := by
    unfold ProbabilityTheory.cond
    exact hi.integrableOn.smul_measure hne
  rw [postMean_eq _ hint, condMean_id]
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul]

lemma regPayoff_nonneg (M B : ℝ) (hM : 0 < M) (hBM : B ≤ M) (μ : Measure ℝ) :
    0 ≤ regPayoff M B μ := by
  unfold regPayoff
  split_ifs with h
  · linarith
  · linarith

lemma measurable_postMean : Measurable postMean := by
  unfold postMean
  refine Measurable.sub ?_ ?_
  · exact (Measure.measurable_lintegral (by fun_prop)).ennreal_toReal
  · exact (Measure.measurable_lintegral (by fun_prop)).ennreal_toReal

lemma measurable_regPayoff (M B : ℝ) : Measurable (regPayoff M B) := by
  unfold regPayoff
  exact Measurable.ite (measurableSet_lt measurable_const measurable_postMean)
    measurable_postMean measurable_const

/-- The Lagrangian integrand. -/
noncomputable def φ (M B lam : ℝ) (θ : ℝ) : ℝ := max θ (M + lam * (M - B - θ))

lemma φ_nonneg (M B lam : ℝ) (hM : 0 < M) (hBM : B ≤ M) (hlam : 0 ≤ lam) (θ : ℝ) :
    0 ≤ φ M B lam θ := by
  unfold φ
  rcases le_total 0 θ with h | h
  · exact le_trans h (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ lam * (M - B - θ) := mul_nonneg hlam (by linarith)
    linarith

lemma φ_continuous (M B lam : ℝ) : Continuous (φ M B lam) := by
  unfold φ; fun_prop

lemma integrable_φ (μ : Measure ℝ) [IsFiniteMeasure μ] (hi : Integrable (fun θ : ℝ => θ) μ)
    (M B lam : ℝ) : Integrable (φ M B lam) μ := by
  have h2 : Integrable (fun θ : ℝ => M + lam * (M - B - θ)) μ :=
    (integrable_const M).add (((integrable_const (M - B)).sub hi).const_mul lam)
  exact hi.sup h2

/-- Pointwise Lagrangian bound for a single posterior. -/
lemma regPayoff_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hi : Integrable (fun θ : ℝ => θ) μ)
    (M B lam : ℝ) (hlam : 0 ≤ lam) :
    regPayoff M B μ ≤ ∫ θ, φ M B lam θ ∂μ := by
  have h2 : Integrable (fun θ : ℝ => M + lam * (M - B - θ)) μ :=
    (integrable_const M).add (((integrable_const (M - B)).sub hi).const_mul lam)
  have hφ := integrable_φ μ hi M B lam
  unfold regPayoff
  rw [postMean_eq μ hi]
  split_ifs with h
  · exact integral_mono hi hφ (fun θ => le_max_left _ _)
  · push_neg at h
    have hle : ∫ θ, (M + lam * (M - B - θ)) ∂μ ≤ ∫ θ, φ M B lam θ ∂μ :=
      integral_mono h2 hφ (fun θ => le_max_right _ _)
    have hcomp : ∫ θ, (M + lam * (M - B - θ)) ∂μ = M + lam * (M - B - ∫ θ, θ ∂μ) := by
      rw [show (∫ θ, (M + lam * (M - B - θ)) ∂μ) = ∫ θ, ((M + lam * (M - B)) - lam * θ) ∂μ from by
          congr 1; ext θ; ring,
        integral_sub (integrable_const _) (hi.const_mul lam), integral_const, integral_const_mul]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      ring
    have : 0 ≤ lam * (M - B - ∫ θ, θ ∂μ) := mul_nonneg hlam (by linarith)
    linarith

/-- Weak duality: every Bayes-plausible policy is bounded by `∫ φ dP`. -/
lemma value_le (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B)
    (lam : ℝ) (hlam : 0 ≤ lam) (τ : Measure (Measure ℝ))
    (hτ : FinDisclosure.Threshold.IsBayesPlausible P τ) :
    value M B τ ≤ ∫ θ, φ M B lam θ ∂P := by
  have := hS.prob
  obtain ⟨hτp, hτae, hjoin⟩ := hτ
  have hM := hS.M_pos
  have hBM := hS.B_le_M
  have hi := integrable_id P θlo θhi M B hS
  set f : ℝ → ENNReal := fun θ => ENNReal.ofReal (φ M B lam θ) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (φ_continuous M B lam).measurable
  set h : Measure ℝ → ℝ := fun μ => (∫⁻ θ, f θ ∂μ).toReal with hh
  have hhm : Measurable (fun μ : Measure ℝ => ∫⁻ θ, f θ ∂μ) := Measure.measurable_lintegral hfm
  have hjl : ∫⁻ μ, ∫⁻ θ, f θ ∂μ ∂τ = ∫⁻ θ, f θ ∂P := by
    rw [← Measure.lintegral_join hfm.aemeasurable, hjoin]
  have hPφ := integrable_φ P hi M B lam
  have hfin : ∫⁻ θ, f θ ∂P ≠ ⊤ := by
    have := hPφ.2
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun θ => φ_nonneg M B lam hM hBM hlam θ))] at this
    exact this.ne
  have hφP : ∫ θ, φ M B lam θ ∂P = (∫⁻ θ, f θ ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
      (fun θ => φ_nonneg M B lam hM hBM hlam θ)) hPφ.aestronglyMeasurable
  have hhint : Integrable h τ := by
    apply integrable_toReal_of_lintegral_ne_top hhm.aemeasurable
    rw [hjl]; exact hfin
  have hhτ : ∫ μ, h μ ∂τ = ∫ θ, φ M B lam θ ∂P := by
    rw [hh, integral_toReal hhm.aemeasurable, hjl, hφP]
    exact ae_lt_top hhm (by rw [hjl]; exact hfin)
  -- a.e. posterior is supported on the support of the prior
  have hsupp : ∀ᵐ μ ∂τ, μ (Icc θlo θhi)ᶜ = 0 := by
    have hms : MeasurableSet (Icc θlo θhi)ᶜ := measurableSet_Icc.compl
    have h0 : ∫⁻ μ, μ (Icc θlo θhi)ᶜ ∂τ = 0 := by
      rw [← Measure.join_apply hms, hjoin]; exact hS.supp_sub
    exact (lintegral_eq_zero_iff (Measure.measurable_coe hms)).mp h0
  rw [← hhτ]
  unfold value
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall
    (fun μ => regPayoff_nonneg M B hM hBM μ)) hhint ?_
  filter_upwards [hsupp, hτae] with μ hμs hμp
  have hμi : Integrable (fun θ : ℝ => θ) μ := integrable_of_supp μ θlo θhi hμs
  have hμφ := integrable_φ μ hμi M B lam
  have : h μ = ∫ θ, φ M B lam θ ∂μ := by
    rw [hh, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
      (fun θ => φ_nonneg M B lam hM hBM hlam θ)) hμφ.aestronglyMeasurable]
  rw [this]
  exact regPayoff_le μ hμi M B lam hlam

lemma condMean_Ioi_ge (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (hpos : 0 < P (Ioi t)) : t ≤ condMean P id (Ioi t) := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hF : 0 < (P (Ioi t)).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  rw [condMean_id, le_div_iff₀ hF]
  have h := setIntegral_mono_on (integrable_const t).integrableOn hi.integrableOn measurableSet_Ioi
    (fun θ (hθ : θ ∈ Ioi t) => le_of_lt hθ)
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h
  linarith

lemma value_reveal (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (hpos1 : 0 < P (Ioi t)) (hpos0 : 0 < P (Iic t))
    (hhigh : M - B < condMean P id (Ioi t)) (hlow : condMean P id (Iic t) ≤ M - B) :
    value M B (FinDisclosure.Threshold.revealPolicy P (Ioi t)) =
      (∫ θ in Ioi t, θ ∂P) + M * (P (Iic t)).toReal := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hsm : StronglyMeasurable (regPayoff M B) := (measurable_regPayoff M B).stronglyMeasurable
  have hint : ∀ (c : ENNReal) (ν : Measure ℝ), c ≠ ⊤ →
      Integrable (regPayoff M B) (c • Measure.dirac ν) := fun c ν hc =>
    (integrable_dirac' hsm enorm_lt_top).smul_measure hc
  unfold value FinDisclosure.Threshold.revealPolicy
  rw [integral_add_measure (hint _ _ (measure_ne_top _ _)) (hint _ _ (measure_ne_top _ _)),
    integral_smul_measure, integral_smul_measure, integral_dirac' _ _ hsm,
    integral_dirac' _ _ hsm, compl_Ioi]
  have e1 : regPayoff M B (P[|Ioi t]) = condMean P id (Ioi t) := by
    unfold regPayoff
    rw [postMean_cond P hi _ measurableSet_Ioi hpos1, if_pos hhigh]
  have e0 : regPayoff M B (P[|Iic t]) = M := by
    unfold regPayoff
    rw [postMean_cond P hi _ measurableSet_Iic hpos0, if_neg (not_lt.mpr hlow)]
  rw [e1, e0, condMean_id, smul_eq_mul, smul_eq_mul]
  have hF : 0 < (P (Ioi t)).toReal := ENNReal.toReal_pos hpos1.ne' (measure_ne_top _ _)
  rw [mul_div_cancel₀ _ hF.ne']
  ring

lemma integral_φ_split (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B)
    (t lam : ℝ) (hlam : 0 ≤ lam) (hrel : M + lam * (M - B) = (1 + lam) * t)
    (hcs : lam * ((M - B) * (P (Iic t)).toReal - ∫ θ in Iic t, θ ∂P) = 0) :
    ∫ θ, φ M B lam θ ∂P = (∫ θ in Ioi t, θ ∂P) + M * (P (Iic t)).toReal := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hPφ := integrable_φ P hi M B lam
  rw [← integral_add_compl measurableSet_Ioi hPφ, compl_Ioi]
  have h1 : ∫ θ in Ioi t, φ M B lam θ ∂P = ∫ θ in Ioi t, θ ∂P := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun θ (hθ : t < θ) => ?_)
    unfold φ
    have : 0 ≤ (1 + lam) * (θ - t) := mul_nonneg (by linarith) (by linarith)
    exact max_eq_left (by nlinarith)
  have h2 : ∫ θ in Iic t, φ M B lam θ ∂P = ∫ θ in Iic t, ((M + lam * (M - B)) - lam * θ) ∂P := by
    refine setIntegral_congr_fun measurableSet_Iic (fun θ (hθ : θ ≤ t) => ?_)
    unfold φ
    have : 0 ≤ (1 + lam) * (t - θ) := mul_nonneg (by linarith) (by linarith)
    rw [max_eq_right (by nlinarith)]
    ring
  rw [h1, h2, integral_sub (integrable_const _).integrableOn (hi.const_mul lam).integrableOn,
    setIntegral_const, integral_const_mul, smul_eq_mul, measureReal_def]
  linear_combination hcs

end AccProp2Sol

open AccountingRules.Threshold AccProp2Sol in
theorem solution (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B) (hlo : θlo < M - B) (hB : 0 < B) :
    ∃ θhat ∈ Ioc (M - B) M,
      (∀ τ : Measure (Measure ℝ), FinDisclosure.Threshold.IsBayesPlausible P τ →
          value M B τ ≤ value M B (FinDisclosure.Threshold.revealPolicy P (Ioi θhat))) ∧
      (B ≤ condMean P (fun θ => M - θ) (Iic M) → θhat = M) ∧
      (condMean P (fun θ => M - θ) (Iic M) < B →
          θhat ∈ Ioo (M - B) M ∧ condMean P id (Iic θhat) = M - B ∧
          ∀ t ∈ Ioo (M - B) M, condMean P id (Iic t) = M - B → t = θhat) ∧
      (M - B < postMean (P[|Ioi θhat]) ∧
        postMean (P[|Iic θhat]) ≤ M - B) := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hMhi := hS.M_lt_θhi
  have hlohi : θlo < θhi := by linarith
  have hFM : 0 < P (Iic M) := pos_Iic P θlo θhi M B hS M (by linarith) hlohi
  -- generic conclusion for a threshold `t` with multiplier `lam`
  have key : ∀ t lam : ℝ, M - B < t → t ≤ M → 0 ≤ lam → M + lam * (M - B) = (1 + lam) * t →
      lam * ((M - B) * (P (Iic t)).toReal - ∫ θ in Iic t, θ ∂P) = 0 →
      condMean P id (Iic t) ≤ M - B →
      (∀ τ : Measure (Measure ℝ), FinDisclosure.Threshold.IsBayesPlausible P τ →
          value M B τ ≤ value M B (FinDisclosure.Threshold.revealPolicy P (Ioi t))) ∧
      (M - B < postMean (P[|Ioi t]) ∧ postMean (P[|Iic t]) ≤ M - B) := by
    intro t lam ht1 ht2 hlam hrel hcs hlow
    have hp1 : 0 < P (Ioi t) := pos_Ioi P θlo θhi M B hS t (by linarith) hlohi
    have hp0 : 0 < P (Iic t) := pos_Iic P θlo θhi M B hS t (by linarith) hlohi
    have hhigh : M - B < condMean P id (Ioi t) :=
      lt_of_lt_of_le ht1 (condMean_Ioi_ge P θlo θhi M B hS t hp1)
    refine ⟨fun τ hτ => ?_, ?_, ?_⟩
    · calc value M B τ ≤ ∫ θ, φ M B lam θ ∂P := value_le P θlo θhi M B hS lam hlam τ hτ
        _ = _ := by
          rw [integral_φ_split P θlo θhi M B hS t lam hlam hrel hcs,
            value_reveal P θlo θhi M B hS t hp1 hp0 hhigh hlow]
    · rwa [postMean_cond P hi _ measurableSet_Ioi hp1]
    · rwa [postMean_cond P hi _ measurableSet_Iic hp0]
  by_cases hA : B ≤ condMean P (fun θ => M - θ) (Iic M)
  · have hcM : condMean P id (Iic M) ≤ M - B := by
      rw [condMean_sub P θlo θhi M B hS M hFM] at hA; linarith
    obtain ⟨k1, k2⟩ := key M 0 (by linarith) le_rfl le_rfl (by ring) (by ring) hcM
    exact ⟨M, ⟨by linarith, le_rfl⟩, k1, fun _ => rfl, fun h => absurd hA (not_le.mpr h), k2⟩
  · push_neg at hA
    have hcM : M - B < condMean P id (Iic M) := by
      rw [condMean_sub P θlo θhi M B hS M hFM] at hA; linarith
    have hGM : 0 < G P (M - B) M := by
      have := (condMean_le_iff P θlo θhi M B hS (M - B) M hFM).not.mp (not_le.mpr hcM)
      linarith
    have hG0 : G P (M - B) (M - B) < 0 := G_self_neg P θlo θhi M B hS (M - B) hlo hlohi
    obtain ⟨t, ⟨ht1, ht2⟩, hGt⟩ := intermediate_value_Ioo (by linarith : M - B ≤ M)
      (G_continuous P θlo θhi M B hS (M - B)).continuousOn ⟨hG0, hGM⟩
    have hp0 : 0 < P (Iic t) := pos_Iic P θlo θhi M B hS t (by linarith) hlohi
    have hroot : condMean P id (Iic t) = M - B :=
      (condMean_eq_iff P θlo θhi M B hS (M - B) t hp0).mpr hGt
    have hd : 0 < t - (M - B) := by linarith
    set lam := (M - t) / (t - (M - B)) with hlam_def
    have hlam : 0 ≤ lam := div_nonneg (by linarith) hd.le
    have hrel : M + lam * (M - B) = (1 + lam) * t := by
      rw [hlam_def]; field_simp; ring
    have hcs : lam * ((M - B) * (P (Iic t)).toReal - ∫ θ in Iic t, θ ∂P) = 0 := by
      rw [G_eq P θlo θhi M B hS] at hGt
      rw [show (M - B) * (P (Iic t)).toReal - ∫ θ in Iic t, θ ∂P = 0 by linarith, mul_zero]
    obtain ⟨k1, k2⟩ := key t lam ht1 ht2.le hlam hrel hcs hroot.le
    refine ⟨t, ⟨ht1, ht2.le⟩, k1, fun h => absurd h (not_le.mpr hA), fun _ => ⟨⟨ht1, ht2⟩, hroot, ?_⟩, k2⟩
    intro s ⟨hs1, hs2⟩ hs
    have hps : 0 < P (Iic s) := pos_Iic P θlo θhi M B hS s (by linarith) hlohi
    have hGs := (condMean_eq_iff P θlo θhi M B hS (M - B) s hps).mp hs
    rcases lt_trichotomy s t with h | h | h
    · have := G_strictMono P θlo θhi M B hS (M - B) hlo s t hs1.le h (by linarith)
      linarith
    · exact h
    · have := G_strictMono P θlo θhi M B hS (M - B) hlo t s ht1.le h (by linarith)
      linarith


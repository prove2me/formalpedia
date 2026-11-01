-- Prove2me | solution 1 for AccountingRules.Threshold.binary_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T04:16:46.138296+00:00
-- url     : https://prove2.me/submissions/6324f11d-0c29-4269-bc7f-eadba1810d5c

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

lemma postMean_eq (μ : Measure ℝ) (h : Integrable (fun θ : ℝ => θ) μ) :
    postMean μ = ∫ θ, θ ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h]; rfl

lemma measurable_postMean : Measurable postMean := by
  unfold postMean
  refine Measurable.sub ?_ ?_
  · exact (Measure.measurable_lintegral (by fun_prop)).ennreal_toReal
  · exact (Measure.measurable_lintegral (by fun_prop)).ennreal_toReal

lemma measurable_regPayoff (M B : ℝ) : Measurable (regPayoff M B) := by
  unfold regPayoff
  exact Measurable.ite (measurableSet_lt measurable_const measurable_postMean)
    measurable_postMean measurable_const

lemma rule_int (P : Measure ℝ) [IsFiniteMeasure P] (hi : Integrable (fun θ : ℝ => θ) P)
    (m : ℝ → ℝ) (hm : IsRule m) :
    Integrable m P ∧ Integrable (fun θ => θ * m θ) P := by
  have hb : ∀ᵐ θ ∂P, ‖m θ‖ ≤ 1 := Filter.Eventually.of_forall (fun θ => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hm.2 θ).1, (hm.2 θ).2])
  refine ⟨Integrable.mono' (integrable_const 1) hm.1.aestronglyMeasurable hb, ?_⟩
  have := hi.bdd_mul hm.1.aestronglyMeasurable hb
  simpa [mul_comm] using this


lemma supp_ae (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B)
    (τ : Measure (Measure ℝ)) (hjoin : τ.join = P) : ∀ᵐ μ ∂τ, μ (Icc θlo θhi)ᶜ = 0 := by
  have hms : MeasurableSet (Icc θlo θhi)ᶜ := measurableSet_Icc.compl
  have h0 : ∫⁻ μ, μ (Icc θlo θhi)ᶜ ∂τ = 0 := by
    rw [← Measure.join_apply hms, hjoin]; exact hS.supp_sub
  exact (lintegral_eq_zero_iff (Measure.measurable_coe hms)).mp h0

lemma postMean_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ] (θlo θhi : ℝ)
    (h : μ (Icc θlo θhi)ᶜ = 0) : θlo ≤ postMean μ ∧ postMean μ ≤ θhi := by
  have hi := integrable_of_supp μ θlo θhi h
  have hae : ∀ᵐ θ ∂μ, θ ∈ Icc θlo θhi := by
    rw [ae_iff]; simpa [compl_def] using h
  rw [postMean_eq μ hi]
  constructor
  · have := integral_mono_ae (integrable_const θlo) hi (hae.mono fun θ hθ => hθ.1)
    simpa using this
  · have := integral_mono_ae hi (integrable_const θhi) (hae.mono fun θ hθ => hθ.2)
    simpa using this

lemma lintegral_ofReal_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (θlo θhi : ℝ) (hlo : 0 ≤ θlo)
    (h : μ (Icc θlo θhi)ᶜ = 0) :
    ∫⁻ θ, ENNReal.ofReal θ ∂μ = ENNReal.ofReal (postMean μ) := by
  have hi := integrable_of_supp μ θlo θhi h
  have hae : ∀ᵐ θ ∂μ, θ ∈ Icc θlo θhi := by
    rw [ae_iff]; simpa [compl_def] using h
  rw [postMean_eq μ hi, ofReal_integral_eq_lintegral_ofReal hi
    (hae.mono fun θ hθ => le_trans hlo hθ.1)]

end AccProp2Sol

open AccountingRules.Threshold AccProp2Sol

theorem solution (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B) (τ : Measure (Measure ℝ))
    (hτ : FinDisclosure.Threshold.IsBayesPlausible P τ) :
    ∃ m : ℝ → ℝ, IsRule m ∧ A1 P M B m ∧ A2 P M B m ∧
      value M B τ = objective P M m := by
  have := hS.prob
  obtain ⟨hτp, hτae, hjoin⟩ := hτ
  have hi := integrable_id P θlo θhi M B hS
  have hlo0 := hS.θlo_nonneg
  set H : Set (Measure ℝ) := {μ | M - B < postMean μ} with hH
  have hHm : MeasurableSet H := measurableSet_lt measurable_const measurable_postMean
  have hgood : ∀ᵐ μ ∂τ, IsProbabilityMeasure μ ∧ μ (Icc θlo θhi)ᶜ = 0 :=
    hτae.and (supp_ae P θlo θhi M B hS τ hjoin)
  have hpmint : Integrable postMean τ := by
    refine Integrable.mono' (integrable_const (|θlo| + |θhi|))
      measurable_postMean.aestronglyMeasurable ?_
    filter_upwards [hgood] with μ hμ
    obtain ⟨hp, hs⟩ := hμ
    have := postMean_bounds μ θlo θhi hs
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le θlo, abs_nonneg θhi]
    · linarith [le_abs_self θhi, abs_nonneg θlo]
  have hkey : ∀ S : Set (Measure ℝ), MeasurableSet S →
      ((τ.restrict S).join ≤ P) ∧
        ∫ θ, θ ∂((τ.restrict S).join) = ∫ μ in S, postMean μ ∂τ := by
    intro S hSm
    have hle : (τ.restrict S).join ≤ P := by
      rw [Measure.le_iff]
      intro s hs
      rw [Measure.join_apply hs, ← hjoin, Measure.join_apply hs]
      exact setLIntegral_le_lintegral S _
    refine ⟨hle, ?_⟩
    have hac := Measure.absolutelyContinuous_of_le hle
    have hnn : 0 ≤ᵐ[(τ.restrict S).join] (fun θ : ℝ => θ) :=
      hac.ae_le ((ae_mem P θlo θhi M B hS).mono fun θ hθ => le_trans hlo0 hθ.1)
    have hof : Measurable (fun θ : ℝ => ENNReal.ofReal θ) := ENNReal.measurable_ofReal
    rw [integral_eq_lintegral_of_nonneg_ae hnn measurable_id.aestronglyMeasurable,
      Measure.lintegral_join hof.aemeasurable,
      integral_eq_lintegral_of_nonneg_ae _ measurable_postMean.aestronglyMeasurable]
    · congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hgood] with μ hμ
      obtain ⟨hp, hs⟩ := hμ
      exact lintegral_ofReal_eq μ θlo θhi hlo0 hs
    · filter_upwards [ae_restrict_of_ae hgood] with μ hμ
      obtain ⟨hp, hs⟩ := hμ
      exact le_trans hlo0 (postMean_bounds μ θlo θhi hs).1
  -- the high-signal measure
  set ν : Measure ℝ := (τ.restrict H).join with hν
  obtain ⟨hνle, hνθ⟩ := hkey H hHm
  have hac := Measure.absolutelyContinuous_of_le hνle
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_of_le P hνle
  have hνuniv : ν univ = τ H := by
    rw [hν, Measure.join_apply MeasurableSet.univ]
    rw [lintegral_congr_ae (g := fun _ => (1 : ENNReal))]
    · rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
    · filter_upwards [ae_restrict_of_ae hgood] with μ hμ
      obtain ⟨hp, hs⟩ := hμ
      exact measure_univ
  set m : ℝ → ℝ := fun θ => min (ν.rnDeriv P θ).toReal 1 with hmdef
  have hrule : IsRule m := by
    refine ⟨(Measure.measurable_rnDeriv ν P).ennreal_toReal.min measurable_const,
      fun θ => ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩⟩
  have hmae : m =ᵐ[P] fun θ => (ν.rnDeriv P θ).toReal := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hνle, Measure.rnDeriv_lt_top ν P] with θ h1 h2
    simp only [hmdef]
    apply min_eq_left
    have : ν.rnDeriv P θ ≤ 1 := h1
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have hmg : ∀ g : ℝ → ℝ, ∫ θ, m θ * g θ ∂P = ∫ θ, g θ ∂ν := by
    intro g
    rw [← integral_rnDeriv_smul hac]
    apply integral_congr_ae
    filter_upwards [hmae] with θ hθ
    show m θ * g θ = _
    rw [hθ, smul_eq_mul]
  have hint_m : ∫ θ, m θ ∂P = (τ H).toReal := by
    have := hmg (fun _ => 1)
    simp only [mul_one] at this
    rw [this, integral_const, smul_eq_mul, mul_one, measureReal_def, hνuniv]
  have hint_θm : ∫ θ, θ * m θ ∂P = ∫ μ in H, postMean μ ∂τ := by
    have := hmg (fun θ => θ)
    rw [← hνθ, ← this]
    congr 1; ext θ; ring
  have htot : ∫ θ, θ ∂P = ∫ μ, postMean μ ∂τ := by
    have := (hkey univ MeasurableSet.univ).2
    rwa [Measure.restrict_univ, hjoin] at this
  have hcompl : (τ Hᶜ).toReal = 1 - (τ H).toReal := by
    have := probReal_compl_eq_one_sub (μ := τ) hHm
    simpa [measureReal_def] using this
  have hsplit := integral_add_compl hHm hpmint
  obtain ⟨hmi, hθmi⟩ := rule_int P hi m hrule
  refine ⟨m, hrule, ?_, ?_, ?_⟩
  · -- (A.1)
    unfold A1
    have e1 : ∫ θ, θ * (1 - m θ) ∂P = (∫ θ, θ ∂P) - ∫ θ, θ * m θ ∂P := by
      rw [← integral_sub hi hθmi]; congr 1; ext θ; ring
    have e2 : ∫ θ, (1 - m θ) ∂P = 1 - ∫ θ, m θ ∂P := by
      rw [integral_sub (integrable_const 1) hmi]; simp
    have hb := setIntegral_mono_on hpmint.integrableOn (integrable_const (M - B)).integrableOn
      hHm.compl (fun μ (hμ : μ ∈ Hᶜ) => by
        simp only [hH, mem_compl_iff, mem_setOf_eq, not_lt] at hμ; exact hμ)
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at hb
    rw [e1, e2, hint_m, hint_θm, htot]
    rw [hcompl] at hb
    nlinarith
  · -- (A.2)
    unfold A2
    have hb := setIntegral_mono_on (integrable_const (M - B)).integrableOn hpmint.integrableOn
      hHm (fun μ (hμ : μ ∈ H) => le_of_lt hμ)
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at hb
    rw [hint_m, hint_θm]
    linarith
  · -- value identity
    have hregint : Integrable (regPayoff M B) τ := by
      refine Integrable.mono' (hpmint.norm.add (integrable_const |M|))
        (measurable_regPayoff M B).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
      intro μ
      unfold regPayoff
      split_ifs
      · simp only [Pi.add_apply, Real.norm_eq_abs]; linarith [abs_nonneg M]
      · simp only [Pi.add_apply, Real.norm_eq_abs]
        linarith [abs_nonneg (postMean μ), le_abs_self M]
    unfold value objective
    rw [← integral_add_compl hHm hregint,
      setIntegral_congr_fun hHm (g := postMean) (fun μ (hμ : μ ∈ H) => by
        unfold regPayoff; rw [if_pos (show M - B < postMean μ from hμ)]),
      setIntegral_congr_fun hHm.compl (g := fun _ => M) (fun μ (hμ : μ ∈ Hᶜ) => by
        unfold regPayoff; rw [if_neg (show ¬ (M - B < postMean μ) from hμ)]),
      setIntegral_const, smul_eq_mul, measureReal_def, hcompl, hint_θm, hint_m]
    ring

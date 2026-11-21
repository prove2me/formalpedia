-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterGronwall_F000
-- name    : LevyStochCalc_Poisson_CharacterGronwall_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:09:57.841196+00:00
-- url     : https://prove2.me/theorems/e19cba37-ccd8-41dd-a21e-b6ef447e2b26
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterGronwall
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterGronwall. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_GronwallIterate_F000
import Definitions.Def_LevyStochCalc_Poisson_CharacterFubini_F001
import Definitions.Def_SourceProof_146f4516246fb102b7d6e6c1
import Definitions.Def_SourceProof_330381a3f4dc8c5fdcdefb8b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the characters satisfies a Grönwall inequality

For a square-integrable weight of mean zero orthogonal to every compensated integral over the
horizon, the pairing `u(t) = 𝔼[r · χ_t]` with the character of the window counts up to `t` is a
window integral of the marks times the pairings at earlier times. Its norm is therefore bounded by
`2 ν(A)` times its own running integral, and it is a bounded measurable function of the time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Pairing

/-- The pairing of a weight with the character of the window counts up to time `s`. -/
noncomputable def charPairing (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (r : Ω → ℝ) (s : ℝ) : ℂ :=
  ∫ ω, (r ω : ℂ) * charAt N w Bfam s ω ∂P
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem integrable_mul_charAt (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {r : Ω → ℝ}
    (hr1 : Integrable r P) (s : ℝ) :
    Integrable (fun ω => (r ω : ℂ) * charAt N w Bfam s ω) P := by
  have h := hr1.ofReal.bdd_mul (c := 1) (measurable_charAt N w hBm s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [charAt, Complex.norm_exp_I_mul_ofReal])
  exact h.congr (Filter.Eventually.of_forall fun ω => mul_comm _ _)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_charPairing_le (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    {r : Ω → ℝ} (hr1 : Integrable r P) (s : ℝ) :
    ‖charPairing N w Bfam r s‖ ≤ ∫ ω, ‖r ω‖ ∂P := by
  refine norm_integral_le_of_norm_le hr1.norm (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul, Complex.norm_real, charAt, Complex.norm_exp_I_mul_ofReal, mul_one]
/-- The pairing of an integrable weight with a unimodular exponential of a jointly measurable
integrand is a measurable function of the time. -/
theorem aestronglyMeasurable_pairing_exp {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    {r : Ω → ℝ} (hr1 : Integrable r P) (μ : Measure ℝ) [SFinite μ] :
    AEStronglyMeasurable
      (fun s => ∫ ω, (r ω : ℂ) * Complex.exp (Complex.I * (f ω s : ℂ)) ∂P) μ := by
  have hr' : AEStronglyMeasurable (fun ω => (r ω : ℂ)) P :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hr1.aestronglyMeasurable
  have hexp : Measurable fun p : Ω × ℝ => Complex.exp (Complex.I * (f p.1 p.2 : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hf))
  exact (hr'.comp_fst.mul hexp.aestronglyMeasurable).prod_swap.integral_prod_right'
/-- A function of the time that agrees, at every time in `(0, T]`, with the pairing of an
integrable weight against a unimodular exponential of a jointly measurable integrand is
measurable on `[0, T]`. -/
theorem aestronglyMeasurable_of_pairing_exp {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) {r : Ω → ℝ} (hr1 : Integrable r P) {u : ℝ → ℂ}
    {T : ℝ} (hu : ∀ s, 0 < s → s ≤ T →
      ∫ ω, (r ω : ℂ) * Complex.exp (Complex.I * (f ω s : ℂ)) ∂P = u s) :
    AEStronglyMeasurable u (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  refine (aestronglyMeasurable_pairing_exp hf hr1 (volume.restrict (Set.Icc (0 : ℝ) T))).congr ?_
  have h0 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton,
      Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
  exact hu s (lt_of_le_of_ne hs.1 hs0.symm) hs.2
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The pairing is, at every positive time up to `T`, a pairing against the predictable
exponential of the chain rule, hence measurable in the time. -/
theorem aestronglyMeasurable_charPairing (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {r : Ω → ℝ} (hr1 : Integrable r P) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) (hAne : A.Nonempty) :
    AEStronglyMeasurable (charPairing N w Bfam r) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  obtain ⟨e₀, he₀⟩ := hAne
  have hpm : Measurable[Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
      predStrict N w (truncFam Bfam T) A T p.1 p.2.1 p.2.2 :=
    markedPredictable_predStrict N hℱ w (measurableSet_truncFam hBm T) hA hAν T
  have hpm' : Measurable fun p : Ω × ℝ × E =>
      predStrict N w (truncFam Bfam T) A T p.1 p.2.1 p.2.2 :=
    hpm.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hg : Measurable fun p : Ω × ℝ => (p.1, (p.2, e₀)) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  -- Elaborated without an expected type: unifying `?g ∘ ?f` against the composite would
  -- unfold `predStrict`.
  have hf := hpm'.comp hg
  exact aestronglyMeasurable_of_pairing_exp
    (f := fun ω s => predStrict N w (truncFam Bfam T) A T ω s e₀) hf hr1
    (fun s hs hsT => integral_mul_exp_predStrict N w hBm hs hsT le_rfl he₀)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem integrableOn_norm_charPairing (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {r : Ω → ℝ} (hr1 : Integrable r P) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) (hAne : A.Nonempty) :
    IntegrableOn (fun s => ‖charPairing N w Bfam r s‖) (Set.Icc (0 : ℝ) T) volume := by
  refine Integrable.mono' (integrable_const (∫ ω, ‖r ω‖ ∂P))
    (aestronglyMeasurable_charPairing N hℱ hr1 w hBm hA hAν T hAne).norm
    (Filter.Eventually.of_forall fun s => ?_)
  rw [norm_norm]
  exact norm_charPairing_le N w Bfam hr1 s
end Pairing

section Bound

/-- **The pairing as a window integral.** For a square-integrable weight of mean zero orthogonal to
every compensated integral, the pairing at `t` is the integral over the window of the mark times
the pairings at earlier times. -/
theorem charPairing_eq_window_integral (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    {t : ℝ} (htT : t ≤ T) :
    charPairing N w Bfam r t
      = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          charMark w Bfam t q * charPairing N w Bfam r q.1 ∂(referenceIntensity ν) := by
  have hr1 : Integrable r P := hr2.integrable one_le_two
  have h1 : charPairing N w Bfam r t = ∫ ω, (r ω : ℂ) * (charAt N w Bfam t ω - 1) ∂P := by
    have hsub : ∀ ω, (r ω : ℂ) * (charAt N w Bfam t ω - 1)
        = (r ω : ℂ) * charAt N w Bfam t ω - (r ω : ℂ) := fun ω => by ring
    simp_rw [hsub]
    have hrC : Integrable (fun ω => (r ω : ℂ)) P := hr1.ofReal
    have hz : ∫ ω, (r ω : ℂ) ∂P = 0 := by
      have : ∫ ω, (r ω : ℂ) ∂P = ((∫ ω, r ω ∂P : ℝ) : ℂ) := integral_ofReal
      rw [this, hr0]; simp
    rw [integral_sub (integrable_mul_charAt N w hBm hr1 t) hrC, hz, sub_zero]
    rfl
  rw [h1, _root_.Prove2MeSourceProof.h_146f4516246fb102b7d6e6c1 N hℱ hT hr2 hperp w hBm hA hAν hBsub htT,
    _root_.Prove2MeSourceProof.h_330381a3f4dc8c5fdcdefb8b N hℱ hr1 w hBm hA hAν hBsub htT]
  rfl
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The function of the time alone is integrable over a window against the reference
intensity. -/
theorem integrableOn_prod_of_time {f : ℝ → ℝ} {t : ℝ} (hf : IntegrableOn f (Set.Ioc 0 t) volume)
    {A : Set E} (hAν : ν A ≠ ⊤) :
    IntegrableOn (fun q : ℝ × E => f q.1) (Set.Ioc (0 : ℝ) t ×ˢ A) (referenceIntensity ν) := by
  haveI : IsFiniteMeasure (ν.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hAν⟩
  have hI : Set.Ioc (0 : ℝ) t ∩ Set.Ici 0 = Set.Ioc 0 t :=
    Set.inter_eq_left.mpr (fun x hx => le_of_lt hx.1)
  rw [IntegrableOn, referenceIntensity, ← Measure.prod_restrict,
    Measure.restrict_restrict measurableSet_Ioc, hI]
  have := hf.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : E => (1 : ℝ)) (ν.restrict A))
  simpa using this
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- A window integral of a function of the time alone is the mark measure of the window times
the time integral. -/
theorem setIntegral_prod_of_time {f : ℝ → ℝ} {t : ℝ} (hf : IntegrableOn f (Set.Ioc 0 t) volume)
    {A : Set E} (hAν : ν A ≠ ⊤) :
    ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, f q.1 ∂(referenceIntensity ν)
      = (ν A).toReal * ∫ s in Set.Ioc (0 : ℝ) t, f s := by
  have hint := integrableOn_prod_of_time (ν := ν) hf hAν
  rw [referenceIntensity] at hint ⊢
  rw [setIntegral_prod _ hint]
  simp_rw [setIntegral_const, smul_eq_mul]
  have hI : Set.Ioc (0 : ℝ) t ∩ Set.Ici 0 = Set.Ioc 0 t :=
    Set.inter_eq_left.mpr fun x hx => le_of_lt hx.1
  rw [MeasureTheory.integral_const_mul, Measure.restrict_restrict measurableSet_Ioc, hI,
    measureReal_def]
end Bound

end LevyStochCalc.Poisson



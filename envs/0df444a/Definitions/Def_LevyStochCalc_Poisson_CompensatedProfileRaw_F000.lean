-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileRaw_F000
-- name    : LevyStochCalc_Poisson_CompensatedProfileRaw_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:18:07.08957+00:00
-- url     : https://prove2.me/theorems/2d4823f2-83e5-4378-8f42-b63efd7416a2
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProfileRaw
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProfileRaw. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileLinear_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileLinear_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileRepr_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F003
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of an integrable mark profile is pathwise

Let `N` be a Poisson random measure on `[0, ∞) × E` with `σ`-finite intensity `ν`, possibly
`ν(E) = ∞`, and let `f ∈ L¹(ν) ∩ L²(ν)` be a deterministic mark profile. Over a step `(a, b]`,
`0 ≤ a ≤ b`, almost surely `f` is integrable on `(a, b] × E` against `N(ω)` and the compensated
integral of `f` is the raw integral minus its compensator:

  `∫_E f(e) ΔÑ(de) = ∫_{(a, b] × E} f(e) N(ω)(ds, de) − (b − a) ∫_E f dν`.

The mean measure of `N` is its reference intensity (Campbell's formula), so the raw integral of
`|f|` over the step has mean `(b − a) ‖f‖_{L¹(ν)}`. At a simple profile the identity is the
definition of the compensated step integral. Simple functions converging to `f` both in `L¹(ν)`
and in `L²(ν)` then carry the identity to `f`: the compensated integrals converge in `L²(P)` and
the raw integrals minus their compensators converge in `L¹(P)`.

## Main statements

* `LevyStochCalc.Poisson.PoissonRandomMeasure.bind_N` — the mean measure of a Poisson random
  measure is its reference intensity.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.lintegral_lintegral_N` — Campbell's formula.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.ae_integrableOn_cell` — an integrable mark profile
  is almost surely integrable on a step times the mark space.
* `LevyStochCalc.Poisson.compensatedProfile_ae_eq_integral_sub` — the compensated integral of a
  mark profile in `L¹(ν) ∩ L²(ν)` is the raw integral minus its compensator.
* `LevyStochCalc.Poisson.compensatedProfileRepr_ae_eq_integral_sub` — the same for the
  representative of the compensated integral for a sub-σ-algebra.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The mean measure -/

/-- The reference intensity on a step times the mark space is Lebesgue measure on the step times
the intensity. -/
theorem referenceIntensity_restrict_Ioc_prod_univ {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    (referenceIntensity ν).restrict (Set.Ioc a b ×ˢ Set.univ)
      = (volume.restrict (Set.Ioc a b)).prod ν := by
  have hsub : Set.Ioc a b ∩ Set.Ici (0 : ℝ) = Set.Ioc a b := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun h => ha.trans h.1.le
  rw [referenceIntensity, ← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Ioc,
    hsub, Measure.restrict_univ]
namespace PoissonRandomMeasure

variable (N : PoissonRandomMeasure P ν)

/-- A Poisson random measure is a measurable map into the measures on the time–mark space. -/
theorem measurable_N : Measurable N.N :=
  Measure.measurable_of_measurable_coe _ fun _ hB => N.measurable_eval hB
/-- The mean count of a measurable set is its reference intensity, finite or not. -/
theorem lintegral_N_apply {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    ∫⁻ ω, N.N ω B ∂P = referenceIntensity ν B := by
  by_cases hB' : referenceIntensity ν B = ⊤
  · rw [hB', lintegral_congr_ae (N.infinite_at_infinite_intensity hB hB'), lintegral_const,
      measure_univ, mul_one]
  · exact _root_.Prove2MeSourceProof.h_9d62612e2dce26cbc374ccfb N hB hB'
/-- **The mean measure of a Poisson random measure is its reference intensity.** -/
theorem bind_N : P.bind N.N = referenceIntensity ν := by
  ext B hB
  rw [Measure.bind_apply hB N.measurable_N.aemeasurable, N.lintegral_N_apply hB]
/-- **Campbell's formula.** The mean integral of a measurable nonnegative function against a
Poisson random measure is its integral against the reference intensity. -/
theorem lintegral_lintegral_N {g : ℝ × E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ q, g q ∂(N.N ω) ∂P = ∫⁻ q, g q ∂(referenceIntensity ν) := by
  rw [← N.bind_N, Measure.lintegral_bind N.measurable_N.aemeasurable hg.aemeasurable]
/-- The integral of a measurable nonnegative function over a measurable set against a Poisson
random measure is measurable in the sample point. -/
theorem measurable_setLIntegral_N {g : ℝ × E → ℝ≥0∞} (hg : Measurable g) {S : Set (ℝ × E)}
    (hS : MeasurableSet S) : Measurable fun ω => ∫⁻ q in S, g q ∂(N.N ω) := by
  simp_rw [← lintegral_indicator hS]
  exact (Measure.measurable_lintegral (hg.indicator hS)).comp N.measurable_N
/-- Campbell's formula on a measurable set. -/
theorem lintegral_setLIntegral_N {g : ℝ × E → ℝ≥0∞} (hg : Measurable g) {S : Set (ℝ × E)}
    (hS : MeasurableSet S) :
    ∫⁻ ω, ∫⁻ q in S, g q ∂(N.N ω) ∂P = ∫⁻ q in S, g q ∂(referenceIntensity ν) := by
  simp_rw [← lintegral_indicator hS]
  exact N.lintegral_lintegral_N (hg.indicator hS)
/-- Campbell's formula for a function of the mark on a step times the mark space. -/
theorem lintegral_setLIntegral_N_cell {g : E → ℝ≥0∞} (hg : Measurable g) {a : ℝ} (ha : 0 ≤ a)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc a b ×ˢ Set.univ, g q.2 ∂(N.N ω) ∂P
      = ENNReal.ofReal (b - a) * ∫⁻ e, g e ∂ν := by
  rw [N.lintegral_setLIntegral_N (g := fun q : ℝ × E => g q.2) (hg.comp measurable_snd)
      (S := Set.Ioc a b ×ˢ Set.univ) (measurableSet_Ioc.prod .univ),
    referenceIntensity_restrict_Ioc_prod_univ ha b,
    lintegral_prod (fun q : ℝ × E => g q.2) (hg.comp measurable_snd).aemeasurable]
  simp only [setLIntegral_const, Real.volume_Ioc]
  rw [mul_comm]
/-- Almost surely a Poisson random measure does not charge the time–mark sets over a null set of
marks, so functions of the mark equal `ν`-almost everywhere are equal `N(ω)`-almost
everywhere. -/
theorem ae_ae_eq_comp_snd {f g : E → ℝ} (hfg : f =ᵐ[ν] g) :
    ∀ᵐ ω ∂P, (fun q : ℝ × E => f q.2) =ᵐ[N.N ω] fun q => g q.2 := by
  obtain ⟨Z, hsub, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hfg)
  have hUZ : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Z) := MeasurableSet.univ.prod hZ
  have h0 : ∫⁻ ω, N.N ω ((Set.univ : Set ℝ) ×ˢ Z) ∂P = 0 := by
    rw [N.lintegral_N_apply hUZ, referenceIntensity, Measure.prod_prod, hZ0, mul_zero]
  have hae := (lintegral_eq_zero_iff (N.measurable_eval hUZ)).1 h0
  filter_upwards [hae] with ω hω
  refine ae_iff.2 (measure_mono_null (fun q hq => ?_) hω)
  exact ⟨Set.mem_univ _, hsub hq⟩
/-- An integrable measurable mark profile is almost surely integrable on a step times the mark
space against a Poisson random measure. -/
theorem ae_integrableOn_cell_of_measurable {f : E → ℝ} (hfm : Measurable f)
    (hf : Integrable f ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => f q.2) (Set.Ioc a b ×ˢ Set.univ) (N.N ω) := by
  have hmean : ∫⁻ ω, ∫⁻ q in Set.Ioc a b ×ˢ Set.univ, ‖f q.2‖ₑ ∂(N.N ω) ∂P ≠ ⊤ := by
    rw [N.lintegral_setLIntegral_N_cell hfm.enorm ha b]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.2.ne
  have hm := N.measurable_setLIntegral_N (g := fun q : ℝ × E => ‖f q.2‖ₑ)
    (hfm.comp measurable_snd).enorm (S := Set.Ioc a b ×ˢ Set.univ)
    (measurableSet_Ioc.prod MeasurableSet.univ)
  filter_upwards [ae_lt_top hm hmean] with ω hω
  exact ⟨(hfm.comp measurable_snd).aestronglyMeasurable, hω⟩
/-- **An integrable mark profile is almost surely integrable on a step times the mark space**
against a Poisson random measure. -/
theorem ae_integrableOn_cell {f : E → ℝ} (hf : Integrable f ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => f q.2) (Set.Ioc a b ×ˢ Set.univ) (N.N ω) := by
  have hmk := hf.1.ae_eq_mk
  filter_upwards [N.ae_integrableOn_cell_of_measurable hf.1.stronglyMeasurable_mk.measurable
    (hf.congr hmk) ha b, N.ae_ae_eq_comp_snd hmk] with ω hω hωe
  exact hω.congr_fun_ae (ae_restrict_of_ae hωe.symm)
/-- The integral of a measurable mark profile on a step times the mark space against a Poisson
random measure is almost everywhere strongly measurable in the sample point. -/
theorem aestronglyMeasurable_setIntegral_cell {f : E → ℝ} (hfm : Measurable f)
    (hf : Integrable f ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    AEStronglyMeasurable (fun ω => ∫ q in Set.Ioc a b ×ˢ Set.univ, f q.2 ∂(N.N ω)) P := by
  have hW : MeasurableSet (Set.Ioc a b ×ˢ (Set.univ : Set E)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hpos := N.measurable_setLIntegral_N
    (ENNReal.measurable_ofReal.comp (hfm.comp measurable_snd)) hW
  have hneg := N.measurable_setLIntegral_N
    (ENNReal.measurable_ofReal.comp (hfm.comp measurable_snd).neg) hW
  refine AEStronglyMeasurable.congr
    ((hpos.ennreal_toReal.sub hneg.ennreal_toReal).aestronglyMeasurable) ?_
  filter_upwards [N.ae_integrableOn_cell_of_measurable hfm hf ha b] with ω hω
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω).symm
end PoissonRandomMeasure

/-! ### Simple profiles -/

/-- The integral over a set `s ×ˢ univ` of the indicator of a mark set `B` is the measure of
`s ×ˢ B`. -/
private theorem setIntegral_indicator_snd (μ : Measure (ℝ × E)) (s : Set ℝ) {B : Set E}
    (hB : MeasurableSet B) :
    ∫ q in s ×ˢ Set.univ, B.indicator (fun _ => (1 : ℝ)) q.2 ∂μ = μ.real (s ×ˢ B) := by
  have hfun : (fun q : ℝ × E => B.indicator (fun _ => (1 : ℝ)) q.2)
      = (Prod.snd ⁻¹' B).indicator fun _ => (1 : ℝ) := by
    funext q
    by_cases hq : q.2 ∈ B
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' B from hq)]
    · rw [Set.indicator_of_notMem hq,
        Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' B from hq)]
  have hset : Prod.snd ⁻¹' B ∩ s ×ˢ Set.univ = s ×ˢ B := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact and_comm
  rw [hfun, integral_indicator_const _ (measurable_snd hB), smul_eq_mul, mul_one,
    measureReal_def, Measure.restrict_apply (measurable_snd hB), hset, measureReal_def]
/-! ### The pathwise identity -/

section Repr

variable {Ω' : Type u} (m : MeasurableSpace Ω') [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P']

end Repr

end LevyStochCalc.Poisson



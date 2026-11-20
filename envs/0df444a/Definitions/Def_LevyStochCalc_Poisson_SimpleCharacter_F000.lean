-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleCharacter_F000
-- name    : LevyStochCalc_Poisson_SimpleCharacter_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:36:31.082186+00:00
-- url     : https://prove2.me/theorems/8b89cf02-02d8-4255-8128-dce6e08e917a
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleCharacter
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleCharacter. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ChainRule_F001
import Definitions.Def_LevyStochCalc_Poisson_StrictCount_F000
import Definitions.Def_SourceProof_74eb321e4a8b4ce4ef69f2c2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple integrands and their window sums

A finite combination of indicators integrates against a Poisson random measure as the matching
combination of counts, so for such an integrand the window sums of the jump chain rule are
finite sums of counts. Those are adapted, which is what the predictable form of the chain rule's
integrand needs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

/-- A simple time–mark integrand: a finite combination of indicators. -/
noncomputable def simpleMark (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (p : ℝ × E) : ℝ :=
  ∑ j, w j * (Bfam j).indicator (fun _ => (1 : ℝ)) p
theorem measurable_simpleMark (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) : Measurable (simpleMark w Bfam) := by
  classical
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_const.indicator (hBm j)).const_mul (w j)
omit [MeasurableSpace E] in
theorem simpleMark_eq_zero (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {D : Set (ℝ × E)}
    (hBsub : ∀ j, Bfam j ⊆ D) {p : ℝ × E} (hp : p ∉ D) : simpleMark w Bfam p = 0 := by
  classical
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Set.indicator_of_notMem (fun hmem => hp (hBsub j hmem)), mul_zero]
/-- **The integral of a simple integrand over a time window is the matching combination of
counts.** -/
theorem ae_setIntegral_simpleMark (N : PoissonRandomMeasure P ν) {A : Set E}
    (hAν : ν A ≠ ⊤) {T : ℝ} (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    ∀ᵐ ω ∂P, ∀ S : Set ℝ,
      (∫ p in (⋃ j, Bfam j) ∩ S ×ˢ Set.univ, simpleMark w Bfam p ∂(N.N ω))
        = ∑ j, w j * (N.N ω (Bfam j ∩ S ×ˢ Set.univ)).toReal := by
  classical
  have hBm' : MeasurableSet (⋃ j, Bfam j) := MeasurableSet.iUnion hBm
  have hBsub' : (⋃ j, Bfam j) ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := Set.iUnion_subset hBsub
  have hBfin : referenceIntensity ν (⋃ j, Bfam j) ≠ ⊤ :=
    ne_top_of_le_ne_top (referenceIntensity_Ioc_prod_ne_top hAν T) (measure_mono hBsub')
  filter_upwards [N.integer_valued hBm' hBfin] with ω hω S
  obtain ⟨m, hm⟩ := hω
  haveI : IsFiniteMeasure ((N.N ω).restrict ((⋃ j, Bfam j) ∩ S ×ˢ Set.univ)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    refine lt_of_le_of_lt (measure_mono Set.inter_subset_left) ?_
    rw [hm]
    exact ENNReal.natCast_lt_top m
  have hint : ∀ j : ι, Integrable (fun p : ℝ × E => w j * (Bfam j).indicator (fun _ => (1 : ℝ)) p)
      ((N.N ω).restrict ((⋃ j, Bfam j) ∩ S ×ˢ Set.univ)) := fun j =>
    ((integrable_const (1 : ℝ)).indicator (hBm j)).const_mul (w j)
  simp only [simpleMark]
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, setIntegral_indicator (hBm j), setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def]
  congr 2
  rw [Set.inter_assoc, Set.inter_comm (S ×ˢ Set.univ) (Bfam j), ← Set.inter_assoc,
    Set.inter_eq_self_of_subset_right (Set.subset_iUnion Bfam j)]
/-- The window sums of a simple integrand, in both the closed and the open form. -/
theorem ae_windowSum_simple (N : PoissonRandomMeasure P ν) {A : Set E}
    (hAν : ν A ≠ ⊤) {T : ℝ} (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      windowSum N (⋃ j, Bfam j) (simpleMark w Bfam) t ω
          = ∑ j, w j * (N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ)).toReal
        ∧ windowSumStrict N (⋃ j, Bfam j) (simpleMark w Bfam) t ω
          = ∑ j, w j * (N.N ω (Bfam j ∩ Set.Ioo (0 : ℝ) t ×ˢ Set.univ)).toReal := by
  filter_upwards [ae_setIntegral_simpleMark N hAν w hBm hBsub] with ω hω t
  exact ⟨hω (Set.Ioc (0 : ℝ) t), hω (Set.Ioo (0 : ℝ) t)⟩
section Predictable

variable (N : PoissonRandomMeasure P ν)

/-- The predictable form of the strictly-past window sum of a simple integrand. -/
noncomputable def predStrict (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  ∑ j, w j * (strictCount N (Bfam j) A T ω s e).toReal
theorem markedPredictable_predStrict {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (T : ℝ) : Probability.MarkedPredictable ℱ ν (predStrict N w Bfam A T) := by
  classical
  change Measurable[Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    ∑ j, w j * (strictCount N (Bfam j) A T p.1 p.2.1 p.2.2).toReal
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((ENNReal.measurable_toReal.comp
    (markedPredictable_strictCount N hℱ (hBm j) hA hAν T)).const_mul (w j))
theorem predStrict_eq (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) {A : Set E} {T s : ℝ}
    (hs : 0 < s) (hsT : s ≤ T) {e : E} (he : e ∈ A) (ω : Ω) :
    predStrict N w Bfam A T ω s e
      = ∑ j, w j * (N.N ω (Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ)).toReal := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.Prove2MeSourceProof.h_74eb321e4a8b4ce4ef69f2c2 N hs hsT he ω]
end Predictable

end LevyStochCalc.Poisson



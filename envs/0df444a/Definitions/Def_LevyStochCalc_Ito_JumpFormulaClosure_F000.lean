-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaClosure_F000
-- name    : LevyStochCalc_Ito_JumpFormulaClosure_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:47:09.944548+00:00
-- url     : https://prove2.me/theorems/a4f37a05-14ab-4c6b-a6db-73a8d42f049c
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaClosure
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaClosure. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F001
import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F002
import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F003
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exhausting a σ-finite mark space by finite-activity complements

A σ-finite intensity has a monotone family of measurable sets of finite measure covering the mark
space, so the complements of that family are antitone, have empty intersection, and carry finite
intensity on their own complements. Truncating a jump coefficient to the complement of a member
therefore leaves finite activity, and the members shrink to a null set.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.smallMarks` — the complements of a spanning family of the
  intensity.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurableSet_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.antitone_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.measure_compl_smallMarks_lt_top`,
  `LevyStochCalc.Ito.JumpFormula.iInter_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.measure_iInter_smallMarks` — the four properties the small-jump
  truncation asks of a family of mark sets.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe v

variable {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]

/-- The complements of a spanning family of the intensity, used as the small-mark sets of the
truncation. -/
def smallMarks (m : ℕ) : Set E := (spanningSets ν m)ᶜ
theorem measurableSet_smallMarks (m : ℕ) : MeasurableSet (smallMarks ν m) :=
  (measurableSet_spanningSets ν m).compl
theorem compl_smallMarks (m : ℕ) : (smallMarks ν m)ᶜ = spanningSets ν m :=
  compl_compl _
theorem antitone_smallMarks : Antitone (smallMarks ν) := fun _ _ h =>
  Set.compl_subset_compl.mpr (monotone_spanningSets ν h)
theorem measure_compl_smallMarks_lt_top (m : ℕ) : ν (smallMarks ν m)ᶜ < ⊤ := by
  rw [compl_smallMarks]
  exact measure_spanningSets_lt_top ν m
theorem measure_compl_smallMarks_ne_top (m : ℕ) : ν (smallMarks ν m)ᶜ ≠ ⊤ :=
  (measure_compl_smallMarks_lt_top ν m).ne
theorem iInter_smallMarks : (⋂ m, smallMarks ν m) = (∅ : Set E) := by
  simp only [smallMarks, ← Set.compl_iUnion, iUnion_spanningSets ν, Set.compl_univ]
theorem measure_iInter_smallMarks : ν (⋂ m, smallMarks ν m) = 0 := by
  rw [iInter_smallMarks ν]
  exact measure_empty
/-- Almost every mark eventually leaves the small-mark sets. -/
theorem ae_eventually_notMem_smallMarks :
    ∀ᵐ e ∂ν, ∀ᶠ m in Filter.atTop, e ∉ smallMarks ν m :=
  ae_eventually_notMem_of_antitone (antitone_smallMarks ν) (measure_iInter_smallMarks ν)
section Augmentation

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The multidimensional Brownian integral over a filtration agrees almost everywhere with the
integral over its augmentation. -/
theorem multidimStochasticIntegral_augFiltration
    (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : ∀ i : Fin d, IsBrownianFiltration (W.W i) ℱ) (Z : ℝ → Ω → Fin d → ℝ)
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hp' : ∀ i : Fin d,
      Probability.ProgressivelyMeasurable (augFiltration ℱ P) fun ω s => Z s ω i)
    (hq : ∀ (i : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) :
    MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq T
      =ᵐ[P] MultidimBrownianMotion.stochasticIntegral W (augFiltration ℱ P)
        (fun i => isBrownianFiltration_augFiltration (hℱ i)) Z hm hp' hq T := by
  have hchan : ∀ i : Fin d,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱ i)
          (fun ω s => Z s ω i) (hm i) (hp i) (hq i) T
        =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i)
          (augFiltration ℱ P) (isBrownianFiltration_augFiltration (hℱ i))
          (fun ω s => Z s ω i) (hm i) (hp' i) (hq i) T :=
    fun i => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_augFiltration
      (W.W i) ℱ (hℱ i) _ (hm i) (hp i) (hp' i) (hq i) T
  filter_upwards [MeasureTheory.ae_all_iff.mpr hchan] with ω hω
  rw [multidimStochasticIntegral_eq_sum W ℱ hℱ Z hm hp hq T ω,
    multidimStochasticIntegral_eq_sum W (augFiltration ℱ P)
      (fun i => isBrownianFiltration_augFiltration (hℱ i)) Z hm hp' hq T ω]
  exact Finset.sum_congr rfl fun i _ => hω i
end Augmentation

section Repair

universe w

variable {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}

/-- An almost-sure property holds on a measurable set whose complement is null. -/
theorem exists_measurable_full_of_ae {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, p ω := by
  obtain ⟨Z, hsub, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  refine ⟨Zᶜ, hZm.compl, ?_, fun ω hω => ?_⟩
  · rwa [compl_compl]
  · by_contra hp
    exact hω (hsub hp)
/-- A path agreeing with a given one on a set and vanishing off it. -/
noncomputable def repairOn (G : Set Ω) (X : ℝ → Ω → Fin n → ℝ) (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  haveI := Classical.dec (ω ∈ G)
  if ω ∈ G then X t ω else 0
omit [MeasurableSpace Ω] in
@[simp] theorem repairOn_of_mem {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ} {ω : Ω} (hω : ω ∈ G) (t : ℝ) :
    repairOn G X t ω = X t ω := by
  simp only [repairOn, hω, if_true]
omit [MeasurableSpace Ω] in
@[simp] theorem repairOn_of_notMem {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ} {ω : Ω} (hω : ω ∉ G)
    (t : ℝ) : repairOn G X t ω = 0 := by
  simp only [repairOn, hω, if_false]
/-- The repaired path agrees with the original almost surely, at every time simultaneously. -/
theorem ae_forall_repairOn_eq {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ} (hG : P Gᶜ = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, repairOn G X t ω = X t ω := by
  have : ∀ᵐ ω ∂P, ω ∈ G := mem_ae_iff.mpr hG
  filter_upwards [this] with ω hω t
  exact repairOn_of_mem hω t
/-- The repaired path is jointly measurable. -/
theorem measurable_uncurry_repairOn {G : Set Ω} (hGm : MeasurableSet G)
    {X : ℝ → Ω → Fin n → ℝ} (hX : Measurable (Function.uncurry X)) :
    Measurable (Function.uncurry (repairOn G X)) := by
  classical
  have hmem : MeasurableSet {q : ℝ × Ω | q.2 ∈ G} := measurable_snd hGm
  have heq : Function.uncurry (repairOn G X)
      = fun q : ℝ × Ω => if q.2 ∈ G then Function.uncurry X q else 0 := by
    funext q
    by_cases hq : q.2 ∈ G <;> simp [Function.uncurry, repairOn, hq]
  rw [heq]
  exact Measurable.ite hmem hX measurable_const
omit [MeasurableSpace Ω] in
/-- Off the good set the repaired path is the constant zero path, which is càdlàg; on it the
repaired path is the original one, so the repair is càdlàg at every sample point. -/
theorem repairOn_cadlag {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}
    (hGp : ∀ ω ∈ G, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
            Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds L))
    (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
    Filter.Tendsto (fun s => repairOn G X s ω) (nhdsWithin t (Set.Ioi t))
        (nhds (repairOn G X t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ,
          Filter.Tendsto (fun s => repairOn G X s ω i) (nhdsWithin t (Set.Iio t)) (nhds L) := by
  by_cases hω : ω ∈ G
  · simpa only [repairOn_of_mem hω] using hGp ω hω t ht
  · refine ⟨?_, fun i => ⟨0, ?_⟩⟩
    · simp only [repairOn_of_notMem hω]
      exact tendsto_const_nhds
    · simp only [repairOn_of_notMem hω]
      exact tendsto_const_nhds
omit [MeasurableSpace Ω] in
/-- Off the good set the repaired path is the constant zero path, which is continuous; on it the
repaired path is the original one, so the repair is continuous at every sample point. -/
theorem repairOn_continuous {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}
    (hGc : ∀ ω ∈ G, Continuous fun t => X t ω) (ω : Ω) :
    Continuous fun t => repairOn G X t ω := by
  by_cases hω : ω ∈ G
  · simpa only [repairOn_of_mem hω] using hGc ω hω
  · simp only [repairOn_of_notMem hω]
    exact continuous_const
omit [MeasurableSpace Ω] in
/-- The repaired path agrees with the original at every sample point of the good set. -/
theorem repairOn_eq_on {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ} {ω : Ω} (hω : ω ∈ G) :
    (fun t => repairOn G X t ω) = fun t => X t ω :=
  funext fun t => repairOn_of_mem hω t
/-- On the augmented filtration a set of full measure is measurable at every nonnegative time. -/
theorem measurableSet_augFiltration_of_full {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {G : Set Ω}
    (hGm : MeasurableSet G) (hG : P Gᶜ = 0) {t : ℝ} (ht : 0 ≤ t) :
    MeasurableSet[LevyStochCalc.Brownian.augFiltration ℱ P t] G := by
  have h0 : MeasurableSet[LevyStochCalc.Brownian.augFiltration ℱ P 0] G := by
    have := LevyStochCalc.Brownian.measurableSet_augFiltration_of_null ℱ P hGm.compl hG
    simpa using this.compl
  exact (LevyStochCalc.Brownian.augFiltration ℱ P).mono ht _ h0
/-- The repaired path is adapted to the augmented filtration whenever the original is adapted to
the filtration itself. -/
theorem measurable_augFiltration_repairOn {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {G : Set Ω}
    (hGm : MeasurableSet G) (hG : P Gᶜ = 0) {X : ℝ → Ω → Fin n → ℝ}
    (hX : ∀ t : ℝ, Measurable[ℱ t] (X t)) {t : ℝ} (ht : 0 ≤ t) :
    Measurable[LevyStochCalc.Brownian.augFiltration ℱ P t] (repairOn G X t) := by
  classical
  have hGaug : MeasurableSet[LevyStochCalc.Brownian.augFiltration ℱ P t] G :=
    measurableSet_augFiltration_of_full hGm hG ht
  have hXaug : Measurable[LevyStochCalc.Brownian.augFiltration ℱ P t] (X t) :=
    (hX t).mono (LevyStochCalc.Brownian.le_augFiltration ℱ P t) le_rfl
  have heq : repairOn G X t = fun ω => if ω ∈ G then X t ω else 0 := by
    funext ω
    by_cases hω : ω ∈ G <;> simp [repairOn, hω]
  rw [heq]
  exact Measurable.ite hGaug hXaug measurable_const
end Repair

section MarkCut

open LevyStochCalc.Probability

universe u₃ v₃

variable {Ω : Type u₃} [MeasurableSpace Ω] {E : Type v₃} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end MarkCut

section ZeroExtension

open LevyStochCalc.Probability LevyStochCalc.Poisson.Compensated

universe u₄ v₄

variable {Ω : Type u₄} [MeasurableSpace Ω] {E : Type v₄} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end ZeroExtension

section Duplicates

universe u₂ v₂

variable {E : Type v₂} [MeasurableSpace E] {n d : ℕ}

end Duplicates

end LevyStochCalc.Ito.JumpFormula



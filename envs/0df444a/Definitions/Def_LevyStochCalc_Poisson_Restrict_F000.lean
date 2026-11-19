-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_Restrict_F000
-- name    : LevyStochCalc_Poisson_Restrict_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:20:23.688598+00:00
-- url     : https://prove2.me/theorems/6a22c044-01fc-4518-a4a5-8f40d4d3240c
-- title:
--   Source declarations: LevyStochCalc.Poisson.Restrict
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.Restrict. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Restricting a Poisson random measure to a mark set

Restricting the marks of a Poisson random measure to a measurable set `A` gives a Poisson random
measure with the restricted intensity: every structural field is the corresponding field of the
original evaluated on the intersection with `ℝ × A`.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- Restricting the intensity to a mark set restricts the reference intensity to `ℝ × A`. -/
theorem referenceIntensity_restrict (A : Set E) :
    referenceIntensity (ν.restrict A) = (referenceIntensity ν).restrict (Set.univ ×ˢ A) := by
  rw [referenceIntensity, referenceIntensity]
  conv_lhs => rw [← Measure.restrict_univ (μ := volume.restrict (Set.Ici (0 : ℝ)))]
  rw [Measure.prod_restrict]
theorem referenceIntensity_restrict_apply (A : Set E) {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    referenceIntensity (ν.restrict A) B = referenceIntensity ν (B ∩ Set.univ ×ˢ A) := by
  rw [referenceIntensity_restrict A, Measure.restrict_apply hB]
/-- **The restriction of a Poisson random measure to a mark set.** -/
noncomputable def PoissonRandomMeasure.restrict (N : PoissonRandomMeasure P ν) {A : Set E}
    (hA : MeasurableSet A) : PoissonRandomMeasure P (ν.restrict A) where
  N ω := (N.N ω).restrict (Set.univ ×ˢ A)
  measurable_eval {B} hB := by
    simp only [Measure.restrict_apply hB]
    exact N.measurable_eval (hB.inter (MeasurableSet.univ.prod hA))
  integer_valued {B} hB hfin := by
    simp only [Measure.restrict_apply hB]
    rw [referenceIntensity_restrict_apply A hB] at hfin
    exact N.integer_valued (hB.inter (MeasurableSet.univ.prod hA)) hfin
  infinite_at_infinite_intensity {B} hB hinf := by
    simp only [Measure.restrict_apply hB]
    rw [referenceIntensity_restrict_apply A hB] at hinf
    exact N.infinite_at_infinite_intensity (hB.inter (MeasurableSet.univ.prod hA)) hinf
  poisson_law {B} hB hfin := by
    have hfin' : referenceIntensity ν (B ∩ Set.univ ×ˢ A) ≠ ⊤ := by
      rwa [referenceIntensity_restrict_apply A hB] at hfin
    have hfun : (fun ω => ((N.N ω).restrict (Set.univ ×ˢ A)) B)
        = fun ω => N.N ω (B ∩ Set.univ ×ˢ A) := by
      funext ω; exact Measure.restrict_apply hB
    rw [hfun, referenceIntensity_restrict_apply A hB]
    exact N.poisson_law (hB.inter (MeasurableSet.univ.prod hA)) hfin'
  independent_disjoint {ι} _ B hBm hBd := by
    have hfun : (fun (i : ι) (ω : Ω) => ((N.N ω).restrict (Set.univ ×ˢ A)) (B i))
        = fun (i : ι) (ω : Ω) => N.N ω (B i ∩ Set.univ ×ˢ A) := by
      funext i ω; exact Measure.restrict_apply (hBm i)
    rw [hfun]
    refine N.independent_disjoint (fun i => B i ∩ Set.univ ×ˢ A)
      (fun i => (hBm i).inter (MeasurableSet.univ.prod hA)) ?_
    intro i j hij
    exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hBd hij)
  joint_past_future_independent {s t} hs hst {A'} hA' hA'ν := by
    have hA'A : ν (A' ∩ A) ≠ ⊤ := by
      rwa [Measure.restrict_apply hA'] at hA'ν
    have hfut : (fun ω => ((N.N ω).restrict (Set.univ ×ˢ A)) (Set.Ioc s t ×ˢ A'))
        = fun ω => N.N ω (Set.Ioc s t ×ˢ (A' ∩ A)) := by
      funext ω
      rw [Measure.restrict_apply (measurableSet_Ioc.prod hA'), Set.prod_inter_prod,
        Set.inter_univ]
    rw [hfut]
    refine indep_of_indep_of_le_left
      (N.joint_past_future_independent hs hst (hA'.inter hA) hA'A) ?_
    refine iSup₂_le fun B hB => ?_
    have hfun : (fun ω => ((N.N ω).restrict (Set.univ ×ˢ A)) B)
        = fun ω => N.N ω (B ∩ Set.univ ×ˢ A) := by
      funext ω; exact Measure.restrict_apply hB.2
    rw [hfun]
    exact le_iSup₂ (f := fun B (_ : B ∈ {C : Set (ℝ × E) |
      C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C}) =>
      MeasurableSpace.comap (fun ω => N.N ω B) inferInstance)
      (B ∩ Set.univ ×ˢ A)
      ⟨Set.inter_subset_left.trans hB.1, hB.2.inter (MeasurableSet.univ.prod hA)⟩
theorem PoissonRandomMeasure.restrict_apply (N : PoissonRandomMeasure P ν) {A : Set E}
    (hA : MeasurableSet A) {B : Set (ℝ × E)} (hB : MeasurableSet B) (ω : Ω) :
    (N.restrict hA).N ω B = N.N ω (B ∩ Set.univ ×ˢ A) :=
  Measure.restrict_apply hB
end LevyStochCalc.Poisson



-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_Transport_F000
-- name    : LevyStochCalc_Poisson_Transport_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:20:49.929208+00:00
-- url     : https://prove2.me/theorems/f15cd990-4d2a-4f89-9dfa-73221d6ae1f3
-- title:
--   Source declarations: LevyStochCalc.Poisson.Transport
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.Transport. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
import Definitions.Def_LevyStochCalc_Probability_Transport_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson random measures along a measure-preserving map

If `h : Ω' → Ω` is measure preserving from `P'` to `P` and `N` is a Poisson random measure
on `(Ω, P)` with intensity `ν`, then `ω' ↦ N (h ω')` is a Poisson random measure on
`(Ω', P')` with the same intensity. Together with the Brownian analogue this puts a
Brownian motion and a Poisson random measure on one product space
(`LevyStochCalc/Driver/Existence.lean`).
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {Ω' : Type u} [MeasurableSpace Ω']
  {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ν : Measure E} [SigmaFinite ν]

/-- The Poisson random measure `ω' ↦ N (h ω')` obtained by pulling `N` back along a
measure-preserving map `h`; the intensity is unchanged. -/
noncomputable def PoissonRandomMeasure.comap (N : PoissonRandomMeasure P ν) {h : Ω' → Ω}
    (hmp : MeasurePreserving h P' P) : PoissonRandomMeasure P' ν where
  N := fun ω' => N.N (h ω')
  measurable_eval := fun hB => (N.measurable_eval hB).comp hmp.measurable
  integer_valued := fun hB hfin =>
    hmp.quasiMeasurePreserving.ae (N.integer_valued hB hfin)
  infinite_at_infinite_intensity := fun hB hinf =>
    hmp.quasiMeasurePreserving.ae (N.infinite_at_infinite_intensity hB hinf)
  poisson_law := by
    intro B hB hfin
    rw [show (fun ω' => N.N (h ω') B) = (fun ω => N.N ω B) ∘ h from rfl,
      ← Measure.map_map (N.measurable_eval hB) hmp.measurable, hmp.map_eq]
    exact N.poisson_law hB hfin
  independent_disjoint := fun B hB hd =>
    Probability.iIndepFun_comp_of_measurePreserving (fun i => N.measurable_eval (hB i))
      (N.independent_disjoint B hB hd) hmp
  joint_past_future_independent := by
    intro s t hs hst A hA hAν
    have key := Probability.indep_comap_of_measurePreserving hmp
      (m₁ := ⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance)
      (m₂ := MeasurableSpace.comap
        (fun ω => N.N ω (Set.Ioc s t ×ˢ A)) inferInstance)
      (iSup₂_le fun _ hB => (N.measurable_eval hB.2).comap_le)
      (N.measurable_eval (measurableSet_Ioc.prod hA)).comap_le
      (N.joint_past_future_independent hs hst hA hAν)
    simpa only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def]
      using key
@[simp]
lemma PoissonRandomMeasure.comap_apply (N : PoissonRandomMeasure P ν) {h : Ω' → Ω}
    (hmp : MeasurePreserving h P' P) (ω' : Ω') : (N.comap hmp).N ω' = N.N (h ω') := rfl
end LevyStochCalc.Poisson



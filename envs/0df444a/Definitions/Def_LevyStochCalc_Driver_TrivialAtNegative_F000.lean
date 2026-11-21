-- Prove2me | Definitions.Def_LevyStochCalc_Driver_TrivialAtNegative_F000
-- name    : LevyStochCalc_Driver_TrivialAtNegative_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:20:16.965942+00:00
-- url     : https://prove2.me/theorems/37345c2e-2ca7-4f36-837a-c4e4167a4ff8
-- title:
--   Source declarations: LevyStochCalc.Driver.TrivialAtNegative
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.TrivialAtNegative. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_LevyStochCalc_Poisson_ZeroIntensity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint filtration of a Lévy driver at non-positive times

A Brownian motion vanishes almost surely at every time `u ≤ 0` and a Poisson random measure
carries no points at or before time `0`, so each generator of the joint filtration
`LevyStochCalc.Driver.LevyDriver.filtration` at a time `s ≤ 0` is almost surely constant. Hence
every set of `D.filtration s` is null or conull, and the same holds for the right-continuous
version at a time `s < 0`, which sits inside `D.filtration 0`.

## Main statements

* `LevyDriver.filtration_le_trivialSigma` — `D.filtration s ≤ trivialSigma` for `s ≤ 0`.
* `LevyDriver.isTrivialSigma_filtration` — `D.filtration s` is `P`-trivial for `s < 0`.
* `LevyDriver.isTrivialSigma_rightCont_filtration` — `(D.filtration)₊ s` is `P`-trivial
  for `s < 0`.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- The natural filtration of a Brownian motion at a non-positive time consists of null or
conull sets. -/
theorem naturalFiltration_le_trivialSigma (W : Brownian.BrownianMotion P) {s : ℝ} (hs : s ≤ 0) :
    Brownian.Martingale.naturalFiltration W s
      ≤ Probability.trivialSigma ‹MeasurableSpace Ω› P := by
  have hseq : Brownian.Martingale.naturalFiltration W s
      = ⨆ j ≤ s, MeasurableSpace.comap (W.W j) inferInstance := rfl
  rw [hseq]
  refine iSup₂_le fun j hj => Probability.comap_le_trivialSigma (y := 0) (W.measurable_eval j) ?_
  rcases lt_or_eq_of_le (hj.trans hs) with h | h
  · exact W.negative_zero j h
  · subst h
    exact W.initial_zero
/-- The natural filtration of a Poisson random measure at a non-positive time consists of null or
conull sets. -/
theorem naturalFiltration_poisson_le_trivialSigma (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν)
    {s : ℝ} (hs : s ≤ 0) :
    Poisson.naturalFiltration N s ≤ Probability.trivialSigma ‹MeasurableSpace Ω› P := by
  have hseq : Poisson.naturalFiltration N s
      = ⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance := rfl
  rw [hseq]
  refine iSup₂_le fun B hB =>
    Probability.comap_le_trivialSigma (y := 0) (N.measurable_eval hB.2) ?_
  have hBsub : B ⊆ Set.Iic (0 : ℝ) ×ˢ Set.univ :=
    hB.1.trans (Set.prod_mono (Set.Iic_subset_Iic.mpr hs) le_rfl)
  have hBeq : B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ = B := Set.inter_eq_self_of_subset_left hBsub
  have h0 : Poisson.referenceIntensity ν B = 0 := by
    have hint := Poisson.referenceIntensity_inter_Iic_zero (ν := ν) B
    rwa [hBeq] at hint
  exact Poisson.ae_count_eq_zero_of_intensity_eq_zero N hB.2 h0
namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

/-- The joint filtration of a Lévy driver at a non-positive time consists of null or conull
sets. -/
theorem filtration_le_trivialSigma {s : ℝ} (hs : s ≤ 0) :
    D.filtration s ≤ Probability.trivialSigma ‹MeasurableSpace Ω› P := by
  rw [D.filtration_apply, Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_apply]
  exact sup_le (iSup_le fun i => naturalFiltration_le_trivialSigma (D.W.W i) hs)
    (naturalFiltration_poisson_le_trivialSigma D.N hs)
/-- Every set of the joint filtration at a non-positive time has measure `0` or `1`. -/
theorem isTrivialSigma_filtration_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    Probability.IsTrivialSigma P (D.filtration s) := fun A hA =>
  (D.filtration_le_trivialSigma hs A hA).2
/-- Every set of the joint filtration at a negative time has measure `0` or `1`. -/
theorem isTrivialSigma_filtration {s : ℝ} (hs : s < 0) :
    Probability.IsTrivialSigma P (D.filtration s) :=
  D.isTrivialSigma_filtration_of_nonpos hs.le
/-- The right-continuous version of the joint filtration at a negative time is contained in the
joint filtration at time `0`. -/
theorem rightCont_filtration_le_filtration_zero {s : ℝ} (hs : s < 0) :
    (D.filtration).rightCont s ≤ D.filtration 0 := by
  rw [Filtration.rightCont_eq]
  exact iInf₂_le (0 : ℝ) hs
/-- Every set of the right-continuous joint filtration at a negative time has measure `0`
or `1`. -/
theorem isTrivialSigma_rightCont_filtration {s : ℝ} (hs : s < 0) :
    Probability.IsTrivialSigma P ((D.filtration).rightCont s) := fun A hA =>
  D.isTrivialSigma_filtration_of_nonpos le_rfl A (D.rightCont_filtration_le_filtration_zero hs A hA)
end LevyDriver

end LevyStochCalc.Driver



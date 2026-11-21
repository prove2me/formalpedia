-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
-- name    : LevyStochCalc_Driver_CrossElementary_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:35:56.314241+00:00
-- url     : https://prove2.me/theorems/cb79ea43-901a-44a2-92a2-e18f3334356e
-- title:
--   Source declarations: LevyStochCalc.Driver.CrossElementary
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CrossElementary. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CrossFiltration_F000
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One cross term between the two drivers

A Brownian increment weighted at its left endpoint, against a compensated mass weighted at its
left endpoint, has zero mean: whichever of the two cells starts later, its increment is centred
given an enlargement of the filtration carrying the whole path of the other driver, and the
remaining factor is measurable there.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

/-- Two enlargements of a filtration `ℱ` making a cross term conditionable: one for which `N` is
a Poisson random measure and every Brownian increment is measurable, and one for which every
coordinate is a Brownian motion and every compensated mass is measurable. -/
structure CrossWitness (D : LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) where
  /-- The enlargement carrying the whole Brownian path. -/
  poissonLarger : Filtration ℝ ‹MeasurableSpace Ω›
  /-- It contains `ℱ`. -/
  poisson_le : ∀ s, ℱ s ≤ poissonLarger s
  /-- `N` is a Poisson random measure for it. -/
  isPoisson : Poisson.IsPoissonFiltration D.N poissonLarger
  /-- Brownian increments are measurable there at every time. -/
  measurable_increment : ∀ (i : Fin d) (s p q : ℝ),
    Measurable[poissonLarger s] fun ω => (D.W.W i).W q ω - (D.W.W i).W p ω
  /-- The enlargement carrying the whole Poisson path. -/
  brownianLarger : Filtration ℝ ‹MeasurableSpace Ω›
  /-- It contains `ℱ`. -/
  brownian_le : ∀ s, ℱ s ≤ brownianLarger s
  /-- Every coordinate is a Brownian motion for it. -/
  isBrownian : ∀ i, Brownian.IsBrownianFiltration (D.W.W i) brownianLarger
  /-- Compensated masses are measurable there at every time. -/
  stronglyMeasurable_compensated : ∀ (s : ℝ) {B : Set (ℝ × E)}, MeasurableSet B →
    StronglyMeasurable[brownianLarger s] fun ω => D.N.compensated B ω
/-- The joint natural filtration is witnessed by the two enlargements. -/
noncomputable def crossWitness (D : LevyDriver.{u, v, w} P d ν) : CrossWitness D D.filtration where
  poissonLarger := D.crossPoissonFiltration
  poisson_le := D.filtration_le_crossPoisson
  isPoisson := D.isPoissonFiltration_crossPoisson
  measurable_increment := D.measurable_increment_crossPoisson
  brownianLarger := D.crossBrownianFiltration
  brownian_le := D.filtration_le_crossBrownian
  isBrownian := D.isBrownianFiltration_crossBrownian
  stronglyMeasurable_compensated := fun s _ hB =>
    D.stronglyMeasurable_compensated_crossBrownian s hB
/-- Augmenting by the null sets preserves a witness. -/
noncomputable def CrossWitness.aug {D : LevyDriver.{u, v, w} P d ν}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (𝒲 : CrossWitness D ℱ) :
    CrossWitness D (Brownian.augFiltration ℱ P) where
  poissonLarger := Brownian.augFiltration 𝒲.poissonLarger P
  poisson_le := fun _ => Probability.aug_mono (𝒲.poisson_le _)
  isPoisson := Poisson.isPoissonFiltration_augFiltration 𝒲.isPoisson
  measurable_increment := fun i s p q =>
    (𝒲.measurable_increment i s p q).mono
      (Brownian.le_augFiltration 𝒲.poissonLarger P s) le_rfl
  brownianLarger := Brownian.augFiltration 𝒲.brownianLarger P
  brownian_le := fun _ => Probability.aug_mono (𝒲.brownian_le _)
  isBrownian := fun i => Brownian.isBrownianFiltration_augFiltration (𝒲.isBrownian i)
  stronglyMeasurable_compensated := fun s _ hB =>
    (𝒲.stronglyMeasurable_compensated s hB).mono
      (Brownian.le_augFiltration 𝒲.brownianLarger P s)
section CrossTerm

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end CrossTerm

end LevyDriver

end LevyStochCalc.Driver



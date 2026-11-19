-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F002
-- name    : BrownianMotion_Auxiliary_MeasureTheory_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:12:43.182305+00:00
-- url     : https://prove2.me/theorems/78fc2fde-633d-4220-b5f3-785e49c92bd7
-- title:
--   Source declarations: BrownianMotion.Auxiliary.MeasureTheory
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Auxiliary.MeasureTheory. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Algebra_F000
import Definitions.Def_BrownianMotion_Auxiliary_Metric_F000
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.ZeroOne


/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

@[expose] public section

open MeasureTheory WithLp

open scoped ENNReal NNReal ProbabilityTheory

attribute [fun_prop] aemeasurable_id'

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)}

variable [∀ i, IsProbabilityMeasure (μ i)]

end iIndepFun

section covariance

end covariance

end ProbabilityTheory

--generalizing `MeasureTheory.Measure.addHaar_ball_center`

open Metric

section covariance

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y Z : Ω → ℝ} (c : ℝ)

end ProbabilityTheory

open ProbabilityTheory MeasurableSpace

lemma Indep.singleton_indepSets {Ω : Type*} {m1 m2 mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (h : Indep m1 m2 P) {A : Set Ω}
    (hA : MeasurableSet[m1] A) : IndepSets {A} {s | MeasurableSet[m2] s} P := by
  have := (Indep_iff_IndepSets m1 m2 P).1 h
  apply indepSets_of_indepSets_of_le_left this
  simpa
lemma measurableSpace_le_iff {Ω : Type*} {m1 m2 : MeasurableSpace Ω} :
    m1 ≤ m2 ↔ ∀ s, MeasurableSet[m1] s → MeasurableSet[m2] s := by aesop
end covariance



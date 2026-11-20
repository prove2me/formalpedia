-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ChainRule_F000
-- name    : LevyStochCalc_Poisson_ChainRule_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:56:38.606719+00:00
-- url     : https://prove2.me/theorems/fa959444-6ae9-420e-8c76-51a85a9b7cad
-- title:
--   Source declarations: LevyStochCalc.Poisson.ChainRule
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ChainRule. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpSum_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump chain rule for a Poisson random measure

A product over a finite set whose factors are ordered by a key telescopes: the product minus one
is the sum, over the factors, of the product of the earlier ones times the increment of that
factor. On a set of finite reference intensity a Poisson random measure is a finite sum of unit
masses at distinct times, so the exponential of an integral against it obeys that telescoping,
which is the chain rule the exponential family needs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

section Telescope

variable {α : Type*} [DecidableEq α] {K : Type*} [LinearOrder K] {M : Type*} [CommRing M]

end Telescope

section Pathwise

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The Bochner integral against a finite sum of Dirac masses, in a normed space. -/
theorem integral_of_eq_sum_dirac' {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure α} [IsFiniteMeasure μ]
    {s : Finset α} (hμ : μ = ∑ p ∈ s, μ {p} • Measure.dirac p) (g : α → F) :
    ∫ a, g a ∂μ = ∑ p ∈ s, (μ {p}).toReal • g p := by
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure fun p _ =>
    (integrable_dirac (by simp)).smul_measure (measure_ne_top μ _)]
  exact Finset.sum_congr rfl fun p _ => by rw [integral_smul_measure, integral_dirac]
/-- The integral of `h` against the points of `B` in `(0, t]`. -/
noncomputable def windowSum (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (h : ℝ × E → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∫ p in B ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ, h p ∂(N.N ω)
/-- The integral of `h` against the points of `B` strictly before `t`. -/
noncomputable def windowSumStrict (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E))
    (h : ℝ × E → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ p in B ∩ Set.Ioo (0 : ℝ) t ×ˢ Set.univ, h p ∂(N.N ω)
end Pathwise

end LevyStochCalc.Poisson



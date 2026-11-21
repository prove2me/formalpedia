-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_CadlagVectorIntegral_F000
-- name    : LevyStochCalc_Brownian_CadlagVectorIntegral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:57:33.328266+00:00
-- url     : https://prove2.me/theorems/eb5781ca-082d-4621-ae9c-f06b42f3e543
-- title:
--   Source declarations: LevyStochCalc.Brownian.CadlagVectorIntegral
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.CadlagVectorIntegral. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MultidimIto_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F003
import Definitions.Def_LevyStochCalc_Ito_PicardOutputStepDiff_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F003
import Definitions.Def_LevyStochCalc_Martingale_CadlagModification_F000
import Definitions.Def_LevyStochCalc_Martingale_CadlagModification_F001
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# An everywhere-càdlàg version of the multidimensional Brownian integral

The multidimensional `L²` Itô integral `∫_0^t Z_s · dW_s = ∑_i ∫_0^t Z_s^i dW_s^i` is defined
separately at each time, so it carries no path regularity. Each coordinate integral has an
adapted modification with almost surely càdlàg paths; when the null set on which the paths fail
to be càdlàg belongs to `ℱ 0` and the filtration is constant before time `0`, that modification
can be replaced by `0` there, which makes every path càdlàg. Summing the `d` coordinate
modifications gives a version of the vector integral that is adapted to the right-continuous
filtration, jointly measurable, càdlàg at every sample point and a martingale.

## Main statements

* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.martingale_finsetSum` — a finite sum
  of martingales is a martingale.
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral`
  — the multidimensional Brownian integral has an everywhere-càdlàg martingale version.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ}

omit [IsProbabilityMeasure P] in
/-- A finite sum of martingales is a martingale. -/
theorem martingale_finsetSum {ι : Type v} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (s : Finset ι) (F : ι → ℝ → Ω → ℝ) (hF : ∀ i ∈ s, Martingale (F i) ℱ P) :
    Martingale (fun t ω => ∑ i ∈ s, F i t ω) ℱ P := by
  have hsum : Martingale (∑ i ∈ s, F i) ℱ P :=
    Finset.sum_induction F (fun G => Martingale G ℱ P) (fun _ _ ha hb => ha.add hb)
      (martingale_zero ℝ ℱ P) hF
  have heq : (∑ i ∈ s, F i) = fun t ω => ∑ i ∈ s, F i t ω := by
    funext t ω
    simp
  rwa [heq] at hsum
end MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim



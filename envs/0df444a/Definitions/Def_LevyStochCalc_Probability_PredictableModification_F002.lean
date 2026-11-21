-- Prove2me | Definitions.Def_LevyStochCalc_Probability_PredictableModification_F002
-- name    : LevyStochCalc_Probability_PredictableModification_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:49:01.017119+00:00
-- url     : https://prove2.me/theorems/7322a341-494d-41f5-9731-aeacd38cb3e8
-- title:
--   LevyStochCalc source module: LevyStochCalc.Probability.PredictableModification
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Probability.PredictableModification in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F000
import Definitions.Def_LevyStochCalc_Probability_Predictable_F000
import Definitions.Def_SourceProof_ab7eaa8ef4ca09c9e29c494e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of progressive integrands

The elementary integrands of the `L²` theory — finite sums of a coefficient measurable at the
left endpoint of a cell, carried on that cell — are predictable, and the predictable processes
are closed under pointwise upper limits. Since the elementary integrands are dense in the
progressive integrands of finite energy, a progressive integrand agrees with a predictable one
almost everywhere in time and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

section Cells

end Cells

section Modification

open Brownian.Ito

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **An admissible horizon integrand has a predictable version.** -/
theorem exists_predictable_ae_eq_horizonIntegrand (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ}
    (hT : 0 < T) (G : HorizonIntegrand P ℱ T) :
    ∃ K : Ω → ℝ → ℝ, Predictable ℱ K ∧
      (fun p : Ω × ℝ => G.toFun p.1 p.2) =ᵐ[energyMeasure P T] fun p : Ω × ℝ => K p.1 p.2 :=
  _root_.Prove2MeSourceProof.h_ab7eaa8ef4ca09c9e29c494e ℱ G.measurable_uncurry G.progressive hT G.energy_ne_top
end Modification

end LevyStochCalc.Probability



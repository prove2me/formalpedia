-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000
-- name    : LevyStochCalc_Brownian_ItoDriverLinear_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:29:26.109551+00:00
-- url     : https://prove2.me/theorems/8f4ca856-fe3d-46ea-bc52-dec096162875
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.ItoDriverLinear
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.ItoDriverLinear in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000
import Definitions.Def_LevyStochCalc_Brownian_LinearCombination_F000
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the Itô integral in the driver

The elementary integral of a simple integrand against a linear combination of Brownian motions is
the corresponding combination of the elementary integrals, and both sides of the resulting
identity are `L²`-limits along the same approximating sequence, so the identity passes to the
`L²` Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The elementary integral against a linear combination is the combination of the elementary
integrals. -/
theorem simpleIntegral_combineBM (W : Multidim.MultidimBrownianMotion P d) {c : Fin d → ℝ}
    (hc : ∑ i, c i ^ 2 = 1) {T : ℝ} (G : SimplePredictable Ω T) (t : ℝ) (ω : Ω) :
    simpleIntegral (Multidim.MultidimBrownianMotion.combineBM W hc) G t ω
      = ∑ i, c i * simpleIntegral (W.W i) G t ω := by
  simp only [simpleIntegral]
  have hstep : ∀ k : Fin G.N,
      G.ξ k ω * ((Multidim.MultidimBrownianMotion.combineBM W hc).W
            (min (G.partition k.succ) t) ω
          - (Multidim.MultidimBrownianMotion.combineBM W hc).W
            (min (G.partition k.castSucc) t) ω)
        = ∑ i, c i * (G.ξ k ω * ((W.W i).W (min (G.partition k.succ) t) ω
            - (W.W i).W (min (G.partition k.castSucc) t) ω)) := by
    intro k
    change G.ξ k ω * (Multidim.MultidimBrownianMotion.combine W c _ ω
      - Multidim.MultidimBrownianMotion.combine W c _ ω) = _
    rw [Multidim.MultidimBrownianMotion.combine_sub, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
end LevyStochCalc.Brownian.Ito



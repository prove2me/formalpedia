-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F001
-- name    : LevyStochCalc_Brownian_ItoSimpleIntegrand_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:49:21.914371+00:00
-- url     : https://prove2.me/theorems/ca793bd0-04d8-4108-a312-3d5679964591
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.ItoSimpleIntegrand
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.ItoSimpleIntegrand in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple predictable integrands and the elementary Brownian integral

The class `SimplePredictable` of integrands `∑_i ξ_i · 1_{(t_i, t_{i+1}]}` with bounded
measurable coefficients, their pointwise evaluation `SimplePredictable.eval`, the elementary
integral `simpleIntegral` against a scalar Brownian motion `W`, and the energy
`∫⁻ ‖H.eval s ω‖₊ ^ 2` of the integrand, which the disjointness of the partition intervals
`(t_i, t_{i+1}]` turns into the sum `∑_i (t_{i+1} - t_i) · ∫⁻ ‖ξ_i‖₊ ^ 2 ∂P`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The simple integral at time `0` is identically zero (each term is
`ξ_i · (W_{0∧0} − W_{0∧0}) = ξ_i · 0`). -/
lemma simpleIntegral_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    simpleIntegral W H 0 ω = 0 := by
  unfold simpleIntegral
  -- Each summand: ξ_i ω · (W (min partition_succ 0) ω − W (min partition_castSucc 0) ω).
  -- By H.partition_zero = 0 and H.partition_strictMono, partition i ≥ 0 for i ≥ 0,
  -- so min(partition_succ, 0) = 0 and similarly for castSucc.
  -- Hence each term is ξ_i ω · (W 0 ω − W 0 ω) = ξ_i ω · 0 = 0.
  apply Finset.sum_eq_zero
  intro i _
  -- Show: H.partition i.succ ≥ 0 and H.partition i.castSucc ≥ 0.
  have h_zero_le_castSucc : H.partition 0 ≤ H.partition i.castSucc :=
    H.partition_strictMono.monotone (Fin.zero_le i.castSucc)
  have h_zero_le_succ : H.partition 0 ≤ H.partition i.succ :=
    H.partition_strictMono.monotone (Fin.zero_le i.succ)
  rw [H.partition_zero] at h_zero_le_castSucc h_zero_le_succ
  rw [min_eq_right h_zero_le_succ, min_eq_right h_zero_le_castSucc]
  ring
end LevyStochCalc.Brownian.Ito



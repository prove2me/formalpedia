-- Prove2me | Definitions.Def_SourceProof_c270d540a1c5354737ac7c4b
-- name    : SourceProof_c270d540a1c5354737ac7c4b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:04:55.012654+00:00
-- url     : https://prove2.me/theorems/9c5b2e36-463b-42f3-a2dc-67b11cee6bed
-- title:
--   LevyStochCalc source module: SourceProof_c270d540a1c5354737ac7c4b
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.SimplePredictable.referenceIntensity_fullRect` comes from the `LevyStochCalc.Poisson.CompensatedSimple` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_c270d540a1c5354737ac7c4b
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)
      = ENNReal.ofReal (φ.partition i.succ - φ.partition i.castSucc) * ν (φ.A i) := by
  unfold LevyStochCalc.Poisson.Compensated.SimplePredictable.fullRect LevyStochCalc.Poisson.referenceIntensity
  rw [MeasureTheory.Measure.prod_prod]
  congr 1
  -- volume.restrict [0,∞) (Ioc t_i t_{i+1}) = volume (Ioc t_i t_{i+1})
  -- (since t_i ≥ 0, the interval is in [0,∞))
  have h_t_i_nn : 0 ≤ φ.partition i.castSucc := by
    have : φ.partition 0 ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.zero_le _)
    rw [φ.partition_zero] at this
    exact this
  have h_subset :
      Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    exact h_t_i_nn.trans (le_of_lt hx.1)
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  rw [Set.inter_eq_left.mpr h_subset]
  rw [Real.volume_Ioc]
end LevyStochCalc.Poisson.Compensated



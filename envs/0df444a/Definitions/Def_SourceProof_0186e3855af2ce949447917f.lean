-- Prove2me | Definitions.Def_SourceProof_0186e3855af2ce949447917f
-- name    : SourceProof_0186e3855af2ce949447917f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:29:59.22188+00:00
-- url     : https://prove2.me/theorems/c5e4eeab-25a0-4267-aa04-f6ae7a1dd0f1
-- title:
--   LevyStochCalc source module: SourceProof_0186e3855af2ce949447917f
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_zero` comes from the `LevyStochCalc.Poisson.CompensatedSimple` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F004

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


theorem _root_.Prove2MeSourceProof.h_0186e3855af2ce949447917f
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (ω : Ω) :
    simpleIntegral N φ 0 ω = 0 := by
  unfold LevyStochCalc.Poisson.Compensated.simpleIntegral
  apply Finset.sum_eq_zero
  intro i _
  -- Show: φ.timeRect i 0 = ∅, hence compensated value = 0.
  have h_zero_le_castSucc : φ.partition 0 ≤ φ.partition i.castSucc :=
    φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
  have h_zero_le_succ : φ.partition 0 ≤ φ.partition i.succ :=
    φ.partition_strictMono.monotone (Fin.zero_le i.succ)
  rw [φ.partition_zero] at h_zero_le_castSucc h_zero_le_succ
  have h_min_castSucc : min (φ.partition i.castSucc) 0 = 0 :=
    min_eq_right h_zero_le_castSucc
  have h_min_succ : min (φ.partition i.succ) 0 = 0 := min_eq_right h_zero_le_succ
  have h_rect_empty : φ.timeRect i 0 = ∅ := by
    unfold LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect
    rw [h_min_castSucc, h_min_succ]
    rw [Set.Ioc_self]
    exact Set.empty_prod
  rw [h_rect_empty]
  -- compensated of ∅ is 0
  unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
  simp
end LevyStochCalc.Poisson.Compensated



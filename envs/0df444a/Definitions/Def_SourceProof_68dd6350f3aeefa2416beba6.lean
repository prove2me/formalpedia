-- Prove2me | Definitions.Def_SourceProof_68dd6350f3aeefa2416beba6
-- name    : SourceProof_68dd6350f3aeefa2416beba6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:48:59.733643+00:00
-- url     : https://prove2.me/theorems/2c61ecf7-3931-4fb4-938e-7e75dde811db
-- title:
--   LevyStochCalc source module: SourceProof_68dd6350f3aeefa2416beba6
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.measurable_markedStopped` comes from the `LevyStochCalc.Ito.CompensatedLocalityCutoff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The marked integrand cut off at a stopping time

The marked process `markedStopped τ φ`, which agrees with `φ` at the times a stopping time `τ`
has not passed and vanishes afterwards, is dominated pointwise by `φ` and inherits from it joint
measurability, marked progressive measurability and finite energy; those three admissibility
properties transport along an equality of marked integrands and are stable under differences.

## Main definitions

* `markedStopped τ φ` — the marked process `φ` cut off at the stopping time `τ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section MarkedStopped

variable (τ : Ω → WithTop ℝ) (φ : Ω → ℝ → E → ℝ)

variable {τ φ}


theorem _root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 (hτ : IsStoppingTime ℱ τ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) :
    Measurable fun p : Ω × ℝ × E => markedStopped τ φ p.1 p.2.1 p.2.2 := by
  set S : Set (Ω × ℝ × E) := {p | (p.1, p.2.1) ∈ LevyStochCalc.Probability.stoppedSet τ}
    with hS
  have hfun : (fun p : Ω × ℝ × E => LevyStochCalc.Poisson.Compensated.markedStopped τ φ p.1 p.2.1 p.2.2)
      = S.indicator fun p => φ p.1 p.2.1 p.2.2 := by
    funext p
    by_cases hp : ((p.2.1 : ℝ) : WithTop ℝ) ≤ τ p.1
    · rw [Set.indicator_of_mem (show p ∈ S from hp)]
      exact if_pos hp
    · rw [Set.indicator_of_notMem (show p ∉ S from hp)]
      exact if_neg hp
  rw [hfun]
  exact hm.indicator ((_root_.Prove2MeSourceProof.h_b85c983107ceb7c8ce4a3574 hτ).preimage
    (measurable_fst.prodMk measurable_snd.fst))
end MarkedStopped

section Transport

variable {φ ψ : Ω → ℝ → E → ℝ}

end Transport

end LevyStochCalc.Poisson.Compensated



-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F000
-- name    : LevyStochCalc_Ito_CompensatedLocalityCutoff_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:45:13.039292+00:00
-- url     : https://prove2.me/theorems/6c559151-6cf4-43b8-8b3c-70c3f105eb1e
-- title:
--   Source declarations: LevyStochCalc.Ito.CompensatedLocalityCutoff
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CompensatedLocalityCutoff. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F000
import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F002

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

/-- A marked process cut off at a stopping time. -/
noncomputable def markedStopped (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  if ((s : ℝ) : WithTop ℝ) ≤ τ ω then φ ω s e else 0
omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem abs_markedStopped_le (ω : Ω) (s : ℝ) (e : E) :
    |markedStopped τ φ ω s e| ≤ |φ ω s e| := by
  rw [markedStopped]
  split_ifs
  · exact le_rfl
  · simp
omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem markedStopped_of_le {ω : Ω} {s : ℝ} (h : ((s : ℝ) : WithTop ℝ) ≤ τ ω) (e : E) :
    markedStopped τ φ ω s e = φ ω s e := if_pos h
omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem markedStopped_of_not_le {ω : Ω} {s : ℝ} (h : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω)
    (e : E) :
    markedStopped τ φ ω s e = 0 := if_neg h
variable {τ φ}

end MarkedStopped

section Transport

variable {φ ψ : Ω → ℝ → E → ℝ}

end Transport

end LevyStochCalc.Poisson.Compensated



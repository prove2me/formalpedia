-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
-- name    : MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:28.016439+00:00
-- url     : https://prove2.me/theorems/6c9127e9-400e-49b6-9487-6d9becd75114
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurability of random shifts of continuous paths

Shifting a continuous path by a Borel measurable random time, and evaluating it at that time,
are Borel measurable, because the deterministic shift and the evaluation are jointly continuous
in the time and the path.  A finite `NNReal`-valued stopping time for the canonical filtration is
such a random time.  No countable-range premise is used.

This is ordinary measurability infrastructure.  It proves no restart identity and no conditional
expectation formula; those are in `Trajectory/FellerStoppingRestart.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- Evaluating a path at a Borel measurable random time is Borel measurable. -/
theorem measurable_eval_of_measurable (T : ContinuousPath alpha → NNReal)
    (hT : Measurable T) :
    Measurable (fun omega : ContinuousPath alpha ↦ omega (T omega)) := by
  have hpair : Measurable (fun omega : ContinuousPath alpha ↦ (omega, T omega)) :=
    measurable_id.prodMk hT
  exact (ContinuousEval.continuous_eval (F := ContinuousPath alpha)).measurable.comp hpair

/-- A finite stopping time for the canonical filtration is Borel measurable. -/
theorem measurable_of_isStoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable T := by
  refine measurable_of_Iic fun i ↦ ?_
  have h := (canonicalFiltration (alpha := alpha)).le i _ (hT i)
  simpa only [Set.preimage, Set.mem_Iic, WithTop.coe_le_coe] using h



/-- The state at a finite stopping time for the canonical filtration is Borel measurable. -/
theorem measurable_eval_stoppingTime_borel (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable (fun omega : ContinuousPath alpha ↦ omega (T omega)) :=
  measurable_eval_of_measurable T (measurable_of_isStoppingTime T hT)

end ContinuousPath
end MarkovProcess



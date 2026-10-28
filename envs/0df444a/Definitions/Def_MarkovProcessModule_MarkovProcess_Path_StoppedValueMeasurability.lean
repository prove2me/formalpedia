-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Path_StoppedValueMeasurability
-- name    : MarkovProcessModule_MarkovProcess_Path_StoppedValueMeasurability
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:33:31.413082+00:00
-- url     : https://prove2.me/theorems/8788fc95-7d3d-439c-8710-18ffdf67b158
-- title:
--   MarkovProcess.Path.StoppedValueMeasurability
-- statement:
--   # Measurability of the state at a stopping time
--
--   The coordinate process of canonical continuous-path space is adapted to the canonical filtration
--   and continuous in time, hence progressively measurable.  Consequently the state at a finite
--   stopping time is measurable for the stopped sigma-algebra.  No countable-range premise is used.
--   Plain Borel measurability of the same map, under weaker assumptions, is in
--   `Path/RandomShiftMeasurability.lean`.
--
--   This is ordinary measurability infrastructure.  It proves no restart identity and no conditional
--   expectation formula; those are in `Trajectory/FellerStoppingRestart.lean` and
--   `Trajectory/FellerStoppingConditional.lean`.
--
--   Complete pinned Lean module MarkovProcess.Path.StoppedValueMeasurability by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/StoppedValueMeasurability.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Path_Basic
import Mathlib.Probability.Process.Stopping

/-!
# Measurability of the state at a stopping time

The coordinate process of canonical continuous-path space is adapted to the canonical filtration
and continuous in time, hence progressively measurable.  Consequently the state at a finite
stopping time is measurable for the stopped sigma-algebra.  No countable-range premise is used.
Plain Borel measurability of the same map, under weaker assumptions, is in
`Path/RandomShiftMeasurability.lean`.

This is ordinary measurability infrastructure.  It proves no restart identity and no conditional
expectation formula; those are in `Trajectory/FellerStoppingRestart.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- The coordinate process is adapted to the canonical filtration. -/
theorem adapted_coordinateProcess :
    StronglyAdapted (canonicalFiltration (alpha := alpha)) (coordinateProcess (alpha := alpha)) :=
  fun t ↦ (measurable_coordinateProcess_canonicalFiltration (alpha := alpha) t).stronglyMeasurable

/-- The coordinate process is progressively measurable for the canonical filtration. -/
theorem progMeasurable_coordinateProcess :
    IsStronglyProgressive (canonicalFiltration (alpha := alpha))
      (coordinateProcess (alpha := alpha)) :=
  adapted_coordinateProcess.isStronglyProgressive_of_continuous fun omega ↦ omega.continuous

/-- The state at a finite stopping time is measurable for the stopped sigma-algebra. -/
theorem measurable_eval_stoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable[hT.measurableSpace] (fun omega ↦ omega (T omega)) := by
  have h := measurable_stoppedValue (progMeasurable_coordinateProcess (alpha := alpha)) hT
  simpa only [stoppedValue, coordinateProcess_apply] using! h

end ContinuousPath
end MarkovProcess



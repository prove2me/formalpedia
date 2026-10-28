-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_ClampedCoordinate
-- name    : MarkovProcessModule_MarkovProcess_Trajectory_ClampedCoordinate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:40:48.828841+00:00
-- url     : https://prove2.me/theorems/2059ef66-473b-4c57-8937-6263b8dfeae4
-- title:
--   MarkovProcess.Trajectory.ClampedCoordinate
-- statement:
--   # Measurability of clamped path coordinates
--
--   This file records the joint measurability of a continuous-path coordinate whose time argument is
--   clamped at a deterministic horizon.  It is the common progressive-measurability input for
--   adapted integral functionals.
--
--   Main result: `ContinuousPath.measurable_clampedCoordinate`.
--
--   No stochastic-process law or stopping-time identity is asserted.
--
--   Complete pinned Lean module MarkovProcess.Trajectory.ClampedCoordinate by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/ClampedCoordinate.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Path_StoppedValueMeasurability

/-!
# Measurability of clamped path coordinates

This file records the joint measurability of a continuous-path coordinate whose time argument is
clamped at a deterministic horizon.  It is the common progressive-measurability input for
adapted integral functionals.

Main result: `ContinuousPath.measurable_clampedCoordinate`.

No stochastic-process law or stopping-time identity is asserted.
-/

open MeasureTheory
open scoped NNReal

namespace MarkovProcess.ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- The coordinate at a real time clamped to `[0, t]` is jointly measurable for the Borel
structure in time and the canonical filtration at `t`. -/
theorem measurable_clampedCoordinate (t : NNReal) :
    Measurable[(borel ℝ).prod (canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦ p.2 (min (Real.toNNReal p.1) t)) := by
  have htime : Measurable[(borel ℝ).prod (canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦ min (Real.toNNReal p.1) t) :=
    (measurable_real_toNNReal.comp measurable_fst).min measurable_const
  have hpair : Measurable[(borel ℝ).prod (canonicalFiltration (alpha := alpha) t),
      Subtype.instMeasurableSpace.prod (canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦
        ((⟨min (Real.toNNReal p.1) t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Set.Iic t), p.2)) :=
    (Measurable.subtype_mk htime).prodMk measurable_snd
  exact ((progMeasurable_coordinateProcess (alpha := alpha) t).comp_measurable hpair).measurable

end MarkovProcess.ContinuousPath



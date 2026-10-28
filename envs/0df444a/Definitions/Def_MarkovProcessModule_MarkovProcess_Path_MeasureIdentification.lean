-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Path_MeasureIdentification
-- name    : MarkovProcessModule_MarkovProcess_Path_MeasureIdentification
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:41:07.668881+00:00
-- url     : https://prove2.me/theorems/5a6954ae-0e16-4b57-bf83-0d1255c74398
-- title:
--   MarkovProcess.Path.MeasureIdentification
-- statement:
--   # Identifying continuous-path measures from dense-time restrictions
--
--   A measure on continuous-path space is determined by its pushforward to the fixed dense time
--   carrier. This is the measure-level counterpart of continuous-path kernel identification and is a
--   deterministic property of continuous paths.
--
--   Complete pinned Lean module MarkovProcess.Path.MeasureIdentification by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/MeasureIdentification.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Continuity_DenseTimeContinuousExtension

/-!
# Identifying continuous-path measures from dense-time restrictions

A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. This is the measure-level counterpart of continuous-path kernel identification and is a
deterministic property of continuous paths.
-/

open MeasureTheory

namespace MarkovProcess
namespace Measure

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. -/
theorem map_denseRestriction_injective :
    Function.Injective
      (fun mu : MeasureTheory.Measure (ContinuousPath alpha) ↦
        mu.map ContinuousPath.denseRestriction) := by
  intro mu nu h
  ext s hs
  have himage : MeasurableSet (ContinuousPath.denseRestriction '' s) :=
    ContinuousPath.measurableEmbedding_denseRestriction.measurableSet_image' hs
  have hmap := congrArg
    (fun rho : MeasureTheory.Measure (DenseTime → alpha) ↦
      rho (ContinuousPath.denseRestriction '' s)) h
  dsimp only at hmap
  rw [MeasureTheory.Measure.map_apply ContinuousPath.measurable_denseRestriction himage,
    MeasureTheory.Measure.map_apply ContinuousPath.measurable_denseRestriction himage] at hmap
  simpa only [ContinuousPath.denseRestriction_injective.preimage_image] using hmap

/-- Equality of continuous-path measures is equivalent to equality after restriction to the fixed
dense time carrier. -/
theorem map_denseRestriction_eq_iff
    {mu nu : MeasureTheory.Measure (ContinuousPath alpha)} :
    mu.map ContinuousPath.denseRestriction = nu.map ContinuousPath.denseRestriction ↔
      mu = nu := by
  constructor
  · intro h
    exact map_denseRestriction_injective (alpha := alpha) h
  · intro h
    exact congrArg
      (fun rho : MeasureTheory.Measure (ContinuousPath alpha) ↦
        rho.map ContinuousPath.denseRestriction) h

end
end Measure
end MarkovProcess



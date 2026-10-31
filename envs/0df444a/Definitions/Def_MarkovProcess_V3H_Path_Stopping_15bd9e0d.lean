-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_Stopping_15bd9e0d
-- name    : MarkovProcess_V3H_Path_Stopping_15bd9e0d
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:27:54.871043+00:00
-- url     : https://prove2.me/theorems/dcd1125e-e744-400e-b681-ed9adf68aea1
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_Stopping_15bd9e0d
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic stopping of continuous paths

This file defines stopping a continuous path at a fixed deterministic time. It proves only
topological and Borel-measurability properties of this operation; it introduces no stopping
times or stochastic laws.
-/

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Clamp nonnegative time at the fixed deterministic time `T`. -/
def clampTime (T : NNReal) : C(NNReal, NNReal) where
  toFun t := min t T
  continuous_toFun := continuous_id.min continuous_const

@[simp]
theorem p2m_embedded_1265b9dfd498c786 (T t : NNReal) : clampTime T t = min t T := rfl

/-- A continuous path stopped at the fixed deterministic time `T`. -/
def stoppedPath (T : NNReal) (omega : ContinuousPath alpha) : ContinuousPath alpha :=
  omega.comp (clampTime T)

@[simp]
theorem stoppedPath_apply (T : NNReal) (omega : ContinuousPath alpha) (t : NNReal) :
    stoppedPath T omega t = omega (min t T) :=
  rfl

@[simp]
theorem p2m_embedded_e935722cb7003720 (T : NNReal) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : t ≤ T) : stoppedPath T omega t = omega t := by
  rw [stoppedPath_apply, min_eq_left ht]

@[simp]
theorem p2m_embedded_1f66c03cc6051faf (T : NNReal) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : T ≤ t) : stoppedPath T omega t = omega T := by
  rw [stoppedPath_apply, min_eq_right ht]







/-- Successive deterministic stops combine by taking the earlier stopping time. -/
@[simp]
theorem p2m_embedded_c75f84031746de2b (S T : NNReal) (omega : ContinuousPath alpha) :
    stoppedPath S (stoppedPath T omega) = stoppedPath (min S T) omega := by
  apply ContinuousMap.ext
  intro t
  simp only [stoppedPath_apply, min_assoc]

end ContinuousPath

end MarkovProcess



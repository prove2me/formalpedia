-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_Complex_F000
-- name    : StochLean_Probability_Process_Path_Complex_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:02:03.57886+00:00
-- url     : https://prove2.me/theorems/c707d1a0-36e0-4d29-bff6-09888ae2a41c
-- title:
--   StochLean: Probability.Process.Path.Complex F000

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Complex paths as pairs of the existing real coordinate processes

The source left limit is zero at time zero. At positive times it is
the actual strict-left complex limit whenever the path is cadlag.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

def complexProcess {T Ω : Type*} (X Y : T → Ω → ℝ) : T → Ω → ℂ := fun t ω ↦
  ⟨X t ω, Y t ω⟩
end ProbabilityTheory



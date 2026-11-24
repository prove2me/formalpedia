-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
-- name    : StochLean_Probability_Process_Path_LeftLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:14:27.169211+00:00
-- url     : https://prove2.me/theorems/04da9756-87f5-41ce-ba0d-7ab41644593a
-- title:
--   StochLean: Probability.Process.Path.LeftLimit F000

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source left limits and jumps

The Protter convention is `X_(0-) = 0`, not `X_0`. At positive times the
canonical Mathlib strict-left limit is reused; all mathematical limit identities
are proved on the cadlag domain. No limit property is asserted for an arbitrary
path on which a left limit does not exist.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def leftLimitProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t = 0 then 0 else Function.leftLim (fun s ↦ X s ω) t
noncomputable def jumpProcess (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  X - leftLimitProcess X
end ProbabilityTheory



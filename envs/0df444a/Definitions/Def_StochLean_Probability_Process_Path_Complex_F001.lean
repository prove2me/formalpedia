-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_Complex_F001
-- name    : StochLean_Probability_Process_Path_Complex_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:25.354692+00:00
-- url     : https://prove2.me/theorems/a4c9282d-59d3-4cb9-b7c5-460700b69bf7
-- title:
--   StochLean: Probability.Process.Path.Complex F001

import Definitions.Def_StochLean_Probability_Process_Path_Complex_F000
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23

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

noncomputable def complexLeftLimitProcess {Ω : Type*} (Z : ℝ≥0 → Ω → ℂ) : ℝ≥0 → Ω → ℂ :=
  complexProcess (leftLimitProcess (fun t ω ↦ (Z t ω).re))
    (leftLimitProcess (fun t ω ↦ (Z t ω).im))
end ProbabilityTheory



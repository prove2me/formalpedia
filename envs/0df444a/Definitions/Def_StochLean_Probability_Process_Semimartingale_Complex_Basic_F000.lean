-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_Complex_Basic_F000
-- name    : StochLean_Probability_Process_Semimartingale_Complex_Basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:30.217802+00:00
-- url     : https://prove2.me/theorems/b262c74a-27e7-4fa1-8389-f0acf9728aca
-- title:
--   StochLean: Probability.Process.Semimartingale.Complex.Basic F000

import Definitions.Def_StochLean_Probability_Process_Path_Complex_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Complex semimartingales are pairs of the existing real semimartingales

This is a coordinate predicate, not another good-integrator construction.
All stochastic integration and bracket owners remain the real ones.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {Z W : ℝ≥0 → Ω → ℂ}

def IsComplexSemimartingale (Z : ℝ≥0 → Ω → ℂ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  IsSemimartingale (fun t ω ↦ (Z t ω).re) F P ∧
    IsSemimartingale (fun t ω ↦ (Z t ω).im) F P
end ProbabilityTheory



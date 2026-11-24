-- Prove2me | Definitions.Def_StochLean_Probability_Process_ClassD_Basic_F000
-- name    : StochLean_Probability_Process_ClassD_Basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:21.746084+00:00
-- url     : https://prove2.me/theorems/3d3fa200-46f0-4114-9e60-ac797fdca605
-- title:
--   StochLean: Probability.Process.ClassD.Basic F000

import Definitions.Def_StochLean_Probability_Process_Equivalence_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Class D: uniform integrability of finite stopping values

The sole Class D predicate concerns the family of all everywhere-finite stopping
times, using the existing `FiniteStoppingTime` witness. Adaptation, cadlag paths,
one-sided martingality and initial normalization are separate hypotheses.
In particular this is not uniform integrability at deterministic times.
Source: Protter III.3, printed p.107 (PDF p.118).
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → E}

/-- Uniform integrability over all finite stopping times, not just constant ones. -/
def IsClassD (X : ℝ≥0 → Ω → E) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  UniformIntegrable (fun τ : FiniteStoppingTime F ↦ fun ω ↦ X (τ ω) ω) 1 P
namespace IsClassD

end IsClassD

end ProbabilityTheory



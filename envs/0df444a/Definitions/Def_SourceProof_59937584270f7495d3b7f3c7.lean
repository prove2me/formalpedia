-- Prove2me | Definitions.Def_SourceProof_59937584270f7495d3b7f3c7
-- name    : SourceProof_59937584270f7495d3b7f3c7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:30.856807+00:00
-- url     : https://prove2.me/theorems/6e0af592-6fea-4664-867c-6ad00c23b7dd
-- title:
--   StochLean source theorem: ProbabilityTheory.isClassD_const

import Definitions.Def_StochLean_Probability_Process_ClassD_Basic_F000

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

namespace IsClassD

end IsClassD

theorem _root_.Prove2MeSourceProof.h_59937584270f7495d3b7f3c7 {V : Ω → E} (hV : Integrable V P) :
    IsClassD (fun _ : ℝ≥0 ↦ V) F P :=
  uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.mpr hV)
end ProbabilityTheory



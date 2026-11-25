-- Prove2me | Definitions.Def_SourceProof_03e63d7ecbdfc90f21e5b93e
-- name    : SourceProof_03e63d7ecbdfc90f21e5b93e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:50:55.19909+00:00
-- url     : https://prove2.me/theorems/f93986b7-d5e3-4c17-ace7-f370e04e86b7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsClassD.uniformIntegrable

import Definitions.Def_StochLean_Probability_Process_ClassD_Basic_F000
import Definitions.Def_SourceProof_eb9d0979158009ea89ad5bf1

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

theorem _root_.Prove2MeSourceProof.h_03e63d7ecbdfc90f21e5b93e (hX : IsClassD X F P) : UniformIntegrable X 1 P :=
  (_root_.Prove2MeSourceProof.h_eb9d0979158009ea89ad5bf1 hX) (ProbabilityTheory.FiniteStoppingTime.const F)
end IsClassD

end ProbabilityTheory



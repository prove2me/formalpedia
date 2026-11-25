-- Prove2me | Definitions.Def_SourceProof_fc0f2624190866d48e0e4775
-- name    : SourceProof_fc0f2624190866d48e0e4775
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:40.274123+00:00
-- url     : https://prove2.me/theorems/4ac12240-f649-4475-b946-57d2939979d8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsClassD.integrable

import Definitions.Def_StochLean_Probability_Process_ClassD_Basic_F000
import Definitions.Def_SourceProof_fef49451f572bae1c04cedf5

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

theorem _root_.Prove2MeSourceProof.h_fc0f2624190866d48e0e4775 (hX : IsClassD X F P) (t : ℝ≥0) : Integrable (X t) P :=
  (_root_.Prove2MeSourceProof.h_fef49451f572bae1c04cedf5 hX) (ProbabilityTheory.FiniteStoppingTime.const F t)
end IsClassD

end ProbabilityTheory



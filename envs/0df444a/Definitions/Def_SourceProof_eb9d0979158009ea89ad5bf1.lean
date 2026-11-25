-- Prove2me | Definitions.Def_SourceProof_eb9d0979158009ea89ad5bf1
-- name    : SourceProof_eb9d0979158009ea89ad5bf1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:41:07.866213+00:00
-- url     : https://prove2.me/theorems/79300cea-8c93-57d1-aeb9-f7864a5acad0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsClassD.uniformIntegrable_finiteStoppingTime

import Definitions.Def_StochLean_Probability_Process_ClassD_Basic_F000
import Definitions.Def_SourceProof_5a705a1f4d32da63ab0f4ee7

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

theorem _root_.Prove2MeSourceProof.h_eb9d0979158009ea89ad5bf1 {ι : Type*} (hX : IsClassD X F P)
    (τ : ι → FiniteStoppingTime F) :
    UniformIntegrable (fun i ω ↦ X (τ i ω) ω) 1 P := (_root_.Prove2MeSourceProof.h_5a705a1f4d32da63ab0f4ee7 hX) τ
end IsClassD

end ProbabilityTheory



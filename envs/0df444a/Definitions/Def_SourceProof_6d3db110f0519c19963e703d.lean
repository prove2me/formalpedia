-- Prove2me | Definitions.Def_SourceProof_6d3db110f0519c19963e703d
-- name    : SourceProof_6d3db110f0519c19963e703d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:25:48.244798+00:00
-- url     : https://prove2.me/theorems/6dd011b3-acd8-5564-baf7-1313e90e0fec
-- title:
--   StochLean source theorem: StochLean.continuous_stieltjesContinuousPart

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesContinuousPart_F000
import Definitions.Def_SourceProof_7fe0c496f8e83f4eaf5b3755
import Definitions.Def_SourceProof_8c40de8f67b8fcdd3a3ee5e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous and jump parts of an increasing right-continuous path

Both parts start at zero and use the original Stieltjes measure. Continuity of
the diffuse part follows from the singleton/left-jump formula, including the
bottom endpoint. The original initial value remains a separate term.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_6d3db110f0519c19963e703d (f : StieltjesFunction ℝ≥0) :
    Continuous (stieltjesContinuousPart f) := by
  have : NullSingletonClass (StochLean.stieltjesContinuousPart f).measure := by
    rw [_root_.Prove2MeSourceProof.h_7fe0c496f8e83f4eaf5b3755]
    infer_instance
  exact _root_.Prove2MeSourceProof.h_8c40de8f67b8fcdd3a3ee5e5 _
end StochLean



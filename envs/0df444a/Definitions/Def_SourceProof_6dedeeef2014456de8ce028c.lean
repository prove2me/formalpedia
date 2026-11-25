-- Prove2me | Definitions.Def_SourceProof_6dedeeef2014456de8ce028c
-- name    : SourceProof_6dedeeef2014456de8ce028c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:00.435673+00:00
-- url     : https://prove2.me/theorems/72bc20aa-5a3a-5c25-a779-5efffed3c66d
-- title:
--   StochLean source theorem: StochLean.stieltjesContinuousPart_zero

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesContinuousPart_F000
import Definitions.Def_SourceProof_ad9b7b5a8cf2a241add9b558

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

@[simp] theorem _root_.Prove2MeSourceProof.h_6dedeeef2014456de8ce028c (f : StieltjesFunction ℝ≥0) :
    stieltjesContinuousPart f 0 = 0 := _root_.Prove2MeSourceProof.h_ad9b7b5a8cf2a241add9b558 _ _
end StochLean



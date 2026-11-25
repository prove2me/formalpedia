-- Prove2me | Definitions.Def_SourceProof_ef871b7f247732b34ba06d39
-- name    : SourceProof_ef871b7f247732b34ba06d39
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:17:38.543606+00:00
-- url     : https://prove2.me/theorems/f59707fd-0cb7-485b-9756-246032ea4d24
-- title:
--   StochLean source theorem: StochLean.stieltjesJumpPart_measure

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesContinuousPart_F000
import Definitions.Def_SourceProof_e6e3f4d2909fac9d9c334301

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

theorem _root_.Prove2MeSourceProof.h_ef871b7f247732b34ba06d39 (f : StieltjesFunction ℝ≥0) :
    (stieltjesJumpPart f).measure = pointAtomicPart f.measure :=
  _root_.Prove2MeSourceProof.h_e6e3f4d2909fac9d9c334301 _ _
end StochLean



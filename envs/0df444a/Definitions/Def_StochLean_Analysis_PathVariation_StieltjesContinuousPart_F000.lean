-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_StieltjesContinuousPart_F000
-- name    : StochLean_Analysis_PathVariation_StieltjesContinuousPart_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:45:49.19213+00:00
-- url     : https://prove2.me/theorems/d981500a-faeb-4965-9563-5eed53226f00
-- title:
--   StochLean: Analysis.PathVariation.StieltjesContinuousPart F000

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesSubmeasure_F000
import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F002
import Definitions.Def_SourceProof_49c549aa0a44f9f3d29251ef
import Definitions.Def_SourceProof_8b8684e748d5e31b03d0af2c

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

noncomputable def stieltjesContinuousPart (f : StieltjesFunction ℝ≥0) : StieltjesFunction ℝ≥0 :=
  stieltjesSubmeasure f (_root_.Prove2MeSourceProof.h_8b8684e748d5e31b03d0af2c f.measure)
noncomputable def stieltjesJumpPart (f : StieltjesFunction ℝ≥0) : StieltjesFunction ℝ≥0 :=
  stieltjesSubmeasure f (_root_.Prove2MeSourceProof.h_49c549aa0a44f9f3d29251ef f.measure)
end StochLean



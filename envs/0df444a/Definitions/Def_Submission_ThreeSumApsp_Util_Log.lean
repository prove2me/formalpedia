-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Util_Log
-- name    : Submission_ThreeSumApsp_Util_Log
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:50:43.668956+00:00
-- url     : https://prove2.me/theorems/1b760670-2a33-4162-a788-c4f4a83a4f6d
-- title:
--   Log
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit false
@[expose] public section
namespace Real
end Real
namespace ThreeSumApsp
noncomputable def logU (u : ℝ) : ℝ := Real.log (max u 2)
end ThreeSumApsp



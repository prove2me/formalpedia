-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
-- name    : Submission_ThreeSumApsp_Lang_RunsStayInLimits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:51.423548+00:00
-- url     : https://prove2.me/theorems/9ce08ba1-8171-4f02-b9ce-0987a406aa0f
-- title:
--   Runs Stay In Limits
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Mathlib.Tactic.SplitIfs
set_option autoImplicit false
public section
@[expose] section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
end Light



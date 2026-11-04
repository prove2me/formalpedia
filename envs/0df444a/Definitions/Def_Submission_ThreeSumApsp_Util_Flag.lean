-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Util_Flag
-- name    : Submission_ThreeSumApsp_Util_Flag
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:06.287522+00:00
-- url     : https://prove2.me/theorems/0c190b1e-5b3c-4242-b5ae-f4bb31fbcc08
-- title:
--   Flag
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Flag.lean

module
public import Mathlib.Algebra.Order.Ring.Int
set_option autoImplicit false
@[expose] public section
namespace ThreeSumApsp
open Classical in
/-- The answer of a decision problem as a number: 1 for yes, 0 for no. -/
noncomputable def flag (p : Prop) : ℤ := if p then 1 else 0
end ThreeSumApsp



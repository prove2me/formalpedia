-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
-- name    : Submission_ThreeSumApsp_Util_Ceil
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:52.581533+00:00
-- url     : https://prove2.me/theorems/924674bf-a28b-4ed2-a0e6-fc779c8fb44d
-- title:
--   Ceil
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean

module
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
set_option autoImplicit false
public section
@[expose] section
namespace Nat
end Nat
namespace Real
end Real
namespace ThreeSumApsp
@[expose] noncomputable def cbrtCeil (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊
end ThreeSumApsp



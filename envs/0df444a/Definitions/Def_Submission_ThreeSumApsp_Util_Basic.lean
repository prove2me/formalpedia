-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Util_Basic
-- name    : Submission_ThreeSumApsp_Util_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:23:52.837296+00:00
-- url     : https://prove2.me/theorems/f8c5988b-1889-4043-8104-11d43e436125
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Basic.lean

module
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit false



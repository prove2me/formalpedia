-- Prove2me | Definitions.Def_DeletionCode_ExceptionalCountArithmetic
-- name    : DeletionCode_ExceptionalCountArithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:04:40.552067+00:00
-- url     : https://prove2.me/theorems/15ff0a0c-305c-46a3-a840-8763db14d462
-- title:
--   Exceptional Count Arithmetic
-- statement:
--   Definitions and structural lemmas for Exceptional Count Arithmetic, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalCountArithmetic.lean

import Definitions.Def_DeletionCode_FinitePairUnion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.ExceptionalCountArithmetic
open scoped BigOperators
def exceptionalConstant (t : ℕ) : ℕ :=
  (t + 8 * (2 * t) * (2 * t + 2)) * 4 ^ (2 * t)
end DeletionCode.ExceptionalCountArithmetic



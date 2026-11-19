-- Prove2me | Definitions.Def_DeletionCode_TwoEditWindows
-- name    : DeletionCode_TwoEditWindows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:03:07.052593+00:00
-- url     : https://prove2.me/theorems/93d479f4-7a37-4b6c-bea4-4e7c72ad2a1f
-- title:
--   Two Edit Windows
-- statement:
--   Definitions and structural lemmas for Two Edit Windows, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TwoEditWindows.lean

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.TwoEditWindows
def Avoids (k start edit : ℕ) : Prop := start + k ≤ edit ∨ edit < start
end DeletionCode.TwoEditWindows



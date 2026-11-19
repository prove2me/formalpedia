-- Prove2me | Definitions.Def_DeletionCode_UniqueWordParameters
-- name    : DeletionCode_UniqueWordParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:03:59.370213+00:00
-- url     : https://prove2.me/theorems/20b64134-57a6-4e30-9d5a-575d428bf653
-- title:
--   Unique Word Parameters
-- statement:
--   Definitions and structural lemmas for Unique Word Parameters, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.UniqueWordParameters
def uniquenessLength (n : ℕ) : ℕ := 2 * Nat.clog 2 n + 2
end DeletionCode.UniqueWordParameters



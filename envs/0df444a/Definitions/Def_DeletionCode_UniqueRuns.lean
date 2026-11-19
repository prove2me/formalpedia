-- Prove2me | Definitions.Def_DeletionCode_UniqueRuns
-- name    : DeletionCode_UniqueRuns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:20:07.111503+00:00
-- url     : https://prove2.me/theorems/9118c49e-6dd6-44d3-b82b-bc2c571eb264
-- title:
--   Unique Runs
-- statement:
--   Definitions and structural lemmas for Unique Runs, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueRuns.lean

import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
namespace DeletionCode.UniqueRuns
open Windows
def ConstantOn (x : Letters) (start len : ℕ) (bit : Bool) : Prop :=
  ∀ i, i < len → x (start + i) = bit
end DeletionCode.UniqueRuns



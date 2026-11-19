-- Prove2me | Definitions.Def_DeletionCode_DescriptionCount
-- name    : DeletionCode_DescriptionCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:00:50.868492+00:00
-- url     : https://prove2.me/theorems/a9fa848b-0afd-4ead-85ec-a8b4df697cde
-- title:
--   Description Count
-- statement:
--   Definitions and structural lemmas for Description Count, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DescriptionCount.lean

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.DescriptionCount
def fieldBound (L ν : ℕ) : ℕ := 16 * L * (ν + 1)
abbrev Description (n L ν c : ℕ) :=
  (Fin c → Fin n) × (Fin ν → Fin (4 * L)) × (Fin c → Fin ν) ×
  (Fin (4 * ν) → (Fin 12 → Fin (fieldBound L ν)))
end DeletionCode.DescriptionCount



-- Prove2me | Definitions.Def_DeletionCode_PaperParameters
-- name    : DeletionCode_PaperParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:29:49.86921+00:00
-- url     : https://prove2.me/theorems/1f930047-ffca-495f-af8a-c445032e0ee1
-- title:
--   Paper Parameters
-- statement:
--   Definitions and structural lemmas for Paper Parameters, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
set_option autoImplicit true
namespace DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
def k (n : ℕ) : ℕ := UniqueWordParameters.uniquenessLength n
def L (n : ℕ) : ℕ := HeaderRecovery.windowLength (k n)
end DeletionCode.PaperParameters



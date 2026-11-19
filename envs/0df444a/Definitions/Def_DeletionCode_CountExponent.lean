-- Prove2me | Definitions.Def_DeletionCode_CountExponent
-- name    : DeletionCode_CountExponent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:10:14.024808+00:00
-- url     : https://prove2.me/theorems/67f0612c-2c0e-4c49-8e6d-513d3c937831
-- title:
--   Count Exponent
-- statement:
--   Definitions and structural lemmas for Count Exponent, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountExponent.lean

import Definitions.Def_DeletionCode_DescriptionCount
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
namespace DeletionCode.CountExponent
open DescriptionCount HeaderRecovery
def exponent (t : ℕ) : ℕ := 100 * t * (16 * (2 * t + 1) + 1)
end DeletionCode.CountExponent



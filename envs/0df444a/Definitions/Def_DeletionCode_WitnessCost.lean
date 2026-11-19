-- Prove2me | Definitions.Def_DeletionCode_WitnessCost
-- name    : DeletionCode_WitnessCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:28:38.398804+00:00
-- url     : https://prove2.me/theorems/dbd0bc86-f0de-4e02-980b-8ba28f3b3a91
-- title:
--   Witness Cost
-- statement:
--   Definitions and structural lemmas for Witness Cost, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCost.lean

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
namespace DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters
def exponent (t : ℕ) : ℕ := 4 * CountExponent.exponent t + 2
end DeletionCode.WitnessCost



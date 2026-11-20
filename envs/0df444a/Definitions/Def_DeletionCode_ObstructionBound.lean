-- Prove2me | Definitions.Def_DeletionCode_ObstructionBound
-- name    : DeletionCode_ObstructionBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:01:02.064647+00:00
-- url     : https://prove2.me/theorems/10f353db-5a38-41e8-9dba-8dda973ee86c
-- title:
--   Obstruction Bound
-- statement:
--   Definitions and structural lemmas for Obstruction Bound, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean

import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_WitnessCost
set_option autoImplicit true
namespace DeletionCode.ObstructionBound
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount
open CircleUniform WitnessCounting ObstructionProbability
open scoped BigOperators ENNReal
def scale (t n k : ℕ) : ℕ := n ^ (2 * t - 1) * (windowLength k) ^ (WitnessCost.exponent t)
end DeletionCode.ObstructionBound



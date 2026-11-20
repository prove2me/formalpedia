-- Prove2me | Definitions.Def_DeletionCode_WordGraphWitness
-- name    : DeletionCode_WordGraphWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:32:21.811145+00:00
-- url     : https://prove2.me/theorems/d1800be4-3fd3-402c-b64f-95943e40cbae
-- title:
--   Word Graph Witness
-- statement:
--   Definitions and structural lemmas for Word Graph Witness, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordGraphWitness.lean

import Definitions.Def_DeletionCode_OddGraphWalk
import Definitions.Def_DeletionCode_BoundedWitnessWalk
set_option autoImplicit true
namespace DeletionCode.WordGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks WitnessCases
end DeletionCode.WordGraphWitness



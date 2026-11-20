-- Prove2me | Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
-- name    : DeletionCode_VerifiedConflictGraphWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:58:28.3216+00:00
-- url     : https://prove2.me/theorems/e1489275-230f-4626-b4c5-b1a8a50c20f1
-- title:
--   Verified Conflict Graph Witness
-- statement:
--   Definitions and structural lemmas for Verified Conflict Graph Witness, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/VerifiedConflictGraphWitness.lean

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
set_option autoImplicit true
namespace DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases
end DeletionCode.VerifiedConflictGraphWitness



-- Prove2me | Definitions.Def_DeletionCode_BoundedWitnessWalk
-- name    : DeletionCode_BoundedWitnessWalk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:29:20.965579+00:00
-- url     : https://prove2.me/theorems/146fd908-1017-4bab-b31c-e306189b1d7d
-- title:
--   Bounded Witness Walk
-- statement:
--   Definitions and structural lemmas for Bounded Witness Walk, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BoundedWitnessWalk.lean

import Definitions.Def_DeletionCode_WitnessCases
import Definitions.Def_DeletionCode_FiniteWalkRules
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
namespace DeletionCode.BoundedWitnessWalk
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open CatalogueAlgebra FiniteWalkRules WalkSelection BlockPartition WitnessCases
end DeletionCode.BoundedWitnessWalk



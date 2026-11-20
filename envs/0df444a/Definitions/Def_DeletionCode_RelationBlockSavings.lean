-- Prove2me | Definitions.Def_DeletionCode_RelationBlockSavings
-- name    : DeletionCode_RelationBlockSavings
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:23:04.285685+00:00
-- url     : https://prove2.me/theorems/7f7f9b1a-8ada-45b0-92e0-cf36982ea15d
-- title:
--   Relation Block Savings
-- statement:
--   Definitions and structural lemmas for Relation Block Savings, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
set_option autoImplicit true
namespace DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
noncomputable def blockHull {k : ℕ} (G I : RuleSet k) : RuleSet k := by
  classical
  exact G.filter (fun u => ∃ i ∈ I,
    Relation.EqvGen (FiniteConnectedGrowth.Induced G RuleAdjacent) i u)
end DeletionCode.RelationBlockSavings



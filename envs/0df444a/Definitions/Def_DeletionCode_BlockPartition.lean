-- Prove2me | Definitions.Def_DeletionCode_BlockPartition
-- name    : DeletionCode_BlockPartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:19:20.77296+00:00
-- url     : https://prove2.me/theorems/eb042f41-63bf-447c-9b05-e17921818274
-- title:
--   Block Partition
-- statement:
--   Definitions and structural lemmas for Block Partition, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
set_option autoImplicit true
namespace DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
def ConnectedIn {k : ℕ} (U : RuleSet k)
    (a b : Gram (windowLength k) → ℤ) : Prop :=
  Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) a b
noncomputable def blockOf {k : ℕ} (U : RuleSet k)
    (a : Gram (windowLength k) → ℤ) : RuleSet k := by
  classical
  exact U.filter (fun b => ConnectedIn U a b)
noncomputable def blocks {k : ℕ} (U : RuleSet k) : Finset (RuleSet k) := by
  classical
  exact U.image (blockOf U)
noncomputable def attachedBlocks {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) : Finset (RuleSet k) := by
  classical
  exact (blocks U).filter (fun B => ∃ v, Incident B v ∧ Incident {w} v)
end DeletionCode.BlockPartition



-- Prove2me | Definitions.Def_DeletionCode_FiniteGenerating
-- name    : DeletionCode_FiniteGenerating
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:23:38.589868+00:00
-- url     : https://prove2.me/theorems/56caa7af-7dda-4a63-8d7d-4d149a155e1c
-- title:
--   Finite Generating
-- statement:
--   Definitions and structural lemmas for Finite Generating, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
set_option autoImplicit true
namespace DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition
def GeneratingOn {k : ℕ} (v : Gram (windowLength k) → ℤ) (G : RuleSet k)
    (rank : (Gram (windowLength k) → ℤ) → ℕ) : Prop :=
  ∀ u ∈ G, ∀ g, u g = -1 → v g ≠ 0 ∨ ∃ z ∈ G, rank z < rank u ∧ z g ≠ 0
def Independent {k : ℕ} (G : RuleSet k) : Prop :=
  LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ))
structure GeneratingAt {k : ℕ} (v : Gram (windowLength k) → ℤ) (G : RuleSet k) : Prop where
  independent : Independent G
  ordered : ∃ rank : (Gram (windowLength k) → ℤ) → ℕ,
    Set.InjOn rank (↑G : Set _) ∧ GeneratingOn v G rank
def ClosedIn {k : ℕ} (G U : RuleSet k) : Prop :=
  ∀ a ∈ U, ∀ b ∈ G, ConnectedIn G a b → b ∈ U
end DeletionCode.FiniteGenerating



-- Prove2me | Definitions.Def_DeletionCode_GeneratingBlocks
-- name    : DeletionCode_GeneratingBlocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:07:39.54818+00:00
-- url     : https://prove2.me/theorems/7f815eb3-cdc5-4b13-b3a4-9e70df0f0f35
-- title:
--   Generating Blocks
-- statement:
--   Definitions and structural lemmas for Generating Blocks, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean

import Definitions.Def_DeletionCode_RuleSetGraph
set_option autoImplicit true
namespace DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
def Generating {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) : Prop :=
  ∀ i g, G i g = -1 → v g ≠ 0 ∨ ∃ j, rank j < rank i ∧ G j g ≠ 0
def Adjacent {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (i j : I) : Prop :=
  ∃ u, Incident {G i} u ∧ Incident {G j} u
def Connected {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) : I → I → Prop :=
  Relation.EqvGen (Adjacent G)
def BlockClosed {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (S : Set I) : Prop :=
  ∀ i ∈ S, ∀ j, Connected G i j → j ∈ S
def blockHull {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (T : Set I) : Set I :=
  {j | ∃ i ∈ T, Connected G i j}
end DeletionCode.GeneratingBlocks



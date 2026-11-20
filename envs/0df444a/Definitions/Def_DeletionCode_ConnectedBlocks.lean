-- Prove2me | Definitions.Def_DeletionCode_ConnectedBlocks
-- name    : DeletionCode_ConnectedBlocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:18:18.909437+00:00
-- url     : https://prove2.me/theorems/5deb5e6e-893e-4a97-a876-232cdb4010e9
-- title:
--   Connected Blocks
-- statement:
--   Definitions and structural lemmas for Connected Blocks, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConnectedBlocks.lean

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
set_option autoImplicit true
namespace DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph
def RuleAdjacent {L : ℕ} (w u : Gram L → ℤ) : Prop :=
  ∃ v, Incident {w} v ∧ Incident {u} v
def CatalogueRule (t k : ℕ) (w : Gram (windowLength k) → ℤ) : Prop :=
  ∃ words : Fin (2 * t) → BubbleWord k,
    ValidCatalogue words (fun _ => (0 : Fin 1)) ∧
    OrientationBalanced t words (fun _ => (0 : Fin 1)) ∧
    ruleSpectrum (indexedFamily words (fun _ => (0 : Fin 1))).family
      (windowLength k) Finset.univ = w
def Connected {k : ℕ} (B : RuleSet k) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B,
    Relation.EqvGen (FiniteConnectedGrowth.Induced B RuleAdjacent) a b
end DeletionCode.ConnectedBlocks



-- Prove2me | Definitions.Def_DeletionCode_CatalogueVertexBound
-- name    : DeletionCode_CatalogueVertexBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:19:39.781731+00:00
-- url     : https://prove2.me/theorems/136db0b1-25f6-4dce-94aa-2ac4fc21fc04
-- title:
--   Catalogue Vertex Bound
-- statement:
--   Definitions and structural lemmas for Catalogue Vertex Bound, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueVertexBound.lean

import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
set_option autoImplicit true
namespace DeletionCode.CatalogueVertexBound
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport RuleReconstruction RuleSetGraph SupportComponents ConnectedBlocks
open scoped BigOperators
abbrev VertexNames {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :=
  Σ b : Fin (2 * t),
    Fin (E.family.extra b false + 2) ⊕ Fin (E.family.extra b true + 1)
def namedVertex {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :
    VertexNames E → SupportedVertex E.family (windowLength k)
  | ⟨b, Sum.inl i⟩ => ⟨vertex E.family (windowLength k) b false i.val,
      b, false, i.val, by have := i.isLt; omega, rfl⟩
  | ⟨b, Sum.inr i⟩ => ⟨vertex E.family (windowLength k) b true (i.val + 1),
      b, true, i.val + 1, by have := i.isLt; omega, rfl⟩
end DeletionCode.CatalogueVertexBound



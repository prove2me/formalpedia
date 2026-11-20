-- Prove2me | Definitions.Def_DeletionCode_CatalogueAlgebra
-- name    : DeletionCode_CatalogueAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:23:05.80369+00:00
-- url     : https://prove2.me/theorems/f17728ec-867d-4e5c-bbf4-f4bfe1aa9a7c
-- title:
--   Catalogue Algebra
-- statement:
--   Definitions and structural lemmas for Catalogue Algebra, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
set_option autoImplicit true
namespace DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators
def rational {L : ℕ} (u : Gram L → ℤ) : Gram L → ℚ := fun g => (u g : ℚ)
end DeletionCode.CatalogueAlgebra



-- Prove2me | Definitions.Def_DeletionCode_RelationSavings
-- name    : DeletionCode_RelationSavings
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:22:17.100227+00:00
-- url     : https://prove2.me/theorems/505cd963-78dd-453b-8b7b-0041dc8f5b63
-- title:
--   Relation Savings
-- statement:
--   Definitions and structural lemmas for Relation Savings, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSavings.lean

import Definitions.Def_DeletionCode_CatalogueFamily
import Definitions.Def_DeletionCode_ComponentFibers
import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_SupportInclusion
import Theorems.Thm_DeletionCode_RelationSupport_support_inclusion

set_option autoImplicit true
namespace DeletionCode.RelationSavings
open HeaderRecovery SignedSupport RuleReconstruction RuleSetGraph SupportComponents
open SignedRuleCount ConnectedBlocks CatalogueFamily ComponentFibers SupportInclusion
open scoped BigOperators
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}
theorem relation_support_included (w : Gram (windowLength k) → ℤ) (a : Fin R → ℚ)
    (hrel : RelationSupport.Relation G w a) :
    CoordinateSupportIncluded {w} (Finset.univ.image G) := by
  classical
  intro g hg
  obtain ⟨u, hu, hug⟩ := hg
  have huw : u = w := Finset.mem_singleton.mp hu
  subst u
  obtain ⟨r, hr⟩ := RelationSupport.support_inclusion G w a hrel g hug
  exact ⟨G r, Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩, hr⟩
end DeletionCode.RelationSavings



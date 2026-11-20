-- Prove2me | Definitions.Def_DeletionCode_WitnessCases
-- name    : DeletionCode_WitnessCases
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:24:32.495518+00:00
-- url     : https://prove2.me/theorems/9c0453f5-f6d1-41ad-b61d-494041069dcb
-- title:
--   Witness Cases
-- statement:
--   Definitions and structural lemmas for Witness Cases, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Definitions.Def_DeletionCode_SupportBlockCount
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_LargeBlockSelection
set_option autoImplicit true
namespace DeletionCode.WitnessCases
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition FiniteGenerating FiniteRelationBlocks CatalogueAlgebra
open scoped BigOperators
structure WitnessBounds (t k : ℕ) (U : RuleSet k) : Prop where
  size_lower : 2 ≤ U.card
  size_upper : U.card ≤ 1 + 4 * t * (windowLength k) ^ 2
  components : componentCount U ≤ (2 * t - 1) * U.card + 1
  small_components : U.card ≤ windowLength k → componentCount U ≤ (2 * t - 1) * U.card
structure Witness (t k : ℕ) (v : Gram (windowLength k) → ℤ)
    (K : Set (Gram (windowLength k) → ℤ)) (U : RuleSet k) : Prop where
  generating : GeneratingAt v U
  catalogue : ∀ u ∈ U, CatalogueRule t k u
  surviving : ∀ u ∈ U, u ∈ K
  bounds : WitnessBounds t k U
end DeletionCode.WitnessCases



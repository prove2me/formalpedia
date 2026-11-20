-- Prove2me | Definitions.Def_DeletionCode_ManuscriptCounting
-- name    : DeletionCode_ManuscriptCounting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:21:17.664467+00:00
-- url     : https://prove2.me/theorems/966ba67b-d60c-47fa-8b49-ec0cb4c06357
-- title:
--   Manuscript Counting
-- statement:
--   Definitions and structural lemmas for Manuscript Counting, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ManuscriptCounting.lean

import Definitions.Def_DeletionCode_CountingLemma
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_CanonicalIndex
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_rank_disjoint

set_option autoImplicit true
namespace DeletionCode.ManuscriptCounting
open Windows HeaderRecovery CatalogueWords CatalogueBridge SignedSupport
open RuleReconstruction RuleSetGraph SignedRuleCount CountExponent CanonicalIndex
def GeneratingSet (t : ℕ) (x : Letters) (n k R c : ℕ) (Q : RuleSet k) : Prop :=
  Q.card = R ∧ componentCount Q = c ∧
    ∃ words : Fin R → Fin (2 * t) → BubbleWord k,
      ValidCatalogue (flatten t R words) (group t R) ∧
      OrientationBalanced t (flatten t R words) (group t R) ∧
      SignedGenerating (flatFamily t R words).family x n (windowLength k) ∧
      rulesOfFamily (flatFamily t R words) (group t R) = Q
theorem generatingSet_included (t : ℕ) (x : Letters) (n k R c : ℕ)
    (Q : RuleSet k) (hQ : GeneratingSet t x n k R c Q) :
    CountingLemma.GeneratingSet x n k (2 * t * R) R c (group t R) Q := by
  obtain ⟨hcard, hc, words, hvalid, _, hgen, hrules⟩ := hQ
  exact ⟨hcard, hc, flatFamily t R words, fun _ => rfl,
    hvalid.geometry, hvalid.rank_disjoint, hgen, hrules⟩
def inclusion (t : ℕ) (x : Letters) (n k R c : ℕ) :
    {Q : RuleSet k // GeneratingSet t x n k R c Q} →
      {Q : RuleSet k // CountingLemma.GeneratingSet x n k (2 * t * R) R c (group t R) Q} :=
  fun Q => ⟨Q.val, generatingSet_included t x n k R c Q.val Q.property⟩
end DeletionCode.ManuscriptCounting



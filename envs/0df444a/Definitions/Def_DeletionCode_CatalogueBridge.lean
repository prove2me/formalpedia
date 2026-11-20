-- Prove2me | Definitions.Def_DeletionCode_CatalogueBridge
-- name    : DeletionCode_CatalogueBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:17:15.599496+00:00
-- url     : https://prove2.me/theorems/c817c41a-c062-4d99-8a0f-6e7d2743683d
-- title:
--   Catalogue Bridge
-- statement:
--   Definitions and structural lemmas for Catalogue Bridge, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
set_option autoImplicit true
namespace DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount
def indexedFamily {k ν R : ℕ} (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R) :
    EditedFamily (Fin ν) k := editedFamily bubbles (fun b => (group b).val)
structure ValidCatalogue {k ν R : ℕ}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R) : Prop where
  boundary : ∀ b, (bubbles b).left.getLast? = some (!(bubbles b).bit) ∧
    (bubbles b).right.head? = some (!(bubbles b).bit)
  simple : ∀ b side, Function.Injective
    (fun i : Fin ((indexedFamily bubbles group).family.extra b side + 2) =>
      SupportComponents.vertex (indexedFamily bubbles group).family (windowLength k) b side i.val)
  endpoints : ∀ b i j,
    i ≤ (indexedFamily bubbles group).family.extra b false + 1 →
    j ≤ (indexedFamily bubbles group).family.extra b true + 1 →
    SupportComponents.vertex (indexedFamily bubbles group).family (windowLength k) b false i =
      SupportComponents.vertex (indexedFamily bubbles group).family (windowLength k) b true j →
    (i = 0 ∧ j = 0) ∨
      (i = (indexedFamily bubbles group).family.extra b false + 1 ∧
        j = (indexedFamily bubbles group).family.extra b true + 1)
  within_rule_disjoint : ∀ r : Fin R,
    VertexDisjointOn (indexedFamily bubbles group).family (windowLength k)
      (Finset.univ.filter (fun b => group b = r))
def OrientationBalanced {k ν R : ℕ} (t : ℕ)
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R) : Prop :=
  ∀ r : Fin R,
    (Finset.univ.filter (fun b => group b = r ∧ (bubbles b).orientation = .deletion)).card = t ∧
    (Finset.univ.filter (fun b => group b = r ∧ (bubbles b).orientation = .insertion)).card = t
def CatalogueGeneratingSet (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (Q : RuleSet k) : Prop :=
  ∃ bubbles : Fin ν → BubbleWord k,
    ValidCatalogue bubbles group ∧ OrientationBalanced t bubbles group ∧
    SignedGenerating (indexedFamily bubbles group).family x n (windowLength k) ∧
    Fintype.card
      (SupportComponents.GraphComponents (indexedFamily bubbles group).family (windowLength k)) = c ∧
    rulesOfFamily (indexedFamily bubbles group) group = Q ∧ Q.card = R
end DeletionCode.CatalogueBridge



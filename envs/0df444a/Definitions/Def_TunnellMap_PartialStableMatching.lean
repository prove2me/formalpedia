-- Prove2me | Definitions.Def_TunnellMap_PartialStableMatching
-- name    : TunnellMap_PartialStableMatching
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:25:20.696797+00:00
-- url     : https://prove2.me/theorems/51cccc51-f979-42bf-a703-921809be5d4c
-- title:
--   Partial Stable Matching
-- statement:
--   Definitions and structural lemmas for Partial Stable Matching, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PartialStableMatching.lean

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right


set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*}
def PartialBlocks [LT K] (I : GloballyRanked K S T) (M : PartialEquiv S T)
    (s : S) (t : T) : Prop :=
  (s ∉ M.source ∨ I.rank s t < I.rank s (M s)) ∧
    (t ∉ M.target ∨ I.rank s t < I.rank (M.symm t) t)
def PartialStable [LT K] (I : GloballyRanked K S T)
    (M : PartialEquiv S T) : Prop :=
  ∀ s t, ¬ I.PartialBlocks M s t
def partialEquivToEquiv (M : PartialEquiv S T)
    (hsource : M.source = Set.univ) (htarget : M.target = Set.univ) : S ≃ T where
  toFun := M
  invFun := M.symm
  left_inv s := M.left_inv (by rw [hsource]; trivial)
  right_inv t := M.right_inv (by rw [htarget]; trivial)
theorem partialStable_isPerfect [LT K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T)
    (M : PartialEquiv S T) (hM : I.PartialStable M) :
    M.source = Set.univ ∧ M.target = Set.univ := by
  classical
  have hsource : M.source = Set.univ := by
    by_contra hne
    have hs_exists : ∃ s : S, s ∉ M.source := by
      simpa [Set.eq_univ_iff_forall] using hne
    obtain ⟨s, hs⟩ := hs_exists
    have hsource_lt : Fintype.card M.source < Fintype.card S :=
      Fintype.card_subtype_lt hs
    have hmatched_card : Fintype.card M.source = Fintype.card M.target :=
      Fintype.card_congr M.toEquiv
    have htarget_lt : Fintype.card M.target < Fintype.card T := by
      omega
    have htarget_ne : M.target ≠ Set.univ := by
      intro htarget
      have htarget_card : Fintype.card M.target = Fintype.card T :=
        (set_fintype_card_eq_univ_iff M.target).2 htarget
      omega
    have ht_exists : ∃ t : T, t ∉ M.target := by
      simpa [Set.eq_univ_iff_forall] using htarget_ne
    obtain ⟨t, ht⟩ := ht_exists
    exact hM s t ⟨Or.inl hs, Or.inl ht⟩
  have hmatched_card : Fintype.card M.source = Fintype.card M.target :=
    Fintype.card_congr M.toEquiv
  have hsource_card : Fintype.card M.source = Fintype.card S :=
    (set_fintype_card_eq_univ_iff M.source).2 hsource
  have htarget_card : Fintype.card M.target = Fintype.card T := by
    omega
  exact ⟨hsource, (set_fintype_card_eq_univ_iff M.target).1 htarget_card⟩
end GloballyRanked
end TunnellMap



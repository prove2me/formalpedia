-- Prove2me | Definitions.Def_TunnellMap_MatchedOrder
-- name    : TunnellMap_MatchedOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:53:55.353458+00:00
-- url     : https://prove2.me/theorems/9a862f95-3650-435e-ab4b-9ae7549f798b
-- title:
--   Matched Order
-- statement:
--   Definitions and structural lemmas for Matched Order, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MatchedOrder.lean

import Definitions.Def_TunnellMap_ParkingTotal
import Mathlib.Data.List.NodupEquivFin
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right


set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
noncomputable def matchedSourceList (I : GloballyRanked K S T) (M : S ≃ T) : List S := by
  classical
  exact (Finset.univ : Finset S).toList.mergeSort fun s₁ s₂ =>
    I.rank s₁ (M s₁) ≤ I.rank s₂ (M s₂)
theorem matchedSourceList_nodup (I : GloballyRanked K S T) (M : S ≃ T) :
    (I.matchedSourceList M).Nodup := by
  classical
  unfold matchedSourceList
  exact (Finset.univ : Finset S).nodup_toList.mergeSort
@[simp] theorem mem_matchedSourceList (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : s ∈ I.matchedSourceList M := by
  classical
  simp [matchedSourceList]
@[simp] theorem length_matchedSourceList (I : GloballyRanked K S T) (M : S ≃ T) :
    (I.matchedSourceList M).length = Fintype.card S := by
  classical
  simp [matchedSourceList]
noncomputable def matchedKeyOrderEquiv (I : GloballyRanked K S T) (M : S ≃ T) :
    Fin (Fintype.card S) ≃ S := by
  classical
  let l := I.matchedSourceList M
  let cast : Fin (Fintype.card S) ≃ Fin l.length :=
    finCongr (I.length_matchedSourceList M).symm
  let get : Fin l.length ≃ S :=
    (I.matchedSourceList_nodup M).getEquivOfForallMemList l
      (I.mem_matchedSourceList M)
  exact cast.trans get
end GloballyRanked
end TunnellMap



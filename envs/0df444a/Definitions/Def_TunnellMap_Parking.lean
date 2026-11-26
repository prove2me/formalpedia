-- Prove2me | Definitions.Def_TunnellMap_Parking
-- name    : TunnellMap_Parking
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:45:52.277743+00:00
-- url     : https://prove2.me/theorems/a5f4b5d9-17f6-4458-88b6-d80f0c6c8388
-- title:
--   Parking
-- statement:
--   Definitions and structural lemmas for Parking, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Parking.lean

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right


set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
def preferredTargets (I : GloballyRanked K S T) (M : S ≃ T) (s : S) : Finset T :=
  Finset.univ.filter fun t => I.rank s t < I.rank s (M s)
def earlierMatchedSources (I : GloballyRanked K S T) (M : S ≃ T) (s : S) :
    Finset S :=
  Finset.univ.filter fun s' => I.rank s' (M s') < I.rank s (M s)
def proposalCount (I : GloballyRanked K S T) (M : S ≃ T) (s : S) : ℕ :=
  (I.preferredTargets M s).card + 1
omit [Fintype S] [DecidableEq S] [DecidableEq T] in
theorem preferred_target_has_earlier_match (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) (t : T)
    (ht : t ∈ I.preferredTargets M s) :
    I.rank (M.symm t) t < I.rank s (M s) := by
  have hpreferred : I.rank s t < I.rank s (M s) := by
    simpa [preferredTargets] using (Finset.mem_filter.mp ht).2
  have hmatched_le : I.rank (M.symm t) t ≤ I.rank s t := by
    apply le_of_not_gt
    intro hedge_lt
    exact hM s t ⟨hpreferred, hedge_lt⟩
  exact lt_of_le_of_lt hmatched_le hpreferred
noncomputable def preferredToEarlier (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) :
    {t // t ∈ I.preferredTargets M s} → {s' // s' ∈ I.earlierMatchedSources M s} :=
  fun t => ⟨M.symm t.1, by
    simp only [earlierMatchedSources, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using I.preferred_target_has_earlier_match M hM s t.1 t.2⟩
def MatchedKeyOrder (I : GloballyRanked K S T) (M : S ≃ T)
    (order : Fin (Fintype.card S) ≃ S) : Prop :=
  ∀ i j,
    I.rank (order i) (M (order i)) < I.rank (order j) (M (order j)) → i < j
end GloballyRanked
end TunnellMap



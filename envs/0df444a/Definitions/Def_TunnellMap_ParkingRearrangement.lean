-- Prove2me | Definitions.Def_TunnellMap_ParkingRearrangement
-- name    : TunnellMap_ParkingRearrangement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:26:48.091797+00:00
-- url     : https://prove2.me/theorems/c12caba4-9b2c-435e-97bd-f244ffb9e3e0
-- title:
--   Parking Rearrangement
-- statement:
--   Definitions and structural lemmas for Parking Rearrangement, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingRearrangement.lean

import Definitions.Def_TunnellMap_MatchedOrder
set_option autoImplicit true
namespace TunnellMap
def sortedCounts (a : List ℕ) : List ℕ :=
  a.mergeSort (· ≤ ·)
def IsParkingFunction (a : List ℕ) : Prop :=
  (∀ x ∈ a, 0 < x) ∧
    ∀ i : Fin (sortedCounts a).length,
      (sortedCounts a).get i ≤ i.1 + 1
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
noncomputable def matchedProposalCounts (I : GloballyRanked K S T)
    (M : S ≃ T) : List ℕ :=
  List.ofFn fun i : Fin (Fintype.card S) =>
    I.proposalCount M (I.matchedKeyOrderEquiv M i)
end GloballyRanked
end TunnellMap



-- Prove2me | Definitions.Def_TunnellMap_PreferenceList
-- name    : TunnellMap_PreferenceList
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:43:19.663158+00:00
-- url     : https://prove2.me/theorems/abde2f0d-06bb-4f8f-a39a-fdea5e9bb329
-- title:
--   Preference List
-- statement:
--   Definitions and structural lemmas for Preference List, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean

import Definitions.Def_TunnellMap_GloballyRanked
set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]
noncomputable def preferenceList (I : GloballyRanked K S T) (s : S) : List T :=
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  (Finset.univ : Finset T).sort (· ≤ ·)
end GloballyRanked
end TunnellMap



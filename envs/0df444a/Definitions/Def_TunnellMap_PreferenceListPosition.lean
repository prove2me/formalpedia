-- Prove2me | Definitions.Def_TunnellMap_PreferenceListPosition
-- name    : TunnellMap_PreferenceListPosition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:50:32.82399+00:00
-- url     : https://prove2.me/theorems/7a197518-b209-4e8d-ac60-e8fa5248069e
-- title:
--   Preference List Position
-- statement:
--   Definitions and structural lemmas for Preference List Position, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList


set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
noncomputable def preferenceIndex (I : GloballyRanked K S T)
    (s : S) (t : T) : Fin (I.preferenceList s).length :=
  Classical.choose (List.get_of_mem (I.mem_preferenceList s t))
end GloballyRanked
end TunnellMap



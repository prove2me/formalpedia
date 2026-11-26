-- Prove2me | Definitions.Def_TunnellMap_ParkingTotal
-- name    : TunnellMap_ParkingTotal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:51:57.736609+00:00
-- url     : https://prove2.me/theorems/a96843d0-5448-52e9-a4ea-ec493eb83839
-- title:
--   Parking Total
-- statement:
--   Definitions and structural lemmas for Parking Total, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingTotal.lean

import Definitions.Def_TunnellMap_Parking
set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
end GloballyRanked
end TunnellMap



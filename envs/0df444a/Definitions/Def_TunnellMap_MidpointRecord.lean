-- Prove2me | Definitions.Def_TunnellMap_MidpointRecord
-- name    : TunnellMap_MidpointRecord
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:45:45.6406+00:00
-- url     : https://prove2.me/theorems/10923613-ac98-58af-b42d-c8127179a3c4
-- title:
--   Midpoint Record
-- statement:
--   Definitions and structural lemmas for Midpoint Record, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointRecord.lean

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_MidpointBound
set_option autoImplicit true
namespace TunnellMap
structure PreferredMidpointRecord {n : ℤ} (s : BResidual n) (t : AResidual n) where
  target : AResidual n
  target_eq : target = preferredTarget s t
  half : Triple
  half_odd : Odd half.z
  half_sum : IsHalfSum half (residualSourceLift s) (residualTargetLift target)
  direction : Triple
  multiplier : ℤ
  direction_eq : direction = primitiveDirection (preferredVector s t)
  half_decomposition : half = vsmul multiplier direction
  multiplier_odd : Odd multiplier
  direction_third_odd : Odd direction.z
  direction_oriented : FirstNonzeroPositive direction
  bilinear : qBilinear (residualSourceLift s) direction =
    multiplier * qForm direction
  target_formula : residualTargetLift target =
    vadd (negTriple (residualSourceLift s)) (vsmul (2 * multiplier) direction)
  direction_bound : 2 * qForm direction ≤ n - 1
end TunnellMap



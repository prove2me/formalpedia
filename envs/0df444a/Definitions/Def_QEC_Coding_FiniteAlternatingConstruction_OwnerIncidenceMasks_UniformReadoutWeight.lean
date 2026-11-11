-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:12:24.582046+00:00
-- url     : https://prove2.me/theorems/68e45d60-479e-466d-aae6-ee605e4b212c
-- title:
--   Uniform Readout Weight
-- statement:
--   Definitions and structural lemmas for Uniform Readout Weight, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
set_option autoImplicit false
namespace QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
end QEC.Coding.BDL26UniformHistoryObstruction



-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
-- name    : QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T14:23:57.145181+00:00
-- url     : https://prove2.me/theorems/c728205f-bb80-4096-83bd-65d2eade72b4
-- title:
--   Local Background Comparison Depth
-- statement:
--   Definitions and structural lemmas for Local Background Comparison Depth, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators
def budgetDepth (B : Nat) : Nat := 2*(4*B+1)
end QEC.Coding.BDL26LocalBackgroundComparisonDepth



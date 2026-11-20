-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
-- name    : QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T14:17:38.798058+00:00
-- url     : https://prove2.me/theorems/06c12cfc-5dbc-46fc-b812-604e784a3749
-- title:
--   Local Background Comparison Response
-- statement:
--   Definitions and structural lemmas for Local Background Comparison Response, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26LocalBackgroundComparisonResponse
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators
abbrev W (S : OddScale) (n : Nat) := (SuffixData S n).family.Cochain1 (TopIndex n)
abbrev Q (S : OddScale) (n : Nat) := (state S (n+2)).presentation.Q
abbrev boundaries (S : OddScale) (n : Nat) :=
  LinearMap.range ((SuffixData S n).family.coboundary0 (TopIndex n))
def backgroundRestriction (S : OddScale) (n : Nat) (w : W S n) (A : Finset (Q S n)) : W S n :=
  BDL26NonzeroBackgroundComparisonStability.partialWord S n w A
end QEC.Coding.BDL26LocalBackgroundComparisonResponse



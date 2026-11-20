-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
-- name    : QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T14:29:28.647901+00:00
-- url     : https://prove2.me/theorems/b4fd400c-6f3c-46d9-8aed-8b04cff0ebdb
-- title:
--   Local Background Comparison Query Response
-- statement:
--   Definitions and structural lemmas for Local Background Comparison Query Response, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
def physicalRow (z : Coordinates S n (TopIndex n)) : Finset (Q S n) :=
  Finset.univ.filter fun q =>
    (SuffixData S n).family.coboundary1 (TopIndex n)
      (canonicalBasisWord (F:=BDL26Field) q) z ≠ 0
def physicalPullback (A : Finset (Coordinates S n (TopIndex n))) : Finset (Q S n) :=
  A.biUnion (physicalRow S n)
def queryStop (sigma0 : TopInput S n) (g e : W S n) : LevelIndex n :=
  stoppingLevel S n (perturbTop S n sigma0 g) e
def topQueries (sigma0 : TopInput S n) (g e : W S n) :
    Finset (Coordinates S n (TopIndex n)) :=
  queries S n e (queryStop S n sigma0 g e) (TopIndex n)
def queryMask (sigma0 : TopInput S n) (g e : W S n) : Finset (Q S n) :=
  physicalPullback S n (topQueries S n sigma0 g e)
def occupiedQueries (sigma0 : TopInput S n) (g e : W S n) : Finset (Q S n) :=
  hammingSupport g ∩ queryMask S n sigma0 g e
def fiveStepPhysicalBudget (S : OddScale) : Nat := 7 * windowBudget S 5 4
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse



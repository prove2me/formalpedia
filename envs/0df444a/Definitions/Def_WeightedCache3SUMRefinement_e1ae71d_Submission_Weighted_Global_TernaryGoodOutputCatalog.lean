-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGoodOutputCatalog
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGoodOutputCatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:21:39.825417+00:00
-- url     : https://prove2.me/theorems/1f2e2ae8-cb89-4b32-a5b0-4a005dd7793c
-- title:
--   TernaryGoodOutputCatalog
-- statement:
--   Definitions and structural lemmas for TernaryGoodOutputCatalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryLiteralOutputCap
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Mathlib.Algebra.Order.Floor.Div
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalGoodOutputCatalog
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalCoverGoodMaps TernaryCoverFibers WeightedGlobalLocalParameters WeightedGlobalPartitionCount
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {m p : ℕ} [Fact p.Prime]
def Rbar (m : ℕ) := 2^(fixedPi m 1)*3^(fixedPi m 2)
def cap (m p τ : ℕ) := (partitionLoss (2379766416784020*m) (292929977780940*m)*p*τ) ⌈/⌉ Rbar m
abbrev Output (m : ℕ) := {q // q∈vertices (fixedLength m) (fixedPi m)}
abbrev Record (m : ℕ) (I : Type*) := I×Output m
def native (w : Weight m p) (q : Output m) : ZMod p := outputHash w q.val
variable {I : Type*} [Fintype I] [DecidableEq I]
def catalog (maps : I → Weight m p) (τ : ℕ) : Finset (Record m I) :=
  univ.filter fun r => maps r.1∉rawBadMaps m p τ
def records (maps : I → Weight m p) (τ : ℕ) : List (Record m I) := (catalog maps τ).toList
def key (maps : I → Weight m p) (r : Record m I) : ℤ := (native (maps r.1) r.2).val
def raws (maps : I → Weight m p) (τ : ℕ) : List ℤ := (records maps τ).map (key maps)
def wordCodes (maps : I → Weight m p) (τ : ℕ) : List ℕ :=
  (records maps τ).map fun r => TernaryCodeSemantics.address r.2.val
def mapCodes {F : ℕ} (maps : Fin F → Weight m p) (τ : ℕ) : List ℕ :=
  (records maps τ).map fun r => (Fintype.equivFin (Fin F) r.1).val
def fiber (maps : I → Weight m p) (τ : ℕ) (o : ZMod p) : Finset (Record m I) :=
  (catalog maps τ).filter fun r => native (maps r.1) r.2=o
end ThreeSum.WeightedGlobalGoodOutputCatalog
end
end WeightedCache3SUMRefinement_e1ae71d



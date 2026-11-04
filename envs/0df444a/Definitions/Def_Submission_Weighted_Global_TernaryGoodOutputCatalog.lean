-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
-- name    : Submission_Weighted_Global_TernaryGoodOutputCatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:22.406587+00:00
-- url     : https://prove2.me/theorems/2c574abb-613e-45d8-9126-058833ef6a4c
-- title:
--   Ternary Good Output Catalog
-- statement:
--   Definitions and structural lemmas for Ternary Good Output Catalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGoodOutputCatalog.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryLiteralOutputCap
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Mathlib.Algebra.Order.Floor.Div
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalGoodOutputCatalog
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalCoverGoodMaps TernaryCoverFibers WeightedGlobalLocalParameters WeightedGlobalPartitionCount
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {m p : ℕ} [Fact p.Prime]
def Rbar (m : ℕ) := 2^(fixedPi m 1)*3^(fixedPi m 2)
def cap (m p τ : ℕ) := (partitionLoss (2380004124000*m) (292746547000*m)*p*τ) ⌈/⌉ Rbar m
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



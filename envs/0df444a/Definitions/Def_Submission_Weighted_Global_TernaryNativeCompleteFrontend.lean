-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativeCompleteFrontend
-- name    : Submission_Weighted_Global_TernaryNativeCompleteFrontend
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:34:52.290038+00:00
-- url     : https://prove2.me/theorems/8dbf45a9-08e5-4096-b65d-a921d302604e
-- title:
--   Ternary Native Complete Frontend
-- statement:
--   Definitions and structural lemmas for Ternary Native Complete Frontend, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCompleteFrontend.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativeCompleteFrontend
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCanonicalDictionaries
open TernaryExtensionEncoding WeightedGlobalNativeRequesterCoverage
open WeightedGlobalCanonicalNativeCompleteness LightTernarySourceHost
set_option maxHeartbeats 4000000
variable {p m F r : ℕ} [Fact p.Prime]
def localRecords (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) :=
  records (α := fixedAlpha m) right maps cap
def nativeDictionary (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) (i : ℕ) : ℤ :=
  dictionary ((localRecords maps cap right).map (native right maps)) p r i
def wordDictionary (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) (i : ℕ) : ℤ :=
  dictionary ((localRecords maps cap right).map wordCode) (4^(fixedLength m)) r i
def groupDictionary (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) (i : ℕ) : ℤ :=
  dictionary ((localRecords maps cap right).map mapCode) F r i
structure Sources (S : WeightedSourceCountExecutionFactory.Setup (r*fixedLength m))
    (maps : Fin F→Weight m p) (cap : ℕ) : Prop where
  leftSize : size S.left.xs S.left.J=(localRecords maps cap false).length^r
  rightSize : size S.right.xs S.right.J=(localRecords maps cap true).length^r
  leftNative : ∀j<(localRecords maps cap false).length^r,
    dictionary S.left.xs S.left.p0 S.left.J j=nativeDictionary (r := r) maps cap false j
  rightNative : ∀j<(localRecords maps cap true).length^r,
    dictionary S.right.xs S.right.p0 S.right.J j=nativeDictionary (r := r) maps cap true j
  leftWord : ∀j<(localRecords maps cap false).length^r,
    (TernaryCodeSemantics.address (S.front.E.word (S.left.key j)) : ℤ)=wordDictionary (r := r) maps cap false j
  rightWord : ∀j<(localRecords maps cap true).length^r,
    (TernaryCodeSemantics.address (S.front.E.word (S.right.key j)) : ℤ)=wordDictionary (r := r) maps cap true j
  leftGroup : ∀j<(localRecords maps cap false).length^r,
    (S.left.group j : ℤ)=groupDictionary (r := r) maps cap false j
  rightGroup : ∀j<(localRecords maps cap true).length^r,
    (S.right.group j : ℤ)=groupDictionary (r := r) maps cap true j
def queries {J : ℕ} (maps : Fin F→Weight m p) (τ U radix : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A : ℕ→ℤ) (nA : ℕ) : List TernaryWantedBatchIndex.Entry :=
  TernaryWantedBatchIndex.entries p (4^(fixedLength m)) F r
    (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
    (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) (target H U radix A) (position J) (nA*2^J)
structure Queries {J : ℕ} (S : WeightedSourceCountExecutionFactory.Setup (r*fixedLength m))
    (maps : Fin F→Weight m p) (τ U radix : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A : ℕ→ℤ) (nA : ℕ) (pos : ℕ→ℕ) : Prop where
  count : S.front.count=(queries maps τ U radix H A nA).length
  group : ∀i<S.front.count, S.front.group i=(TernaryWantedBatchIndex.get (queries maps τ U radix H A nA) i).2.2
  word : ∀i<S.front.count, TernaryCodeSemantics.address (S.front.Q i)=
    (TernaryWantedBatchIndex.get (queries maps τ U radix H A nA) i).2.1
  position : ∀i<S.front.count, pos i=(TernaryWantedBatchIndex.get (queries maps τ U radix H A nA) i).1
end ThreeSum.WeightedGlobalNativeCompleteFrontend



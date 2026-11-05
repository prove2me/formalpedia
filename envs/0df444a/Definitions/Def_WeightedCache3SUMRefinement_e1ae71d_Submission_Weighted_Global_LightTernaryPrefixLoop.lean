-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixLoop
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixLoop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:56:26.567457+00:00
-- url     : https://prove2.me/theorems/f405c464-bb2a-4fe8-9047-2e8dac48c834
-- title:
--   LightTernaryPrefixLoop
-- statement:
--   Definitions and structural lemmas for LightTernaryPrefixLoop, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixLoop.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_Submission_ThreeSum_LightTernaryBudgetStep
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalPrefixLoop
open Light
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
def headerWrites : List (ℕ×ℕ) := [
  (6,3),(12,19),(14,17),(15,16),(16,18),(17,14),(21,21),(22,15),
  (29,3),(35,19),(37,17),(38,16),(39,18),(40,14),(44,21),(45,15),
  (46,12),(47,17),(48,16),(50,14),(52,15),
  (58,12),(62,17),(63,16),(64,28),(65,14),(66,13),(71,22),(72,14),
  (75,12),(79,17),(80,16),(81,29),(82,14),(83,13),(88,22),(89,14),
  (93,27),(95,26),(102,23),(103,24)]
def stores : List (ℕ×ℕ)→ Stmt
  | []=>.skip
  | (field,reg)::xs=>.store (v 1 +' k field) (v reg) ;; stores xs
def headerBody : Stmt :=
  .call 189 [v 0,v 1,k 106] 30 ;;
  .set 12 (M (v 2)) ;;
  .set 13 (M (v 2 +' k 1)) ;;
  .set 14 (M (v 2 +' k 2)) ;;
  .set 15 (M (v 2 +' k 3)) ;;
  .set 16 (M (v 2 +' k 4)) ;;
  .set 17 (M (v 2 +' k 5)) ;;
  .set 18 (M (v 2 +' k 6)) ;;
  .set 19 (v 6 *' v 5) ;;
  .set 20 (v 7 *' v 3) ;;
  .call 180 [k 2,v 20] 21 ;;
  .set 22 (v 8 *' v 3) ;;
  .set 23 ((v 12 +' k 1) *' v 16) ;;
  .set 24 (v 12 *' v 16) ;;
  .set 25 (k 2738 *' v 22 +' k 6 *' v 20) ;;
  .set 26 (v 25 -' v 13 -' k 1) ;;
  .call 190 [v 9,v 10,v 3] 27 ;;
  .set 28 (M (v 0 +' k 99) +' v 24) ;;
  .set 29 (M (v 0 +' k 100) +' v 24) ;;
  stores headerWrites ;;
  .store (v 1 +' k 104) (k 0) ;;
  .set 0 (v 19)
def seedArgs : List Expr := (List.range 48).map (fun i=>M (v 3 +' k i))
def prepareBody : Stmt :=
  .set 17 (v 15 +' k 1) ;;
  .call 184 [v 17,v 0,v 1,v 6] 18 ;;
  .call 191 [v 4,v 5,v 18,v 17,v 0,v 2,v 16,v 7,v 8,v 9,v 10,v 11] 19 ;;
  .store (v 3 +' k 4) (v 16) ;;
  .store (v 3 +' k 6) (v 16) ;;
  .store (v 3 +' k 24) (v 5) ;;
  .store (v 3 +' k 39) (v 17) ;;
  .call 195 [v 3 +' k 41,v 2,v 12,v 13,v 14] 26 ;;
  .set 0 (v 19)
def stepBody : Stmt :=
  .call 196 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16] 19 ;;
  .call 178 seedArgs 26 ;;
  .call 188 [M (v 3 +' k 9),M (v 3 +' k 8),M (v 3 +' k 10),
    M (v 3 +' k 13),M (v 3 +' k 12),M (v 3 +' k 14),
    M (v 3 +' k 17),M (v 3 +' k 16),M (v 3 +' k 18)] 26 ;;
  .call 189 [M (v 3 +' k 47),M (v 3 +' k 3),v 19 *' v 11] 26 ;;
  .set 0 (v 19)
def roundArgs : List Expr :=
  [v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 17,v 16]
def loopBody : Stmt :=
  .set 16 (k 1) ;;
  .for 17 (v 0) (.call 192 roundArgs 18 ;; .set 16 (v 18)) ;;
  .set 0 (v 16)
def initBody : Stmt :=
  .call 189 [v 16,v 4,k 48] 17 ;;
  .call 186 [M (v 4 +' k 8),M (v 4 +' k 10),M (v 4 +' k 12),
    M (v 4 +' k 14),M (v 4 +' k 16),M (v 4 +' k 18)] 17 ;;
  .call 0 [M (v 4 +' k 3),v 12,k 0] 17 ;;
  .call 193 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15] 0
def priorProcs (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  LightWeightedGlobalSeedController.program p R S K raws words maps xl yl zl xr yr zr++
    LightWeightedGlobalPrefixSetup.allocatedProgram.map (ReportingHostRelocation.relocate 179)++
    LightTernaryInitialKeys.program.map (ReportingHostRelocation.relocate 185)++
    LightTernaryCommitKeys.program.map (ReportingHostRelocation.relocate 187)++
    LightTernaryCommitSpan.program.map (ReportingHostRelocation.relocate 189)
def program (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  priorProcs p R S K raws words maps xl yl zl xr yr zr++
    [LightTernaryRepeatWord.body,headerBody,stepBody,loopBody,initBody,LightTernaryBudgetStep.body,prepareBody]
def args (rounds m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase : ℕ) : List ℤ :=
  [rounds,m,F,p,liveSeed,template,liveHeader,prefixFree,alpha2,alphaRank,localQ,radix,J,a,b,scaleBase]
def stepArgs (m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase j power : ℕ) : List ℤ :=
  [m,F,p,liveSeed,template,liveHeader,prefixFree,alpha2,alphaRank,localQ,radix,J,a,b,scaleBase,j,power]
def time (r stepTime : ℕ) : ℕ := r*(stepTime+200)+100
def Inv (argv : List ℤ) (p : ℕ) (I : ℕ→ (ℕ→ ℤ)→ Prop) (j : ℕ) (σ : State) : Prop :=
  ∃ ret ν, σ=⟨frame (argv++[((p^j:ℕ):ℤ),(j:ℤ),ret]),ν⟩ ∧ I j ν
end ThreeSum.LightWeightedGlobalPrefixLoop
end
end WeightedCache3SUMRefinement_e1ae71d



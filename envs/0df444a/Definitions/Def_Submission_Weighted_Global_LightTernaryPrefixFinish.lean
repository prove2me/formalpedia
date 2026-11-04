-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
-- name    : Submission_Weighted_Global_LightTernaryPrefixFinish
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:44:04.356452+00:00
-- url     : https://prove2.me/theorems/2d368f60-f61a-42b2-90db-83e50b8bab08
-- title:
--   Light Ternary Prefix Finish
-- statement:
--   Definitions and structural lemmas for Light Ternary Prefix Finish, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixFinish.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFullController
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixProgramLibrary
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalPrefixFinish
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
def body : Stmt :=
  .call 178 seedArgs 26 ;;
  .call 188 [M (v 3 +' k 9),M (v 3 +' k 8),M (v 3 +' k 10),
    M (v 3 +' k 13),M (v 3 +' k 12),M (v 3 +' k 14),
    M (v 3 +' k 17),M (v 3 +' k 16),M (v 3 +' k 18)] 26 ;;
  .call 189 [M (v 3 +' k 47),M (v 3 +' k 3),v 19 *' v 11] 26 ;;
  .set 0 (v 19)
def header (C : Config) (n dB dC dP tB tC tP newSpan : ℕ) : List ℤ :=
  LightWeightedGlobalSeedController.args (withSeed C 0).argv n dB dC dP tB tC tP newSpan
structure Layout (C : Config) (lim : Limits) (seed rows newSpan : ℕ) : Prop where
  seedEnd : seed+48≤C.Bold
  BC : C.Bold+C.nB≤C.Cold
  CO : C.Cold+C.nC≤C.Oold
  OB : C.Oold+C.nO≤C.Bnew
  OC : C.Oold+C.nO≤C.Cnew
  OO : C.Oold+C.nO≤C.Onew
  Bspace : C.Bnew+C.nB≤lim.space
  Cspace : C.Cnew+C.nC≤lim.space
  Ospace : C.Onew+C.nO≤lim.space
  keysSpan : C.Oold+C.nO≤C.catalog
  spanApart : C.catalog+rows*C.J≤newSpan
  spanSpace : newSpan+rows*C.J≤lim.space
def Committed (C : Config) (rows newSpan : ℕ) (ξ ν : ℕ→ℤ) : Prop :=
  Kept ξ ν C.Bold ∧
  (∀i<C.nB, ν (C.Bold+i)=ξ (C.Bnew+i)) ∧
  (∀i<C.nC, ν (C.Cold+i)=ξ (C.Cnew+i)) ∧
  (∀i<C.nO, ν (C.Oold+i)=ξ (C.Onew+i)) ∧
  (∀k<rows, ∀i<C.J, ν (C.catalog+C.J*k+i)=ξ (newSpan+C.J*k+i)) ∧
  (∀x, (x<C.Bold ∨ C.Oold+C.nO≤x)→(x<C.catalog ∨ C.catalog+rows*C.J≤x)→ν x=ξ x)
def time (C : Config) (n seedTime rows : ℕ) : ℕ :=
  LightWeightedGlobalSeedController.time n seedTime (LightSpanCatalogStep.time C.J C.p C.catalogRows)+
    LightTernaryCommitKeys.time C.nB C.nC C.nO+copyTime (rows*C.J)+5000
end ThreeSum.LightWeightedGlobalPrefixFinish



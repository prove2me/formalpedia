-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
-- name    : Submission_Weighted_Global_LightTernaryColoredSolver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:38:09.751424+00:00
-- url     : https://prove2.me/theorems/31fa5862-9c1d-4579-aaaa-8fcbc8a3ca26
-- title:
--   Light Ternary Colored Solver
-- statement:
--   Definitions and structural lemmas for Light Ternary Colored Solver, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColoredSolver.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalColoredSolver
open Light
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
def arenaLibrary (D E : ℕ) : Program := ReportingHostRelocation.program
  (LightWeightedGlobalColorPreparation.program 2) (LightWeightedGlobalArenaTemplate.program D E)
def prepArena (radix D E : ℕ) : Program := ReportingHostRelocation.program
  (LightWeightedGlobalColorPreparation.program radix) (LightWeightedGlobalArenaTemplate.program D E)
def budgetLibrary (radix D E K bDigit a b scaleBase : ℕ) : Program :=
  ReportingHostRelocation.program (prepArena radix D E) (LightTernaryInitialBudgets.program K bDigit a b scaleBase)
def libraries (radix D E K bDigit a b scaleBase p R F : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (budgetLibrary radix D E K bDigit a b scaleBase)
    (LightWeightedGlobalPrefixLoop.program p R F K raws words maps xl yl zl xr yr zr)
def H (i : ℕ) : Expr :=M (v 5 +' k i)
def A (slot : ℕ) : Expr :=v 6 +' k slot *' v 7
def arenaArgs (p R F : ℕ) : List Expr :=
  [v 1 +' H 14,v 6,H 6,H 3,H 7,H 5,H 8,H 9,H 10,H 6,H 7,H 18,H 16,
    k p,k R,k F,H 17,k 0,k 0,k 0,k 0,k 0,k 0]
def loopArgs (m F p alpha2 alphaRank localQ R a b scaleBase : ℕ) : List Expr :=
  [H 15,k m,k F,k p,v 9,v 6,v 10,v 11,k alpha2,k alphaRank,k localQ,k R,H 16,
    k a,k b,k scaleBase,v 8]
def cleanupArgs : List Expr :=
  [H 0,H 1,H 2,H 3,H 4,H 5,A 4,A 5,A 7,A 8,v 12,A 6,v 14,
    A 9,A 10,A 16,A 16 +' H 3,
    A 16 +' H 3 +' k 1,A 16 +' H 3 +' k 1 +' k 2 *' H 5,A 17,A 17 +' H 5]
def hostArgs : List Expr := (List.range 106).map fun i =>
  if i=11 ∨ i=34 then k 0 else M (v 10 +' k i)
def postArgs : List Expr :=cleanupArgs++
  [A 10,A 16,A 16 +' H 3,A 16 +' H 3 +' k 1 +' k 2 *' H 5,A 17,A 17 +' H 5]++
  [H 0,H 1,A 26,A 19,A 25,M (v 10 +' k 104)]++
  [A 10,k 0,A 16 +' H 3 +' k 1 +' k 2 *' H 5,k 0,A 28,A 29,A 25,
    M (v 10 +' k 104),A 53]++hostArgs
def body (pPost m F p alpha2 alphaRank localQ R a b scaleBase L : ℕ) : Stmt :=
  .call 50 [v 0,v 1,v 2,v 3,v 4] 5 ;;
  .ite (v 5 =' k 0) (.set 0 (k 0)) (
    .set 6 (H 13) ;;
    .call 52 (arenaArgs p R F) 15 ;;
    .set 7 (M (v 6 +' k 1) -' M (v 6)) ;;
    .set 8 (A 2) ;; .set 9 (A 3) ;; .set 10 (A 1) ;; .set 11 (A 13) ;;
    .call 54 [v 1,H 16,H 9,v 8,v 8 +' k 48] 15 ;;
    .call 249 (loopArgs m F p alpha2 alphaRank localQ R a b scaleBase) 12 ;;
    .set 13 (k L *' H 15) ;;
    .set 14 (k 2 *' v 13) ;;
    .call pPost postArgs 0)
def program (radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (post : Program) (postMain : ℕ) : Program :=
  let pre:=libraries radix D E K bDigit a b scaleBase p R F raws words maps xl yl zl xr yr zr
  ReportingHostRelocation.program pre post++
    [body (pre.length+postMain) m F p alpha2 alphaRank localQ R a b scaleBase L]
end ThreeSum.LightWeightedGlobalColoredSolver



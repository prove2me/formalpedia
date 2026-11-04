-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
-- name    : Submission_Weighted_Global_LightTernarySeedController
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:23:58.608745+00:00
-- url     : https://prove2.me/theorems/b3f78454-ab61-44fc-a07d-2d30b0d6ca0f
-- title:
--   Light Ternary Seed Controller
-- statement:
--   Definitions and structural lemmas for Light Ternary Seed Controller, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedController.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalSeedController
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
def seedArgs (seed : Expr) : List Expr :=
  [v 0,seed,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,
    v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,
    v 30,v 31,v 32,v 33,v 34,v 35,v 36,v 37,v 38,v 39]
def body : Stmt :=
  .for 48 (v 40) (.call LightWeightedGlobalSeedScore.entry (seedArgs (v 48)) 49) ;;
  .call (LightWeightedGlobalSeedScore.entry+1) [v 35,v 36,v 37,v 38,v 40,v 41,v 42,v 43,v 44,v 45,v 46] 50 ;;
  .ite (k 0 <' v 50)
    (.set 51 (v 50 -' k 1) ;;
      .call LightWeightedGlobalSeedScore.entry (seedArgs (v 51)) 49 ;;
      .call 1 [v 3,v 4,v 0 +' v 51 *' (v 2 +' k 2),v 47,v 2,v 5] 52)
    .skip ;;
  .set 0 (v 50)
def program (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  LightWeightedGlobalSeedScore.program p R S K raws words maps xl yl zl xr yr zr++
    [LightTernaryRowSelector.body,body]
def time (seedCount seedTime spanTime : ℕ) : ℕ :=
  (seedCount+1)*(seedTime+200)+LightTernaryRowSelector.time seedCount+spanTime+1000
def entry : ℕ := LightWeightedGlobalSeedScore.entry+2
def args (base : List ℤ) (seedCount dB dC dP tB tC tP newSpan : ℕ) : List ℤ :=
  base++[(seedCount : ℤ),dB,dC,dP,tB,tC,tP,newSpan]
def Inv (argv : List ℤ) (I : ℕ → (ℕ → ℤ) → Prop) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame (argv++[(i : ℤ),r]),ν⟩ ∧ I i ν
end ThreeSum.LightWeightedGlobalSeedController



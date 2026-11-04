-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPairSearchMain
-- name    : Submission_ThreeSum_LightPairSearchMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:49.362197+00:00
-- url     : https://prove2.me/theorems/d6cb582e-1b67-4672-9826-68a93487a208
-- title:
--   Light Pair Search Main
-- statement:
--   Definitions and structural lemmas for Light Pair Search Main, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchMain.lean

import Definitions.Def_Submission_ThreeSum_LightPairSearch
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
def body (pRow : ℕ) : Stmt :=
  .set 2 (k 0) ;;
  .for 3 (v 0) (.call pRow [v 0,v 3,v 1,v 2] 2) ;;
  .set 0 (v 2)
def time (q T : ℕ) : ℕ := q*(rowTime q T+60)+20
def Inv (I : (ℕ → ℤ) → Prop) (q ctx : ℕ)
    (good : ℕ → ℕ → Prop) [DecidableRel good] (i : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ, σ=⟨frame [q,ctx,first (goodCode q good) (i*q),i],ν⟩ ∧ I ν
variable {lim : Limits} {P : Program}
end ThreeSum.LightPairSearch



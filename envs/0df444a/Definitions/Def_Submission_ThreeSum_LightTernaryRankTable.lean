-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
-- name    : Submission_ThreeSum_LightTernaryRankTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:42:12.427458+00:00
-- url     : https://prove2.me/theorems/a984f4b3-94f4-4dad-93e3-04b119edcf80
-- title:
--   Light Ternary Rank Table
-- statement:
--   Definitions and structural lemmas for Light Ternary Rank Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRankTable.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryRankTable
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType
  ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}
def roundBody (pRank : ℕ) : Stmt :=
  .set 6 (M (v 1 +' v 5)) ;;
  .call pRank [v 0,v 6,v 3] 7 ;;
  .store (v 4 +' v 5) (v 7)
def body (pRank : ℕ) : Stmt := .for 5 (v 2) (roundBody pRank)
def time (N n : ℕ) : ℕ := n*(LightTernaryRank.time N+100)+20
def values (N : ℕ) (codes : ℕ → ℕ) (j : ℕ) : ℤ :=
  LightTernaryRank.partialRank N (codes j) N
def Inv (μ : ℕ → ℤ) (N a n powers dst : ℕ) (codes : ℕ → ℕ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ code result : ℤ, σ=⟨frame [N,a,n,powers,dst,j,code,result],
    wrote μ dst (values N codes) j⟩
def program : Program := [body 1,LightTernaryRank.body 2,
  LightTernaryCodes.digitBody 3,LightMaskErase.body 3]
end ThreeSum.LightTernaryRankTable



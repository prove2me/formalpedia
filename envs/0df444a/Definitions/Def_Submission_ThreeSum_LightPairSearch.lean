-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPairSearch
-- name    : Submission_ThreeSum_LightPairSearch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:25:31.454823+00:00
-- url     : https://prove2.me/theorems/3f23b602-3938-4737-8af6-75a22f2929e2
-- title:
--   Light Pair Search
-- statement:
--   Definitions and structural lemmas for Light Pair Search, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearch.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_PairFirst
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 300000
set_option maxRecDepth 18000
def rowBody (pPred : ℕ) : Stmt :=
  .for 4 (v 0)
    (.ite (v 3 =' k 0)
      (.call pPred [v 1,v 4,v 2] 5 ;;
        .ite (k 0 <' v 5) (.set 3 (k 1 +' v 1 *' v 0 +' v 4)) .skip)
      .skip) ;;
  .set 0 (v 3)
def rowTime (q T : ℕ) : ℕ := q*(T+100)+20
def RowInv (I : (ℕ → ℤ) → Prop) (q u ctx : ℕ)
    (good : ℕ → ℕ → Prop) [DecidableRel good] (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [q,u,ctx,first (goodCode q good) (u*q+j),j,r],ν⟩ ∧ I ν
variable {lim : Limits} {P : Program}
end ThreeSum.LightPairSearch



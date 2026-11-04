-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
-- name    : Submission_ThreeSum_LightOriginalSurvivorPair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:47:31.801032+00:00
-- url     : https://prove2.me/theorems/a85be2fa-eefa-4236-b4a9-24dbe00adf30
-- title:
--   Light Original Survivor Pair
-- statement:
--   Definitions and structural lemmas for Light Original Survivor Pair, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
def body : Stmt :=
  _root_.Light.Stmt.seq
    (.call 7 [v 6, v 3, v 8, v 10, v 13, v 2, v 0, v 1, v 4, v 5, v 11, v 12, k 1, v 14, v 15, v 16] 21)
    (_root_.Light.Stmt.seq
      (.call 7
        [v 7, v 5, v 9, v 10, v 17, v 4, v 0, v 1, v 2, v 3, v 11, v 12,
          (_root_.Light.Expr.op _root_.Light.Op.sub) (k 0) (k 1), v 18, v 19, v 20]
        22)
      (.ite (_root_.Light.Cond.eq (v 21) (k 0)) (.set 0 (v 22)) (.set 0 (k 1))))
def program : Program :=
  LightOriginalSurvivorStage.program ++ [body]
def time (keysB keysC : ℕ → ℕ) (nA nB nC L : ℕ) : ℕ :=
  LightOriginalSurvivorStage.time keysB nB nA L + LightOriginalSurvivorStage.time keysC nC nA L + 200
def Output (ν : ℕ → ℤ) (keys : ℕ → ℕ) (values : ℕ → ℤ) (n out dstValues dstKeys lengthCell : ℕ) : Prop :=
  ν lengthCell = ((indices keys n).length : ℤ) ∧
    Seg ν out (cells (indices keys n)) ∧
      (∀ i < (indices keys n).length, ν (dstValues + i) = values (index keys n i)) ∧
        (∀ i < (indices keys n).length, ν (dstKeys + i) = (keys (index keys n i) : ℤ))
variable {lim : Limits}
def cleanupFlag (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) : ℕ :=
  if LightDeletedTwoSum.flag (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 = 0 then
    LightDeletedTwoSum.flag (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1)
  else 1
end ThreeSum.LightOriginalSurvivorPair



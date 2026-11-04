-- Prove2me | Definitions.Def_Submission_ThreeSum_PairFirst
-- name    : Submission_ThreeSum_PairFirst
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:21:46.878294+00:00
-- url     : https://prove2.me/theorems/fdd00372-f7ba-428c-a349-dcdb9b446802
-- title:
--   Pair First
-- statement:
--   Definitions and structural lemmas for Pair First, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PairFirst.lean

import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.DivMod
import Definitions.Def_Submission_ThreeSum_LightArray
set_option autoImplicit false
namespace ThreeSum.LightPairSearch
set_option maxHeartbeats 300000
def first (good : ℕ → Prop) [DecidablePred good] : ℕ → ℕ
  | 0 => 0
  | k+1 => if first good k=0 ∧ good k then k+1 else first good k
def goodCode (q : ℕ) (good : ℕ → ℕ → Prop) (k : ℕ) : Prop := good (k/q) (k%q)
instance (q : ℕ) (good : ℕ → ℕ → Prop) [DecidableRel good] : DecidablePred (goodCode q good) :=
  fun k => inferInstanceAs (Decidable (good (k/q) (k%q)))
end ThreeSum.LightPairSearch



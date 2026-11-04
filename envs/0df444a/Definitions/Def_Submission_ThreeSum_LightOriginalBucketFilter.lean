-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
-- name    : Submission_ThreeSum_LightOriginalBucketFilter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:42.767494+00:00
-- url     : https://prove2.me/theorems/2a2bf416-a1ce-4c99-8dbf-efac5e52667f
-- title:
--   Light Original Bucket Filter
-- statement:
--   Definitions and structural lemmas for Light Original Bucket Filter, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalBucketFilter.lean

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightOriginalBucketFilter
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
def good (keys counts : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).filter fun i => counts (keys i) = 1
def bad (keys counts : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).filter fun i => counts (keys i) ≠ 1
def cells (xs : List ℕ) : List ℤ :=
  xs.map (fun i => (i : ℤ))
def roundBody : Stmt :=
  _root_.Light.Stmt.seq (.set 8 (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 0) (v 7))))
    (_root_.Light.Stmt.seq (.set 9 (M ((_root_.Light.Expr.op _root_.Light.Op.add) (v 2) (v 8))))
      (.ite (_root_.Light.Cond.eq (v 9) (k 1))
        (_root_.Light.Stmt.seq (.store ((_root_.Light.Expr.op _root_.Light.Op.add) (v 4) (v 5)) (v 7))
          (.set 5 ((_root_.Light.Expr.op _root_.Light.Op.add) (v 5) (k 1))))
        (_root_.Light.Stmt.seq
          (.store
            ((_root_.Light.Expr.op _root_.Light.Op.add) ((_root_.Light.Expr.op _root_.Light.Op.add) (v 4) (v 1)) (v 6))
            (v 7))
          (.set 6 ((_root_.Light.Expr.op _root_.Light.Op.add) (v 6) (k 1))))))
def body : Stmt :=
  _root_.Light.Stmt.seq (.set 5 (k 0))
    (_root_.Light.Stmt.seq (.set 6 (k 0)) (_root_.Light.Stmt.seq (.for 7 (v 1) roundBody) (.set 0 (v 6))))
def time (n : ℕ) : ℕ :=
  200 * n + 100
def Inv (μ : ℕ → ℤ) (keyBase n hist q out : ℕ) (keys counts : ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ key count : ℤ,
    ∃ ν : ℕ → ℤ,
      σ =
          ⟨frame [keyBase, n, hist, q, out, (good keys counts i).length, (bad keys counts i).length, i, key, count],
            ν⟩ ∧
        Seg ν out (cells (good keys counts i)) ∧
          Seg ν (out + n) (cells (bad keys counts i)) ∧ SameOutside μ ν out (2 * n)
variable {lim : Limits} {P : Program}
end ThreeSum.LightOriginalBucketFilter



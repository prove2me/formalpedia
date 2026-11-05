-- Prove2me | Definitions.Def_FloorDepth
-- name    : FloorDepth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/bb5b927b-ed16-4375-b5d2-c7cfaa577e33
-- title:
--   FloorDepth definitions
-- statement:
--   Executable depth for floor-child recursion, with monotonicity and exact row-stock transfer. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorDepth.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorDepth.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
set_option autoImplicit true
namespace FloorDepth
def child (m t e : ℕ) : ℕ := t * (e / m)
theorem child_lt (m t e : ℕ) (ht : t < m) (he : m ≤ e) : child m t e < e := by
  have hm : 0 < m := Nat.zero_lt_of_lt ht
  have hf : 0 < e / m := Nat.div_pos he hm
  calc
    child m t e = t * (e / m) := rfl
    _ < m * (e / m) := Nat.mul_lt_mul_of_pos_right ht hf
    _ ≤ e := Nat.mul_div_le e m
def depth (m t : ℕ) (ht : t < m) (e : ℕ) : ℕ :=
  if h : e < m then 0 else 1 + depth m t ht (child m t e)
termination_by e
decreasing_by exact child_lt m t e ht (Nat.le_of_not_gt h)
end FloorDepth



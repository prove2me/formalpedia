-- Prove2me | Definitions.Def_GTWSched_FixedOrder_Algorithm
-- name    : GTWSched_FixedOrder_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:20:19.37897+00:00
-- url     : https://prove2.me/theorems/501d9dca-7fb4-439b-a97d-940407899af7
-- title:
--   §2.2, p. 337 — fixed-order schedules, total discrepancy, blocks, and the block-shifting algorithm
-- statement:
--   For tasks in a prescribed order, task $i$ has a preferred starting time $a_i$ and length $l_i$. A schedule $s$ for the first $n$ tasks starts each task at a nonnegative time, allows idle time, and satisfies $s_i+l_i\le s_{i+1}$ for successive tasks. Its total discrepancy is
--
--   $$
--   \operatorname{cost}_n(s)=\sum_{i=0}^{n-1}|s_i-a_i|.
--   $$
--
--   A block is a maximal run of tasks that meet exactly, with no idle time between them. Tasks starting later than preferred belong to Decrease; the others belong to Increase. The algorithm starts the first task at its preferred time. Each subsequent task starts at its preferred time if the preceding task has finished, and otherwise starts when that task finishes. If adding it makes the final block's Decrease and Increase counts equal and that block starts after time zero, the algorithm shifts the whole block earlier until it reaches time zero, a preceding block, or a task's preferred start. Its schedule for $n$ tasks is $S_n$.
--
--   These definitions specify the schedules, cost, blocks, counts, and actual procedure used in Theorem 2. An unordered feasibility predicate is also provided for Theorem 3.
--
--   **Formalization Note** Tasks are indexed from zero; task $i$ represents the paper's $T_{i+1}$. Starts for tasks beyond the first $n$ are irrelevant. Nonnegative starts are the scheduling convention used in the paper's stopping rule.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), pp. 330–331, §1; p. 337, §2.2

import Mathlib

namespace GTWSched.FixedOrder

/-- Feasible starts for the first `n` tasks in their prescribed order. -/
def FixedFeasible (l : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) : Prop :=
  (∀ i < n, 0 ≤ s i) ∧ ∀ i, i + 1 < n → s i + l i ≤ s (i + 1)

/-- Total absolute discrepancy of the first `n` tasks. -/
noncomputable def cost (a : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, |s i - a i|

/-- First index of the contiguous block containing task `m`. -/
noncomputable def blockStart (l s : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
      if s m + l m = s (m + 1) then blockStart l s m else m + 1

/-- A maximal contiguous block `[j,k]` among the first `n` tasks. -/
def IsBlock (l : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) (j k : ℕ) : Prop :=
  j ≤ k ∧ k < n ∧
    (∀ i, j ≤ i → i < k → s i + l i = s (i + 1)) ∧
    (j = 0 ∨ s (j - 1) + l (j - 1) < s j) ∧
    (k + 1 = n ∨ s k + l k < s (k + 1))

/-- Number of tasks later than their preferred starts in `[j,m]`. -/
noncomputable def decCount (a s : ℕ → ℝ) (j m : ℕ) : ℕ :=
  ((Finset.Icc j m).filter (fun i => a i < s i)).card

/-- Number of tasks no later than their preferred starts in `[j,m]`. -/
noncomputable def incCount (a s : ℕ → ℝ) (j m : ℕ) : ℕ :=
  ((Finset.Icc j m).filter (fun i => s i ≤ a i)).card

/-- End of the preceding block, or time zero for the first block. -/
def prevEnd (l s : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else s (j - 1) + l (j - 1)

/-- Shift as far as the first stopping event: time zero, preceding block, or a
decreasing task reaching its preferred start. -/
noncomputable def shiftAmount (a l s : ℕ → ℝ) (j m : ℕ) : ℝ :=
  (Finset.Icc j m).toList.foldl
    (fun d i => if a i < s i then min d (s i - a i) else d)
    (s j - prevEnd l s j)

/-- Move precisely the tasks in `[j,m]` earlier by `d`. -/
noncomputable def shiftRange (s : ℕ → ℝ) (j m : ℕ) (d : ℝ) : ℕ → ℝ :=
  fun i => if j ≤ i ∧ i ≤ m then s i - d else s i

/-- Set the start of the newly appended task, leaving prior starts intact. -/
noncomputable def place (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℕ → ℝ :=
  fun i => if i = n then x else s i

/-- One step of the block-shifting algorithm in §2.2. -/
noncomputable def step (a l : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) : ℕ → ℝ :=
  if n = 0 then place s 0 (a 0)
  else
    let finish := s (n - 1) + l (n - 1)
    if finish ≤ a n then place s n (a n)
    else
      let r := place s n finish
      let j := blockStart l r n
      if decCount a r j n = incCount a r j n ∧ r j ≠ 0 then
        shiftRange r j n (shiftAmount a l r j n)
      else r

/-- `sched a l n` is the paper's schedule `Sₙ`, with `S₀` empty. -/
noncomputable def sched (a l : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | n + 1 => step a l n (sched a l n)

/-- Feasible starts for the first `n` tasks with no prescribed order. -/
def UnorderedFeasible (l : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) : Prop :=
  (∀ i < n, 0 ≤ s i) ∧
    ∀ i < n, ∀ j < n, i ≠ j →
      s i + l i ≤ s j ∨ s j + l j ≤ s i

end GTWSched.FixedOrder



-- Prove2me | Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
-- name    : JohnsonFlowShop_ThreeStage_asapSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:42:05.451207+00:00
-- url     : https://prove2.me/theorems/3ce36ee8-fcb2-4499-a887-b0cd56cee61b
-- title:
--   As-soon-as-possible three-machine schedule of an order
-- statement:
--   Let $\sigma$ be an ordering of the $n$ items, with $\sigma(k)$ the item in position $k$ (positions $0, 1, \dots, n-1$). The **as-soon-as-possible schedule** of $\sigma$ processes the items in the order $\sigma$ on all three machines and starts every item on every machine as early as the rules allow.
--
--   Write $c_1(m), c_2(m), c_3(m)$ for the times at which machines 1, 2, 3 finish the items in the first $m$ positions, with $c_1(0) = c_2(0) = c_3(0) = 0$ and, for the item $i = \sigma(m)$ in position $m$,
--
--   $$
--   c_1(m+1) = c_1(m) + A_i,\qquad c_2(m+1) = \max\bigl(c_2(m), c_1(m+1)\bigr) + B_i,\qquad c_3(m+1) = \max\bigl(c_3(m), c_2(m+1)\bigr) + C_i .
--   $$
--
--   If item $i$ is in position $m$, its start times are $c_1(m)$ on machine 1, $\max(c_2(m), c_1(m) + A_i)$ on machine 2 and $\max(c_3(m), \text{its machine-2 completion time})$ on machine 3.
--
--   This is the schedule Johnson's time-scale diagram on p. 66 describes: there is no delay on machine 1, and the delays $Y_i$ on machine 3 are forced by the preceding stages.
--
--   **Formalization Note** The definition file contains the recursion `asapDone` on the number of processed positions and the three start-time functions `asapStart1`, `asapStart2`, `asapStart3`, indexed by item (the position of item `i` is `σ.symm i`).
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 62, proof of Lemma 1 ("we may start each item as soon as possible"), and p. 66, time scales for each machine

import Mathlib

namespace JohnsonFlowShop.ThreeStage

/-- `asapDone A B C σ m` is the triple of times at which machines 1, 2 and 3 finish the items in
the first `m` positions of the order `σ` (`σ k` = item in position `k`, positions `0` to `n`
minus one) under the as-soon-as-possible schedule; it is `(0, 0, 0)` for `m = 0`. With
`i = σ m` the item in position `m` and `(c₁, c₂, c₃)` the times after `m` positions:
`c₁' = c₁ + A i`, `c₂' = max c₂ c₁' + B i`, `c₃' = max c₃ c₂' + C i`. -/
def asapDone {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℕ → ℝ × ℝ × ℝ
  | 0 => (0, 0, 0)
  | m + 1 =>
    if h : m < n then
      let c := asapDone A B C σ m
      let i := σ ⟨m, h⟩
      let d₁ := c.1 + A i
      let d₂ := max c.2.1 d₁ + B i
      (d₁, d₂, max c.2.2 d₂ + C i)
    else asapDone A B C σ m

/-- Machine 1 start time of item `i` in the as-soon-as-possible schedule of `σ`: the time at
which machine 1 finishes the items placed before `i` (there are no delays on machine 1). -/
def asapStart1 {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  (asapDone A B C σ (σ.symm i).val).1

/-- Machine 2 start time of item `i` in the as-soon-as-possible schedule of `σ`: the later of
its machine 1 completion time and the time machine 2 finishes the items placed before `i`. -/
def asapStart2 {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  max (asapDone A B C σ (σ.symm i).val).2.1 (asapStart1 A B C σ i + A i)

/-- Machine 3 start time of item `i` in the as-soon-as-possible schedule of `σ`: the later of
its machine 2 completion time and the time machine 3 finishes the items placed before `i`. -/
def asapStart3 {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  max (asapDone A B C σ (σ.symm i).val).2.2 (asapStart2 A B C σ i + B i)

end JohnsonFlowShop.ThreeStage



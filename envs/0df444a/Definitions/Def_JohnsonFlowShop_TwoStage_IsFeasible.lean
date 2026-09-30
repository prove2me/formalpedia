-- Prove2me | Definitions.Def_JohnsonFlowShop_TwoStage_IsFeasible
-- name    : JohnsonFlowShop_TwoStage_IsFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:35:13.068404+00:00
-- url     : https://prove2.me/theorems/7afe0506-e791-4c4b-8547-2ee0b7fcf2ed
-- title:
--   Feasible two-machine schedule (p. 61)
-- statement:
--   There are $n$ items, each of which must be processed first on machine 1 and then on machine 2; there is one machine per stage and at most one item can be on a machine at a given time. Item $i$ takes time $A_i$ on machine 1 and $B_i$ on machine 2 (setup time plus work time).
--
--   A **schedule** is given by start times $s^1_i$ (machine 1) and $s^2_i$ (machine 2) for every item $i$; item $i$ occupies machine 1 during $[s^1_i, s^1_i + A_i]$ and machine 2 during $[s^2_i, s^2_i + B_i]$. The schedule is **feasible** when
--
--   1. $s^1_i \ge 0$ for every item $i$ (time starts at $0$);
--   2. for distinct items $i \ne j$, $s^1_i + A_i \le s^1_j$ or $s^1_j + A_j \le s^1_i$ (machine 1 handles one item at a time);
--   3. for distinct items $i \ne j$, $s^2_i + B_i \le s^2_j$ or $s^2_j + B_j \le s^2_i$ (machine 2 handles one item at a time);
--   4. $s^1_i + A_i \le s^2_i$ for every item $i$ (an item starts on machine 2 only after it has finished on machine 1).
--
--   This is the feasible set of Bellman's two-stage problem as quoted by Johnson; every optimality statement of the mission ranges over it.
--
--   **Formalization Note** Items are `Fin n`, times are real numbers, and processing is non-preemptive. Positivity of the processing times is not part of this definition; it is a hypothesis of each theorem. The two machines' orders are not required to coincide.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 61, Two-stage production schedule (Bellman's formulation) and p. 62, proof of Lemma 1 ("the start of a B_j must be to the right of the end of an A_j")

import Mathlib

namespace JohnsonFlowShop.TwoStage

/-- A two-machine schedule of `n` items, given by the start times `s₁ i` of item `i` on
machine 1 and `s₂ i` on machine 2, is feasible for processing times `A` (machine 1) and
`B` (machine 2) when: no item starts before time `0`; each machine processes at most one
item at a time (the processing intervals of two distinct items on the same machine do not
overlap); and every item finishes on machine 1 before it starts on machine 2.
Processing is non-preemptive: item `i` occupies machine 1 on `[s₁ i, s₁ i + A i]` and
machine 2 on `[s₂ i, s₂ i + B i]`. -/
def IsFeasible {n : ℕ} (A B : Fin n → ℝ) (s₁ s₂ : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ s₁ i) ∧
  (∀ i j, i ≠ j → s₁ i + A i ≤ s₁ j ∨ s₁ j + A j ≤ s₁ i) ∧
  (∀ i j, i ≠ j → s₂ i + B i ≤ s₂ j ∨ s₂ j + B j ≤ s₂ i) ∧
  (∀ i, s₁ i + A i ≤ s₂ i)

end JohnsonFlowShop.TwoStage



-- Prove2me | Definitions.Def_JohnsonFlowShop_ThreeStage_IsFeasible
-- name    : JohnsonFlowShop_ThreeStage_IsFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:40:15.794891+00:00
-- url     : https://prove2.me/theorems/ee3cbcea-89c0-489e-bed3-e4f7770fd65f
-- title:
--   Feasible three-machine schedule (pp. 61, 65)
-- statement:
--   There are $n$ items, each of which must be processed first on machine 1, then on machine 2, then on machine 3; there is one machine per stage and at most one item can be on a machine at a given time. Item $i$ takes time $A_i$ on machine 1, $B_i$ on machine 2 and $C_i$ on machine 3 (setup time plus work time).
--
--   A **schedule** is given by start times $s^1_i$, $s^2_i$, $s^3_i$ of every item $i$ on the three machines; item $i$ occupies machine 1 during $[s^1_i, s^1_i + A_i]$, machine 2 during $[s^2_i, s^2_i + B_i]$ and machine 3 during $[s^3_i, s^3_i + C_i]$. The schedule is **feasible** when
--
--   1. $s^1_i \ge 0$ for every item $i$ (time starts at $0$);
--   2. for distinct items $i \ne j$, $s^1_i + A_i \le s^1_j$ or $s^1_j + A_j \le s^1_i$ (machine 1 handles one item at a time);
--   3. the same non-overlap condition holds on machine 2 with the times $B$;
--   4. the same non-overlap condition holds on machine 3 with the times $C$;
--   5. $s^1_i + A_i \le s^2_i$ and $s^2_i + B_i \le s^3_i$ for every item $i$ (an item enters a machine only after it has left the previous one).
--
--   This is the feasible set of Johnson's three-stage problem; every optimality statement of the mission ranges over it. The three machines may process the items in different orders.
--
--   **Formalization Note** Items are `Fin n`, times are real numbers, and processing is non-preemptive. Positivity of the processing times is not part of this definition; it is a hypothesis of each theorem.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 61, Two-stage production schedule (Bellman's formulation), and p. 65, Three-stage production schedule ("at most one item at a time on each machine") and Notation

import Mathlib

namespace JohnsonFlowShop.ThreeStage

/-- A three-machine schedule of `n` items, given by the start times `s₁ i`, `s₂ i`, `s₃ i` of
item `i` on machines 1, 2, 3, is feasible for processing times `A` (machine 1), `B` (machine 2)
and `C` (machine 3) when: no item starts before time `0`; each machine processes at most one
item at a time (the processing intervals of two distinct items on the same machine do not
overlap); and every item finishes on machine 1 before it starts on machine 2, and finishes on
machine 2 before it starts on machine 3. Processing is non-preemptive: item `i` occupies
machine 1 on `[s₁ i, s₁ i + A i]`, machine 2 on `[s₂ i, s₂ i + B i]` and machine 3 on
`[s₃ i, s₃ i + C i]`. The order of the items may differ from machine to machine. -/
def IsFeasible {n : ℕ} (A B C : Fin n → ℝ) (s₁ s₂ s₃ : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ s₁ i) ∧
  (∀ i j, i ≠ j → s₁ i + A i ≤ s₁ j ∨ s₁ j + A j ≤ s₁ i) ∧
  (∀ i j, i ≠ j → s₂ i + B i ≤ s₂ j ∨ s₂ j + B j ≤ s₂ i) ∧
  (∀ i j, i ≠ j → s₃ i + C i ≤ s₃ j ∨ s₃ j + C j ≤ s₃ i) ∧
  (∀ i, s₁ i + A i ≤ s₂ i) ∧
  (∀ i, s₂ i + B i ≤ s₃ i)

end JohnsonFlowShop.ThreeStage



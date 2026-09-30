-- Prove2me | Definitions.Def_AlgMechDesign_MinWork_Mechanism
-- name    : AlgMechDesign_MinWork_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:11:10.010789+00:00
-- url     : https://prove2.me/theorems/e64a4e94-30fb-4bcb-b05d-8a8562f958f7
-- title:
--   The MinWork mechanism: minimal-time allocation and second-best payments
-- statement:
--   This file defines the MinWork mechanism of Nisan and Ronen (Definition 11) for $n$ agents and $k$ tasks.
--
--   1. **Allocation.** An allocation rule $x(\cdot)$ is a **MinWork allocation** if, for every declared type vector $t$ and every task $j$, the agent $x_j(t)$ receiving task $j$ declared a minimal time for it:
--   $$
--   t^{x_j(t)}_j \le t^{i'}_j \quad \text{for every agent } i'.
--   $$
--   Tasks with equal declared times may be allocated arbitrarily; the tie-breaking rule may depend on the whole declared vector.
--   2. **Second-best time.** For $n \ge 2$, the second-best time of task $j$ from agent $i$'s point of view is $\min_{i' \neq i} t^{i'}_j$, the smallest time declared for $j$ by the other agents.
--   3. **Minimal time.** $\min_i t^i_j$, the smallest declared time for task $j$.
--   4. **Payment.** For $n \ge 2$, the MinWork payment handed to agent $i$ is
--   $$
--   p^i(t) = \sum_{j \in x^i(t)} \min_{i' \neq i} t^{i'}_j ,
--   $$
--   so for each task it wins, the agent receives the time of the second-best agent for that task.
--
--   Each task is thus sold in a separate Vickrey (second-price) reverse auction. Theorem 4.1 asserts this mechanism is strongly truthful and an $n$-approximation of the minimal make-span.
--
--   **Formalization Note** The allocation rule is a parameter constrained by `IsMinWorkAlloc`, so every theorem holds for every tie-breaking rule. The minima are `Finset.inf'` over nonempty sets: the other agents (nonempty because $n \ge 2$, proof passed as an argument) and all agents (`[NeZero n]`). Payments are computed from the declarations, never from true types.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 176, Definition 11 (MinWork Mechanism)

import Mathlib
import Definitions.Def_AlgMechDesign_MinWork_Model

namespace AlgMechDesign.MinWork

open Finset

/-- The MinWork allocation specification (Def. 11): every task goes to an agent whose declared
time for it is minimal. Ties may be broken in any way, possibly depending on the whole
declaration profile. -/
def IsMinWorkAlloc {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) : Prop :=
  ∀ (t : Fin n → Fin k → ℝ) (j : Fin k) (i' : Fin n), t (alloc t j) j ≤ t i' j

/-- With at least two agents, the set of agents other than `i` is nonempty. -/
theorem erase_nonempty {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : (univ.erase i).Nonempty :=
  Finset.card_pos.mp (by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega)

/-- The second-best time for task `j` from agent `i`'s point of view: `min_{i' ≠ i} t^{i'}_j`,
a minimum over the nonempty set of the other agents (needs `2 ≤ n`). -/
noncomputable def secondBest {n k : ℕ} (hn : 2 ≤ n) (t : Fin n → Fin k → ℝ) (i : Fin n)
    (j : Fin k) : ℝ :=
  (univ.erase i).inf' (erase_nonempty hn i) (fun i' => t i' j)

/-- The minimal declared time for task `j`, `minᵢ tⁱ_j`. -/
noncomputable def minTime {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (j : Fin k) : ℝ :=
  univ.inf' univ_nonempty (fun i => t i j)

/-- The MinWork payment (Def. 11): `pⁱ(t) = ∑_{j ∈ xⁱ(t)} min_{i' ≠ i} t^{i'}_j`, computed from
the declarations `t`, handed to agent `i`. -/
noncomputable def minWorkPay {n k : ℕ} (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (t : Fin n → Fin k → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => alloc t j = i), secondBest hn t i j

end AlgMechDesign.MinWork



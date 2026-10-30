-- Prove2me | Definitions.Def_NisanRonen_Rounding_load
-- name    : NisanRonen_Rounding_load
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:15:03.05502+00:00
-- url     : https://prove2.me/theorems/0513745f-ffe8-4fb2-97f2-d9552e29ac38
-- title:
--   Load of an agent under an allocation
-- statement:
--   There are $n$ agents and $k$ tasks. An **allocation** assigns every task $j$ to one agent $x(j)$; equivalently it is a partition $x = (x^1, \dots, x^n)$ of the tasks, with $x^i = \{j : x(j) = i\}$. For a vector $\tau = (\tau_1, \dots, \tau_k)$ of times, the **load** of agent $i$ is
--
--   $$
--   \mathrm{load}_i(x, \tau) = \sum_{j \in x^i} \tau_j .
--   $$
--
--   This is the inner sum of the make-span $g(x, \tilde t) = \max_i \sum_{j \in x^i} \tilde t_j$ and of the valuation $v^i(x, \tilde t) = -\sum_{j \in x^i} \tilde t_j$ in the task scheduling problem with verification.
--
--   **Formalization Note** Agents are `Fin n`, tasks `Fin k`, an allocation is a function `Fin k → Fin n`.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 20, p. 187 (PDF p. 22)

import Mathlib

namespace NisanRonen.Rounding

/-- **Load of an agent** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 20, p. 187: the inner sum
`Σ_{j ∈ x^i} t̃_j` of the make-span and of the valuation `v^i(x, t̃) = −Σ_{j ∈ x^i} t̃_j`).
For an allocation `x : Fin k → Fin n` (task `j` goes to agent `x j`, so `x^i = {j | x j = i}`)
and a time vector `τ : Fin k → ℝ`, `load x τ i = Σ_{j : x j = i} τ j`.

**Formalization Note** Agents are `Fin n` and tasks `Fin k` (0-based). An allocation is a
function from tasks to agents, i.e. a partition `x = (x¹, …, xⁿ)` of the tasks (Def. 10, p. 175). -/
def load {n k : ℕ} (x : Fin k → Fin n) (τ : Fin k → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => x j = i), τ j

end NisanRonen.Rounding



-- Prove2me | Definitions.Def_AlgMechDesign_CompBonus_Mechanism
-- name    : AlgMechDesign_CompBonus_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:58:01.255863+00:00
-- url     : https://prove2.me/theorems/c1a70e34-aabd-455f-8da9-c028987ae825
-- title:
--   The Compensation-and-Bonus payments
-- statement:
--   This file defines the payment functions of the Compensation-and-Bonus mechanism of Nisan and Ronen (Definitions 21, 23, 24).
--
--   Let $x(\cdot)$ be an allocation algorithm, $d$ the declared type vector and $\tilde t$ the vector of actual times in which the tasks were performed. The **compensation** of agent $i$ reimburses the actual time it spent on its tasks, and the **bonus** is minus the make-span of the allocation when agent $i$'s tasks are counted at their actual times and every other task at the time declared by its agent:
--   $$
--   c^i(d,\tilde t) = \sum_{j\in x^i(d)} \tilde t_j, \qquad b^i(d,\tilde t) = -g\big(x(d), \mathrm{corr}^i(x(d), d, \tilde t)\big),
--   $$
--   where $\mathrm{corr}^i(x, d, \tilde t)_j$ equals $\tilde t_j$ for $j \in x^i$ and $d^l_j$ for $j \in x^l$, $l \ne i$. The Compensation-and-Bonus payment is
--   $$
--   p^i(d, \tilde t) = c^i(d,\tilde t) + b^i(d,\tilde t),
--   $$
--   and the **Compensation-and-Bonus mechanism** is the mechanism with verification $(x, p)$ whose allocation algorithm $x$ is optimal.
--
--   The bonus depends on the other agents only through their declarations, never through their actual execution times; this is what makes the mechanism analysable agent by agent.
--
--   **Formalization Note** `cbPay alloc` is defined for every allocation rule `alloc`; the requirement that `alloc` be optimal is the separate hypothesis `IsOptimalAlloc alloc` in the theorems.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 187–188, Definitions 21, 22, 23, 24

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model

namespace AlgMechDesign.CompBonus

open Finset

/-- The compensation of agent `i` (Def. 21): `cⁱ(d, t̃) = ∑_{j ∈ xⁱ(d)} t̃_j`, where `x = alloc`
is the allocation algorithm, `d` the declarations and `t̃ = tt` the actual times. -/
def compensation {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => alloc d j = i), tt j

/-- The bonus of agent `i` (Def. 23): `bⁱ(d, t̃) = -g(x(d), corrⁱ(x(d), d, t̃))`, computed from
the declarations of the other agents and the actual times of agent `i`'s own tasks. -/
noncomputable def bonus {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  -gT (alloc d) (corr i (alloc d) d tt)

/-- The Compensation-and-Bonus payment based on the allocation algorithm `alloc` (Def. 24):
`pⁱ(d, t̃) = cⁱ(d, t̃) + bⁱ(d, t̃)`, the amount handed to agent `i`. The Compensation-and-Bonus
mechanism is the pair `(alloc, cbPay alloc)` with `alloc` an optimal allocation algorithm. -/
noncomputable def cbPay {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  compensation alloc d tt i + bonus alloc d tt i

end AlgMechDesign.CompBonus



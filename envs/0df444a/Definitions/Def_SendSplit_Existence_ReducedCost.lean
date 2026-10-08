-- Prove2me | Definitions.Def_SendSplit_Existence_ReducedCost
-- name    : SendSplit_Existence_ReducedCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:12:23.057163+00:00
-- url     : https://prove2.me/theorems/c67e84ba-458d-4f87-a6fa-8e8a34dbca37
-- title:
--   Section 2 — altered arc costs $c^\pi_{ij}(y) = c_{ij}(y) - (\pi_i - \pi_j)y$ and altered flow cost $c^\pi$
-- statement:
--   Let $\pi = (\pi_i) \in \mathbb{R}^n$ be a vector of node numbers (potentials). The **altered arc costs** and **altered flow cost** are
--
--   $$c^\pi_{ij}(y) = c_{ij}(y) - (\pi_i - \pi_j)\,y, \qquad c^\pi(x) = \sum_{(i,j)\in A} c^\pi_{ij}(x_{ij}).$$
--
--   Condition 7° of Theorem 1 asks for a $\pi$ making every altered arc cost nonnegative on flows, which reduces the problem to one with nonnegative arc costs.
--
--   **Formalization Note** The paper writes $\sum_{i,j}$; the cost functions are only given on arcs, so the sum is over $A$.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, Section 2

import Mathlib
import Definitions.Def_SendSplit_Existence_Network

namespace SendSplit.Existence

variable {n : ℕ}

/-- The altered arc cost `c^π_ij(y) = c_ij(y) - (π_i - π_j) y` for a node vector `π ∈ ℝ^n`. -/
def reducedArcCost (c : Fin n → Fin n → ℝ → ℝ) (π : Fin n → ℝ) (i j : Fin n) (y : ℝ) : ℝ :=
  c i j y - (π i - π j) * y

/-- The altered flow cost `c^π(x) = ∑_{(i,j) ∈ A} c^π_ij(x_ij)`. -/
def reducedFlowCost (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (π : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) : ℝ :=
  ∑ p ∈ G.A, reducedArcCost c π p.1 p.2 (x p.1 p.2)

end SendSplit.Existence



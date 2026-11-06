-- Prove2me | Definitions.Def_CoverModular_IsOptimal
-- name    : CoverModular_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:36.738788+00:00
-- url     : https://prove2.me/theorems/6961bf58-0f25-4bf3-86d7-fc4b9bba275c
-- title:
--   Optimal solution $x^{\mathcal S}$ of the second-stage LP
-- statement:
--   A flow $x$ is an **optimal solution** of the second-stage LP (3) for the structure $\mathcal A$ (with capacities $c$, demands $d$ and profits $p$) if $x$ is feasible for (3) and $\sum_{i,j}p_{ij}x_{ij}\ge\sum_{i,j}p_{ij}y_{ij}$ for every feasible $y$.
--
--   The paper writes $x^{\mathcal S}$ for an optimal solution of (3) with $\mathcal A=\mathcal S$; it is the input of the primal-derived dual values (6).
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.1, p.11 (definition of $x^{\mathcal S}_{ij}$ before (6))

import Mathlib
import Definitions.Def_CoverModular_lpValue

open BipartiteMatchingHT.Delay

namespace CoverModular

variable {I J : Type} [Fintype I] [Fintype J]

/-- `x` is an optimal solution of the second-stage LP (3) for the structure `A`
(DeValve, Pekeč, Wei, SSRN 3844987, §3.1, p.11: "let `x^𝒮_ij` denote the value of variable
`x_ij` in an optimal solution to the LP in (3) with `𝒜 = 𝒮`"): `x` is feasible for (3) and its
profit is at least that of every feasible flow. -/
def IsOptimal (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ) (A : Finset (I × J))
    (x : I → J → ℝ) : Prop :=
  (network c d A).Feasible x ∧ ∀ y, (network c d A).Feasible y → profit p y ≤ profit p x

end CoverModular



-- Prove2me | Definitions.Def_CoverModular_IsDualFeasible
-- name    : CoverModular_IsDualFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:34.325662+00:00
-- url     : https://prove2.me/theorems/cc94064f-adeb-4f85-a4c4-cc8b8a0a28bf
-- title:
--   Feasibility for the dual (4) of the second-stage LP
-- statement:
--   For a structure $\mathcal A$ and profits $p$, a pair $(\alpha,\beta)$ with $\alpha\in\mathbb R^I$, $\beta\in\mathbb R^J$ is **feasible for the dual (4)**
--
--   $$
--   \min_{\alpha,\beta}\ \sum_i c_i\alpha_i+\sum_j d_j\beta_j\quad\text{s.t.}\quad \alpha_i+\beta_j\ge p_{ij}\ \ ((i,j)\in\mathcal A),\qquad \alpha_i,\beta_j\ge0\ \ \forall i,j,
--   $$
--
--   if it satisfies its constraints: $\alpha_i+\beta_j\ge p_{ij}$ for every arc $(i,j)\in\mathcal A$, and $\alpha_i\ge0$, $\beta_j\ge0$ for all $i,j$. The dual objective is written out in the theorems that use it.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.1, display (4), p.10

import Mathlib

namespace CoverModular

variable {I J : Type}

/-- Dual feasibility for the dual (4) of the second-stage LP (DeValve, Pekeč, Wei,
SSRN 3844987, §3.1, display (4), p.10): `(α, β)` is feasible for
`min ∑_i c_i α_i + ∑_j d_j β_j` s.t. `α_i + β_j ≥ p_ij` for `(i, j) ∈ A`, `α_i, β_j ≥ 0`.
The dual objective does not enter feasibility and is written out where it is used. -/
def IsDualFeasible (p : I → J → ℝ) (A : Finset (I × J)) (α : I → ℝ) (β : J → ℝ) : Prop :=
  (∀ i j, (i, j) ∈ A → p i j ≤ α i + β j) ∧ (∀ i, 0 ≤ α i) ∧ ∀ j, 0 ≤ β j

end CoverModular



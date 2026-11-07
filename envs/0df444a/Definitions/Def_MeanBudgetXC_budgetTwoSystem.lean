-- Prove2me | Definitions.Def_MeanBudgetXC_budgetTwoSystem
-- name    : MeanBudgetXC_budgetTwoSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:24.023067+00:00
-- url     : https://prove2.me/theorems/314904e6-7851-4ebc-8d49-d66a5d90ad54
-- title:
--   The quadratic formulation of Section 3.5
-- statement:
--   With $r=d-1$, the **quadratic formulation** is the following system in the pair array $q$ and the auxiliary variables $p,\tau,z,u,v,w,\lambda,\mu$.
--
--   The first group imposes the star and budget conditions:
--   $$q_{ij}\ge0,\quad \tau_i\ge0,\quad z_{ij}\ge0,\quad z_{ij}\ge q_{ij}-\tau_i\ (i\ne j),\quad r\tau_i+\sum_{j\ne i}z_{ij}\le p_i\le\sum_{j\ne i}q_{ij},\quad \sum_i p_i\le B.$$
--
--   The second group is the dual certificate:
--   $$u_i\ge0,\quad v_{ij}\ge0\ (i\ne j),\quad w_{ij}\ge0\ (i<j),$$
--   $$u_i-\sum_{j\ne i}v_{ij}+\sum_{j\ne i}w_{ij}+\lambda-r\mu_i\ge p_i,$$
--   $$v_{ij}+v_{ji}-w_{ij}+\mu_i+\mu_j\ge-q_{ij}\ (i<j),\qquad \sum_iu_i+\sum_{i<j}w_{ij}+d\lambda\le1.$$
--
--   The system has $(5M+3N+1)+(4M+2N+1)=9M+5N+2$ inequalities in $6M+4N+1$ variables, and no equations.
--
--   **Formalization Note** $q$ and $w$ are indexed by unordered pairs, $z$ and $v$ by ordered pairs, $p,\tau,u,\mu$ by vertices, and $\lambda$ is a scalar. The row $v_{ij}+v_{ji}-w_{ij}+\mu_i+\mu_j\ge-q_{ij}$ is written for every ordered pair; the two orders of one unordered pair give the same inequality, so the solution set is the paper's and the count above stands.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.5, pp.15–16

import Mathlib
import Definitions.Def_MeanBudgetXC_OPair

namespace MeanBudgetXC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **quadratic formulation** of Section 3.5 (pp.15–16), with `r = d − 1`, as a predicate on
the projected coordinates `q` and the auxiliary variables `p, τ, z, u, v, w, λ, μ`. The first group
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, p.15) imposes the star and budget conditions:
`q_ij ≥ 0`, `τ_i ≥ 0`, `z_ij ≥ 0`, `z_ij ≥ q_ij − τ_i` (`i ≠ j`),
`r τ_i + ∑_{j≠i} z_ij ≤ p_i ≤ ∑_{j≠i} q_ij`, `∑_i p_i ≤ B`.
The second group (p.16) is the dual certificate:
`u_i ≥ 0`, `v_ij ≥ 0` (`i ≠ j`), `w_ij ≥ 0` (`i < j`),
`u_i − ∑_{j≠i} v_ij + ∑_{j≠i} w_ij + λ − r μ_i ≥ p_i`,
`v_ij + v_ji − w_ij + μ_i + μ_j ≥ −q_ij` (`i < j`),
`∑_i u_i + ∑_{i<j} w_ij + d λ ≤ 1`.

**Formalization Note** `q` and `w` are indexed by unordered pairs (`Pair V`), `z` and `v` by
ordered pairs (`OPair V`), `p, τ, u, μ` by vertices, and `λ` (written `lam`) is a scalar. The
inequality `v_ij + v_ji − w_ij + μ_i + μ_j ≥ −q_ij` is imposed for every ordered pair; the two
orders of one unordered pair give the same inequality. -/
def budgetTwoSystem (d : ℕ) (B : ℝ) (q : Pair V → ℝ) (p τ u mu : V → ℝ) (z v : OPair V → ℝ)
    (w : Pair V → ℝ) (lam : ℝ) : Prop :=
  -- first group (p.15)
  (∀ e, 0 ≤ q e) ∧ (∀ i, 0 ≤ τ i) ∧ (∀ o, 0 ≤ z o) ∧ (∀ o : OPair V, q o.toPair - τ o.1.1 ≤ z o) ∧
  (∀ i, ((d : ℝ) - 1) * τ i + ∑ o ∈ Finset.univ.filter (fun o : OPair V => o.1.1 = i), z o ≤ p i) ∧
  (∀ i, p i ≤ ∑ o ∈ Finset.univ.filter (fun o : OPair V => o.1.1 = i), q o.toPair) ∧
  ∑ i, p i ≤ B ∧
  -- second group (p.16)
  (∀ i, 0 ≤ u i) ∧ (∀ o, 0 ≤ v o) ∧ (∀ e, 0 ≤ w e) ∧
  (∀ i, p i ≤ u i - ∑ o ∈ Finset.univ.filter (fun o : OPair V => o.1.1 = i), v o
      + ∑ o ∈ Finset.univ.filter (fun o : OPair V => o.1.1 = i), w o.toPair
      + lam - ((d : ℝ) - 1) * mu i) ∧
  (∀ o : OPair V, -q o.toPair ≤ v o + v o.swap - w o.toPair + mu o.1.1 + mu o.1.2) ∧
  ∑ i, u i + ∑ e, w e + (d : ℝ) * lam ≤ 1

end MeanBudgetXC



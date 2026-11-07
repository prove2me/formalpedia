-- Prove2me | Definitions.Def_SteurerHDX_downUp
-- name    : SteurerHDX_downUp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:50.351192+00:00
-- url     : https://prove2.me/theorems/b4222e7c-9601-4d96-bb81-dc362929d9f5
-- title:
--   The down-up walk $P_d^\vee$ on the facets
-- statement:
--   For a $d$-dimensional complex $\mathcal X$, the **down-up walk** on $\mathcal X(d)$ moves from a facet $\tau$ as follows: choose a vertex $v\in\tau$ uniformly at random, then move to a uniformly random facet $\sigma\supseteq\tau\setminus\{v\}$. Its transition matrix is
--   $$P_d^\vee(\tau,\sigma)=\frac1d\sum_{v\in\tau}\frac{\mathbf 1[\tau\setminus\{v\}\subseteq\sigma]}{|\{\rho\in\mathcal X(d):\tau\setminus\{v\}\subseteq\rho\}|}.$$
--   For a pure complex it is symmetric and stochastic, so its stationary distribution is uniform on the facets.
--
--   **Formalization Note** All walk quantities of the down-up walk (stationary distribution, Dirichlet form, variance, $\lambda_2$) are taken with weight matrix $W=P_d^\vee$ itself (row sums $1$).
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.2, p.4

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace SteurerHDX

/-- **The down-up walk P_d^∨.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.2, p.4: "Given a d-dimensional complex X and
a facet τ ∈ X(d), one can run a Markov chain called the down-up walk on X(d): suppose we are
currently at τ; we choose a vertex v ∈ τ uniformly at random, and among all facets σ ⊇ τ \ {v}
we move to one uniformly at random."

**Formalization Note.** P_d^∨(τ, σ) = (1/d) ∑_{v ∈ τ} [τ \ {v} ⊆ σ] / |{ρ ∈ X(d) : τ \ {v} ⊆ ρ}|,
indexed by the facets `faces X d`. The denominator is ≥ 1 since τ itself is counted. For a pure
complex this matrix is symmetric with row sums 1, so its stationary distribution is uniform and
the walk quantities (`statDist`, `walk`, the Dirichlet form, `variance`, `lambdaTwo`) are taken with
W = P_d^∨. -/
noncomputable def downUp {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) :
    Matrix (faces X d) (faces X d) ℝ :=
  Matrix.of fun τ σ => (1 / (d : ℝ)) * ∑ v ∈ τ.1,
    if τ.1.erase v ⊆ σ.1 then
      1 / (((faces X d).filter (fun ρ => τ.1.erase v ⊆ ρ)).card : ℝ)
    else 0

end SteurerHDX



-- Prove2me | Definitions.Def_RobustFracMP_assignCost
-- name    : RobustFracMP_assignCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:49.495407+00:00
-- url     : https://prove2.me/theorems/bde11a14-27b9-4366-aeca-940046acc04b
-- title:
--   Assignment cost $\sigma_z(x)$ of a fractional assignment
-- statement:
--   Let $(P,\mathrm{dist})$ be a finite metric space and $z\ge 1$ an integer. A **fractional assignment** is a vector $x=(x_{p,q})_{p,q\in P}$, where $x_{p,q}$ is the amount by which the point $p$ is assigned to the candidate center $q$ (the candidate centers are the data points themselves, $F=P$). Its **assignment cost** is
--
--   $$\sigma_z(x)=\sum_{p\in P}\sum_{q\in P}x_{p,q}\cdot\mathrm{dist}^z(p,q).$$
--
--   The assignment cost is the objective that the clustering cost of a fractional center set minimizes, and it is the intermediate quantity of every bound in Section 3.
--
--   **Formalization Note** The function takes any real matrix $x$; nonnegativity of $x$ is part of feasibility, not of this formula.
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Section 2, Fractional Solution to Clustering, p.10 (PDF p.12)

import Mathlib

set_option autoImplicit false

namespace RobustFracMP

/-- **Assignment cost σ_z(x) of a fractional assignment.**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering:
Constant Approximation in Constant Rounds*, arXiv:2604.00954 (version of November 3, 2026;
manuscript sha256 c65896fe6f32051527c00d1bcd269746784374658ddefb707cff5f35bd3551d8), Section 2, "Fractional Solution to Clustering", p.10 (PDF p.12):
"The assignment cost of x is defined as σ_z(P, x) := Σ_{p∈P} Σ_{q∈F} x_{p,q} · dist^z(p, q)."

**Formalization Note.** The paper's candidate center set is `F = P` throughout Section 3 (p.11), so
an assignment is `x : P → P → ℝ`, with `x p q` the amount by which `p` is assigned to `q`.
`dist p q ^ z` is the power-`z` distance `dist^z(p, q)` with `z : ℕ`. Nonnegativity of `x` is part
of feasibility (`Feasible`), not of this formula. -/
def assignCost {P : Type*} [Fintype P] [MetricSpace P] (z : ℕ) (x : P → P → ℝ) : ℝ :=
  ∑ p, ∑ q, x p q * dist p q ^ z

end RobustFracMP



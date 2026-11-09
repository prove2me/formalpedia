-- Prove2me | Definitions.Def_RobustFracMP_Feasible
-- name    : RobustFracMP_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:49.000961+00:00
-- url     : https://prove2.me/theorems/4dafd2a7-4507-480d-bcaf-201cad794741
-- title:
--   Feasibility $x\sim y$ of a fractional assignment
-- statement:
--   For a finite set $P$, a fractional assignment $x=(x_{p,q})_{p,q\in P}$ and a fractional center set $y=(y_q)_{q\in P}$, the assignment is **feasible** for $y$, written $x\sim y$, when
--
--   1. $x_{p,q}\ge 0$ for all $p,q\in P$ ($x$ is a fractional assignment, $x\in\mathbb R^{P\times P}_{\ge 0}$);
--   2. (C1) $\sum_{q\in P}x_{p,q}\ge 1$ for every $p\in P$: each point is assigned to at least one unit of centers;
--   3. (C2) $x_{p,q}\le y_q$ for all $p,q\in P$: no point is assigned to $q$ more than the opening of $q$.
--
--   These are the constraints (L1)–(L3) of the facility-location linear program, so feasibility links the clustering cost to linear-programming duality.
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Section 2, constraints (C1)–(C2), pp.10–11 (PDF pp.12–13)

import Mathlib

set_option autoImplicit false

namespace RobustFracMP

/-- **Feasibility x ∼ y of a fractional assignment for a fractional center set.**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering:
Constant Approximation in Constant Rounds*, arXiv:2604.00954 (version of November 3, 2026;
manuscript sha256 c65896fe6f32051527c00d1bcd269746784374658ddefb707cff5f35bd3551d8), Section 2, p.10–11 (PDF pp.12–13): a fractional assignment is
`x = (x_{p,q}) ∈ ℝ^{P×F}_{≥0}`, and `x ∼ y` when
"(C1) ∀p ∈ P, Σ_{q∈F} x_{p,q} ≥ 1" and "(C2) ∀p ∈ P, q ∈ F, x_{p,q} ≤ y_q".

**Formalization Note.** `F = P` (p.11). The nonnegativity `x ∈ ℝ^{P×P}_{≥0}` of the paper's
definition of a fractional assignment is the first conjunct. -/
def Feasible {P : Type*} [Fintype P] (x : P → P → ℝ) (y : P → ℝ) : Prop :=
  (∀ p q, 0 ≤ x p q) ∧ (∀ p, 1 ≤ ∑ q, x p q) ∧ ∀ p q, x p q ≤ y q

end RobustFracMP



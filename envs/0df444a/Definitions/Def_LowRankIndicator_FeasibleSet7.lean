-- Prove2me | Definitions.Def_LowRankIndicator_FeasibleSet7
-- name    : LowRankIndicator_FeasibleSet7
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:52.257273+00:00
-- url     : https://prove2.me/theorems/6b757cda-5808-487e-a02d-562f9e31b5d4
-- title:
--   The feasible region of the linear program (7)
-- statement:
--   Let $A$ be a $k\times n$ real matrix and $\bar x\in\mathbb R^n$. The feasible region of the linear program (7) in the proof of the main theorem is
--
--   $$\{x\in\mathbb R^n: Ax=A\bar x,\quad \bar x_ix_i\ge0\ \ \forall i\in\operatorname{supp}(\bar x),\quad x_i=0\ \ \forall i\in[n]\setminus\operatorname{supp}(\bar x)\}.$$
--
--   It contains $\bar x$, and every feasible point has its support inside $\operatorname{supp}(\bar x)$ with the signs of $\bar x$ there. So it is a polyhedron contained in one orthant.
--
--   **Formalization Note** The paper takes $\bar x$ from a point $(\bar t,\bar x,\bar z)$ of $Q$; the definition takes any vector. The objective of (7) is not part of the definition.
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, proof of Theorem 1, (7), p.7.

import Mathlib

namespace LowRankIndicator

/-- The feasible region of the linear program (7) of Han & Gómez, *Compact Extended Formulations
for Low-Rank Functions with Indicator Variables*, arXiv:2110.14884v2, proof of Theorem 1, p.7:
`{x ∈ ℝⁿ : Ax = Ax̄, x̄ᵢxᵢ ≥ 0 ∀i ∈ supp(x̄), xᵢ = 0 ∀i ∈ [n] \ supp(x̄)}`.

**Formalization Note.** `xbar` is an arbitrary vector here; the proof takes it from a point of `Q`.
The objective of (7) is not part of this definition. -/
def feas7 {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (xbar : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | A.mulVec x = A.mulVec xbar ∧ (∀ i, xbar i ≠ 0 → 0 ≤ xbar i * x i) ∧
    ∀ i, xbar i = 0 → x i = 0}

end LowRankIndicator



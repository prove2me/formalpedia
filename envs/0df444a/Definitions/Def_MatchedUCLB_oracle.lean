-- Prove2me | Definitions.Def_MatchedUCLB_oracle
-- name    : MatchedUCLB_oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:09.177198+00:00
-- url     : https://prove2.me/theorems/d90d5708-aaed-4fd8-a82f-3fc87f713bb2
-- title:
--   The $p$th-order oracle $x\mapsto(F(x),\nabla F(x),\dots,\nabla^pF(x))$
-- statement:
--   For $F:\mathbb R^d\to\mathbb R$ and $x\in\mathbb R^d$, the **$p$th-order oracle** returns
--
--   $$
--   \bigl(F(x),\,\nabla F(x),\,\nabla^2F(x),\,\dots,\,\nabla^pF(x)\bigr),
--   $$
--
--   the value and all derivative tensors of $F$ at $x$ up to order $p$ (with $\nabla^0F:=F$).
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, with the Euclidean inner product and norm. The $k$th entry is `iteratedFDeriv ℝ k F x`; for $k=0$ it is the constant form with value $F(x)$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition B.1, p.17; Notation, Sec. 3, p.4

import Mathlib
import Definitions.Def_MatchedUCLB_OracleOut

namespace MatchedUCLB

/-- **The pth-order oracle.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition B.1, p.17: "An oracle call at `x` returns the
oracle output `(F(x), ∇F(x), …, ∇^pF(x))`"; Notation, Sec. 3, p.4: "We set `∇^0F := F`".

`oracle p F x` is the family `k ↦ ∇^kF(x)`, `0 ≤ k ≤ p`.

**Formalization Note.** `∇^kF(x)` is `iteratedFDeriv ℝ k F x`. For `k = 0` it is the constant
`0`-linear form with value `F x` (`iteratedFDeriv_zero_apply`), so the oracle returns the value; for
`k = 1` it is `fderiv ℝ F x`, i.e. `v ↦ ⟨∇F(x), v⟩`. -/
noncomputable def oracle {d : ℕ} (p : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : OracleOut d p :=
  fun k => iteratedFDeriv ℝ k F x

end MatchedUCLB



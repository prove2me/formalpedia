-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_DiscreteConvexUnivariate
-- name    : DiscreteConvex_MConvexFunctionsB_DiscreteConvexUnivariate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:10.470984+00:00
-- url     : https://prove2.me/theorems/7dc1a039-82f8-498d-be6d-a6563b74ce09
-- title:
--   DiscreteConvexUnivariate
-- statement:
--   A univariate function $\psi : \mathbb Z \to \mathbb R \cup \{+\infty\}$ is **discrete convex** (the book's $\psi \in C[\mathbb Z \to \mathbb R]$): nonempty effective domain and $\psi(x)+\psi(x+2) \ge 2\psi(x+1)$ for all $x$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, citing Eq. (3.68).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, citing Eq. (3.68)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, citing Eq. (3.68), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- A univariate function `ψ : Z → R ∪ {+∞}` is **discrete convex** (the book's `ψ ∈ C[Z→R]`):
nonempty effective domain and the discrete midpoint-convexity inequality
`ψ(x)+ψ(x+2) ≥ 2ψ(x+1)`. -/
def DiscreteConvexUnivariate (psi : ℤ → WithTop ℝ) : Prop :=
  (∃ x, psi x ≠ ⊤) ∧ ∀ x : ℤ, psi x + psi (x + 2) ≥ psi (x + 1) + psi (x + 1)

end DiscreteConvex.MConvexFunctionsB



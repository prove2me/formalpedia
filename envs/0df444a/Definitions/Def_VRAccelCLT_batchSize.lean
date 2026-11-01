-- Prove2me | Definitions.Def_VRAccelCLT_batchSize
-- name    : VRAccelCLT_batchSize
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:11.105971+00:00
-- url     : https://prove2.me/theorems/a86cdd18-0fb7-47c9-88c5-d3b4b333d40f
-- title:
--   Geometric batch size $N_k=\lceil\rho^{-(k+1)}\rceil$
-- statement:
--   For $\rho\in(0,1)$ the **geometrically increasing batch size** at iteration $k\ge0$ is
--
--   $$
--   N_k=\big\lceil \rho^{-(k+1)}\big\rceil ,
--   $$
--
--   a positive integer that grows like $\rho^{-k}$. Proposition 2, Lemma 7 and Theorem 2 use this choice (with $\rho=\rho_2$ for Algorithm 2).
--
--   **Formalization Note** The ceiling is the natural-number ceiling and the power is the real power $\rho^{-(k+1)}$; for $\rho\in(0,1)$ the argument exceeds $1$, so $N_k\ge 1$.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Lemma 7, p.16; Proposition 2, p.12; Theorem 2, p.19

import Mathlib

namespace VRAccelCLT

/-- **Geometrically increasing batch size** `N_k ≜ ⌈ρ^{−(k+1)}⌉`. Lei, Shanbhag,
arXiv:2006.07769v3, Theorem 1, p.16, Lemma 7, p.16, Proposition 2, p.12 and Theorem 2, p.19
(with `ρ = ρ₁` or `ρ₂`).

**Formalization Note.** The ceiling is `Nat.ceil`, a natural number; for `ρ ∈ (0, 1)` the argument
`ρ^{−(k+1)}` is `> 1`, so `N_k ≥ 1` is a positive integer as the paper requires. The exponent is the
real power `ρ ^ (−(k + 1) : ℝ)`. -/
noncomputable def batchSize (ρ : ℝ) (k : ℕ) : ℕ :=
  ⌈ρ ^ (-((k : ℝ) + 1))⌉₊

end VRAccelCLT



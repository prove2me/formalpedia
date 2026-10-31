-- Prove2me | Definitions.Def_GeomRescale_ell
-- name    : GeomRescale_ell
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:07.747898+00:00
-- url     : https://prove2.me/theorems/69833d10-02d6-44fa-8e07-7d59562a4dba
-- title:
--   The logarithmic factor $\ell$ of the time bound
-- statement:
--   $$\ell = 1 + \max\{0, \log_2(n\Lambda)\}.$$
--
--   This factor replaces the printed $\log(nL_{f,2})$, which is $0$ at $n = 1$, $f(\{v\}) = 1$ and undefined for $f \equiv 0$. For $n\Lambda \ge 2$, $\ell \le 2\log_2(n\Lambda)$.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Theorem 3.6, p.10

import Mathlib

namespace GeomRescale

/-- The logarithmic factor of the corrected time bound of Theorem 3.6 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Theorem 3.6, p.10):
`ℓ := 1 + max {0, log₂(nΛ)}`.

**Formalization Note.** The printed factor `log(nL_{f,2})` is `0` at `n = 1`, `f({v}) = 1`, while
the algorithm evaluates `f(V)`, and it is undefined for `f ≡ 0`. For `nΛ ≥ 2`, `ℓ ≤ 2 log₂(nΛ)`, so
this is the printed factor up to the constant wherever the printed factor is meaningful. -/
noncomputable def ell (n : ℕ) (Λ : ℝ) : ℝ :=
  1 + max 0 (Real.logb 2 ((n : ℝ) * Λ))

end GeomRescale



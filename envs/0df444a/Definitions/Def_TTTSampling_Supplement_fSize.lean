-- Prove2me | Definitions.Def_TTTSampling_Supplement_fSize
-- name    : TTTSampling_Supplement_fSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:59:36.344908+00:00
-- url     : https://prove2.me/theorems/1c3a03c2-5b87-4e0f-b78c-3335e0a85973
-- title:
--   The rate $f(n,S)=\max\{\min\{S,n\},\min\{\sqrt{\log S}/\log^2(2+\log S),\,n^2/\log^2 n\}\}$
-- statement:
--   For natural numbers $n$ and $S$, define
--
--   $$
--   f(n,S) \;:=\; \max\left\{\min\{S,n\},\ \min\left\{\frac{\sqrt{\log S}}{\log^2(2+\log S)},\ \frac{n^2}{\log^2 n}\right\}\right\}.
--   $$
--
--   This is the query rate of the size-sensitive lower bound (Theorem 4.12): sampling from a class of at most $S$ distributions on $\{0,1\}^n$ requires $\Omega(f(n,S))$ queries. For $S$ up to about $\exp(n^2\log^4 n)$ the first term dominates; for larger $S$ the second, which grows like $\sqrt{\log S}$ up to polylogarithmic factors until it saturates at $n^2/\log^2 n$.
--
--   **Formalization Note** $\log$ is the natural logarithm and $n$, $S$ are cast to real numbers. The paper does not fix the base; under the unspecified constant of Theorem 4.12 a change of base alters $f$ by at most a constant factor when $n,S\ge 2$. At $n\le 1$ or $S\le 1$ Lean's conventions $\log 0 = 0$ and $x/0=0$ apply, but Theorem 4.12 only evaluates $f$ at $S\ge 2$ and large $n$.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), §4.4, definition of f, p.47 (PDF p.49)

import Mathlib

namespace TTTSampling

namespace Supplement

/-- **The rate `f(n, S)` of the size-sensitive lower bound.**

Golowich, Moitra, Rohatgi, *The Power of Test-Time Training for Approximate Sampling*,
arXiv:2606.11437 (version of November 3, 2026), §4.4, printed p.47 (PDF p.49): "define the function
f : ℕ × ℕ → ℝ by f(n, S) := max{ min{S, n}, min{ √(log S) / log²(2 + log S), n² / log² n } }".

**Formalization Note**
* `log` is the natural logarithm `Real.log`; `n` and `S` are cast to `ℝ`.
* The paper's base of `log` is not fixed; under the constant `c` of Theorem 4.12 a change of base
  changes `f` by at most a constant factor (for `n, S ≥ 2`).
* At `S ∈ {0, 1}` or `n ∈ {0, 1}` the value uses Lean's `Real.log 0 = 0` and `x / 0 = 0`; Theorem
  4.12 evaluates `f` only at `S ≥ 2` and sufficiently large `n`. -/
noncomputable def fSize (n S : ℕ) : ℝ :=
  max (min (S : ℝ) (n : ℝ))
    (min (Real.sqrt (Real.log (S : ℝ)) / (Real.log (2 + Real.log (S : ℝ))) ^ 2)
      ((n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2))

end Supplement

end TTTSampling



-- Prove2me | Definitions.Def_QWildMatch_polyLog
-- name    : QWildMatch_polyLog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:21.481979+00:00
-- url     : https://prove2.me/theorems/7cfcefa9-2fb1-4cfc-8176-c081db645df7
-- title:
--   The polylogarithmic factor $1+\log(n+2)+\log(1/\delta)$ of $\tilde O$
-- statement:
--   The factor $\mathrm{polyLog}(n,\delta)=1+\log(n+2)+\log(1/\delta)$, with natural logarithms. A bound $\tilde O(X)$ of the paper is read as at most $C\cdot X\cdot\mathrm{polyLog}(n,\delta)^c$ for absolute constants $C$ and $c$ fixed before every instance parameter.
--
--   **Formalization Note** For $\delta\in(0,1)$ both logarithms have arguments above $1$, so the factor is at least $1$. The leading $1$ is not needed for positivity at $n\ge0$; it fixes the base of the power at a value at least $1$, so raising $c$ never lowers the bound.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), eq. (2), p.10

import Mathlib

namespace QWildMatch

/-- The polylogarithmic factor of `Õ` (Zhao et al., STOC 2027 submission, eq. (2), p.10):
`1 + log(n + 2) + log(1/δ)`, with natural logarithms.

**Formalization Note** At `δ ∈ (0, 1)` every logarithm has an argument above `1`, so the value is at
least `1`. The `Õ(X)` of the paper is read as `≤ C · X · polyLog ^ c` with `C` and `c` absolute. -/
noncomputable def polyLog (n : ℕ) (δ : ℝ) : ℝ :=
  1 + Real.log ((n : ℝ) + 2) + Real.log (1 / δ)

end QWildMatch



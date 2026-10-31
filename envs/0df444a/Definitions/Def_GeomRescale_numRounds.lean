-- Prove2me | Definitions.Def_GeomRescale_numRounds
-- name    : GeomRescale_numRounds
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:06.737995+00:00
-- url     : https://prove2.me/theorems/00ce39c8-bbef-4502-bab4-0a3024a235f2
-- title:
--   The number $T$ of outer iterations
-- statement:
--   The paper sets $T = 5n \log(nL_{f,2})$. The formalization computes, from a bound $\Lambda \ge L_{f,2}$,
--
--   $$T = \lceil 5n \log_2(n\Lambda) \rceil_+ ,$$
--
--   where $\lceil \cdot \rceil_+$ is the ceiling in $\mathbb{N}$, so $T = 0$ for $n\Lambda \le 1$.
--
--   **Formalization Note** The page fixes neither the base of the logarithm nor the rounding. The base is $2$ because the proof of Theorem 3.6 needs $(16/9)^{T/n} - 1 > 16x^2$ for $x = n\Lambda$, which holds for $x \ge 4$ with $\log_2$. $\Lambda = L_{f,2}$ is the page's choice, and $\Lambda = \|\alpha\|_2$ is the note under Theorem 3.6.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.2, p.9

import Mathlib

namespace GeomRescale

/-- The number of outer iterations `T = 5n log(nL_{f,2})` of Algorithm Rescaling-SFM
(Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.2, p.9), computed from a bound `Λ ≥ L_{f,2}` as `T := ⌈5n log₂(nΛ)⌉₊`.

**Formalization Note.** The page fixes neither the base of the logarithm nor the rounding, and `T`
must be a natural number. The base is `2`: the proof of Theorem 3.6 needs `(16/9)^{T/n} − 1 > 16x²`
for `x = nΛ`, which holds for `x ≥ 4` with `log₂`, and the proof gives no argument with `ln`. The
parameter `Λ` is the page's `L_{f,2}`, or `‖α‖₂` by the note under Theorem 3.6. `Real.logb 2` is
`0` at `0` and negative on `(0, 1)`, and `⌈·⌉₊` is then `0`: `T = 0` for `nΛ ≤ 1`, and the `for` loop
does not run. -/
noncomputable def numRounds (n : ℕ) (Λ : ℝ) : ℕ :=
  ⌈5 * (n : ℝ) * Real.logb 2 ((n : ℝ) * Λ)⌉₊

end GeomRescale



-- Prove2me | Definitions.Def_SplayDynOpt_loglogFactor
-- name    : SplayDynOpt_loglogFactor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:29.170517+00:00
-- url     : https://prove2.me/theorems/5afb7729-bc5d-4ab4-aa76-d1d3315a7c13
-- title:
--   The factor $L(n)=\max(1,\log_2\log_2 n)\cdot\max(1,\log_2\log_2\log_2 n)^2$
-- statement:
--   For $n\in\mathbb N$ put
--   $$
--   L(n)=\max\bigl(1,\log_2\log_2 n\bigr)\cdot\max\bigl(1,\log_2\log_2\log_2 n\bigr)^2 .
--   $$
--   This is the factor $\log\log n\cdot\log^2\log\log n$ of the main theorem, where $\log^2\log\log n$ means $(\log\log\log n)^2$ and all logarithms are binary.
--
--   For $n\ge 16$ both clamps are inactive and $L(n)$ is the printed expression. For $n<16$ the clamps give the value used in place of a meaningless or vanishing iterated logarithm.
--
--   **Formalization Note** Without the clamps the right-hand side of the main bound would vanish at $n\in\{1,2,4\}$, because Lean's `Real.logb` returns $0$ on these iterated inputs, and the bound would be false there. The verification file proves $L(n)\ge 1$ for all $n$, $L(1)=L(2)=L(4)=1$ and $L(16)=2$.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 1, p.13; footnote 6, p.19 (binary logarithms)

import Mathlib

set_option autoImplicit false

namespace SplayDynOpt

/-- The **competitive factor** `L(n) = max(1, log₂log₂n) · max(1, log₂log₂log₂n)²`, the clamped
form of `log log n · log² log log n`.

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), Theorem 1, p.13: "cost(T, X) = O((cost(T^OPT_X, X) + n) · log log n ·
log² log log n)"; footnote 6, p.19: "All logarithms in this work are binary."

**Formalization Note.** `log² log log n` is read as `(log log log n)²`. The clamps `max 1 ·` only
change `L(n)` for `n < 16`, where `Real.logb` would return `0` or negative junk values (for
example `logb 2 (logb 2 2) = 0`); for `n ≥ 16` both clamps are inactive. A bound
`cost ≤ C·(OPT + n)·L(n)` for all `n ≥ 1` is therefore equivalent to the printed asymptotic
bound (for the finitely many `n < 16` every splay access costs at most `2n` and `OPT ≥ m`). -/
noncomputable def loglogFactor (n : ℕ) : ℝ :=
  max 1 (Real.logb 2 (Real.logb 2 n)) * (max 1 (Real.logb 2 (Real.logb 2 (Real.logb 2 n)))) ^ 2

end SplayDynOpt



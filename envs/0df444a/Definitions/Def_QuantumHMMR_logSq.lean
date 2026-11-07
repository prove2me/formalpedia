-- Prove2me | Definitions.Def_QuantumHMMR_logSq
-- name    : QuantumHMMR_logSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:28.40865+00:00
-- url     : https://prove2.me/theorems/727590c6-6eb5-4b38-83fd-8a79bf3aa104
-- title:
--   $\log^2 x$ to a base $\beta$
-- statement:
--   For a base $\beta > 1$ and $x > 0$, $\log^2 x = (\log_\beta x)^2$. The walk length $T = 3m\lceil \log^2 n \rceil$, the design error $e^{-\kappa_t \log^2 n}$ and the number $O(\log^2 n)$ of queries of Theorem 1.3 are expressed through it.
--
--   **Formalization Note** The paper does not print the base; statements quantify over every base $\beta > 1$.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Eqs. (9), (10), p.12; pp.15–16

import Mathlib

namespace QuantumHMMR

/-- `log² x = (log_β x)²` to the base `β` (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), Eqs. (9), (10), p.12, and pp.15–16, where
`log² n` sets the walk length `T = 3m⌈log² n⌉` and the error `e^{-κ_t log² n}`).

**Formalization Note** The paper does not print the base of the logarithm; statements quantify over
every base `β > 1`, which covers every reading. -/
noncomputable def logSq (β x : ℝ) : ℝ :=
  Real.logb β x ^ 2

end QuantumHMMR



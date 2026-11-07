-- Prove2me | Definitions.Def_PredAdvice_logStar
-- name    : PredAdvice_logStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:18.353247+00:00
-- url     : https://prove2.me/theorems/c7a9508c-41ca-4480-ad78-3b9d55781619
-- title:
--   Iterated logarithm $\log^* n$
-- statement:
--   The **iterated logarithm** $\log^* n$ is the least number $k$ of applications of $\log_2$ that bring $n$ down to at most $1$:
--   $$
--   \log^* n=\min\{k\in\mathbb N : \underbrace{\log_2\cdots\log_2}_{k}\, n\le 1\}.
--   $$
--   So $\log^*1=0$, $\log^*2=1$, $\log^*4=2$, $\log^*16=3$. It appears in the classical lower bound $RS(n)\ge 2^{\Omega(\log^* n)}$.
--
--   **Formalization Note** Before the least such $k$ every iterate exceeds $1$, so the logarithm is only applied to numbers larger than $1$.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.1, p.4

import Mathlib

set_option autoImplicit false

namespace PredAdvice

/-- The iterated logarithm `log* n` (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress
the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.1, p.4, in the
bound `2^{Ω(log* n)} ≤ RS(n)`): the least number `k` of applications of `log₂` that bring `n`
down to at most `1`.

**Formalization Note** `log* n := min {k | (log₂)^[k] n ≤ 1}` with real `log₂ = Real.logb 2`
(all logarithms of the paper are to base two, p.10). Before the first `k` with value `≤ 1` every
iterate is `> 1`, so `Real.logb` is only applied to numbers `> 1` and no junk value enters.
`log* 0 = log* 1 = 0`, `log* 2 = 1`, `log* 4 = 2`, `log* 16 = 3`. -/
noncomputable def logStar (n : ℕ) : ℕ :=
  sInf {k : ℕ | (Real.logb 2)^[k] (n : ℝ) ≤ 1}

end PredAdvice



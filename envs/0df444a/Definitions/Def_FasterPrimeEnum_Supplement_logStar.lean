-- Prove2me | Definitions.Def_FasterPrimeEnum_Supplement_logStar
-- name    : FasterPrimeEnum_Supplement_logStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:46:29.790343+00:00
-- url     : https://prove2.me/theorems/cfe54897-252b-44d8-aa29-6ddee9bf6018
-- title:
--   The iterated natural logarithm $\log^* x$
-- statement:
--   For a real number $x$, the **iterated logarithm** $\log^* x$ is the smallest integer $k\ge 0$ such that
--
--   $$
--   \log^{\circ k} x \le 1,
--   $$
--
--   where $\log^{\circ k}$ is the $k$-fold composition of the natural logarithm. For example $\log^* 1 = 0$ and $\log^* e = 1$.
--
--   It measures the depth of the recursion in Harvey's transform scheme: the bound $K(n)\ll n\cdot 4^{\log^* n}$ of Theorem 4.20.
--
--   **Formalization Note** The logarithm is natural (p.1), so this is not the published base-two `PredAdvice.logStar`. Before the least such $k$ every iterate exceeds $1$, so no junk value of the logarithm is used.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §1.1, p.1

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

/-- **The iterated logarithm `log* x`** — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), §1.1, p.1: "We write log* x for the iterated
logarithm, i.e., log* x is the smallest integer k ⩾ 0 such that log^{∘k} x ⩽ 1, where log^{∘k}
denotes the k-fold composition of log." Here `log` is the natural logarithm (p.1: "We write log x
for the natural logarithm").

**Formalization Note.** `log* x = min {k : ℕ | log^{∘k} x ≤ 1}` with `Real.log`. Before the least
such `k` every iterate exceeds `1`, so `Real.log` is only applied to numbers `> 1` and no junk value
of `Real.log` enters. The set is nonempty for every real `x` (iterating `log` from a number `> 1`
reaches `≤ 1`), so the infimum is attained. `log* 1 = 0`, `log* e = 1`. This is not the published
`PredAdvice.logStar`, which iterates `log₂`. -/
noncomputable def logStar (x : ℝ) : ℕ := sInf {k : ℕ | Real.log^[k] x ≤ 1}

end Supplement

end FasterPrimeEnum



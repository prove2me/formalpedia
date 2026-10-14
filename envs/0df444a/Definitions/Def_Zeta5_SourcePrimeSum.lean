-- Prove2me | Definitions.Def_Zeta5_SourcePrimeSum
-- name    : Zeta5_SourcePrimeSum
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T14:18:49.772702+00:00
-- url     : https://prove2.me/theorems/9208f42f-27e4-410c-95d5-c3378ae760ce
-- title:
--   Zeta5: the log-prime weight $c(k)$ of the growth estimates
-- statement:
--   The log-prime weight $c(k) = \log k$ if $k$ is prime and $0$ otherwise, from `Apery/PrimeSum.lean` of the source project. The weighted prime sums of the growth estimates of the normaliser are written $\sum_k c(k) f(k)$. **Formalization Note** The declaration is the source definition, in the `Apery` namespace.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/PrimeSum.lean#L15-L16

import Mathlib

/-!
# The log-prime weight `cPrime` (source `Apery/PrimeSum.lean`)

`cPrime k = log k` if `k` is prime, and `0` otherwise. The weighted prime sums of the growth
estimates of the source (`Apery/PrimeSum.lean` and following) are written as
`∑ k, cPrime k * f k`.
-/

namespace Apery

/-- The log-prime weight. -/
noncomputable def cPrime (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

end Apery



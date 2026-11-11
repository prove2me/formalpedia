-- Prove2me | Definitions.Def_RandModSubsetSum_RoundingLoss
-- name    : RandModSubsetSum_RoundingLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:25.108782+00:00
-- url     : https://prove2.me/theorems/b4d537c1-a562-4498-b2d3-7e93f168224c
-- title:
--   The entropy-continuity modulus $f_q(t)$
-- statement:
--   For $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ with $0\log_20=0$ and an alphabet of size $q\ge 2$,
--   $$f_q(t)=\begin{cases}h_2(t)+t\log_2(q-1),&0\le t\le 1-1/q,\\ \log_2 q,&t>1-1/q,\end{cases}\qquad f_1(t)=0.$$
--   If two distributions on $q$ symbols differ by at most $t$ in total variation, their entropies differ by at most $f_q(t)$ (Appendix A). The paper uses it to bound the rounding loss $\eta$ in (54).
--
--   **Formalization Note** $h_2$ is the published `WildeQIT.binaryEntropy`.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Appendix A, p. 56

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

namespace RandModSubsetSum

/-- The entropy-continuity modulus of Appendix A (p. 56): for an alphabet of size `q ≥ 2`,
`f_q(t) = h₂(t) + t log₂(q − 1)` for `0 ≤ t ≤ 1 − 1/q`, `f_q(t) = log₂ q` for `t > 1 − 1/q`, and
`f₁(t) = 0`; `h₂(t) = −t log₂ t − (1 − t) log₂(1 − t)` with `0 log₂ 0 = 0`.
Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Appendix A, p. 56.

**Formalization Note.** `h₂` is the published `WildeQIT.binaryEntropy` (base 2, `0 log 0 = 0`
automatic). The value at `q = 0` and at `t < 0` is not used by the paper. -/
noncomputable def fq (q : ℕ) (t : ℝ) : ℝ :=
  if q ≤ 1 then 0
  else if t ≤ 1 - 1 / (q : ℝ) then WildeQIT.binaryEntropy t + t * Real.logb 2 ((q : ℝ) - 1)
  else Real.logb 2 q

end RandModSubsetSum



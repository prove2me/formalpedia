-- Prove2me | Definitions.Def_KhintchineTwoRegime_Supplement_sgn
-- name    : KhintchineTwoRegime_Supplement_sgn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:24:03.402672+00:00
-- url     : https://prove2.me/theorems/acfe2456-ba56-43ef-8b71-ed145e29147e
-- title:
--   Sign function with $\operatorname{sgn}(0)=1$
-- statement:
--   The **sign function** used for threshold functions is
--   $$
--   \operatorname{sgn}(x)=\begin{cases}1,& x\ge0,\\-1,& x<0.\end{cases}
--   $$
--   It takes only the values $\pm1$; in particular $\operatorname{sgn}(0)=+1$, so a threshold function is $+1$ at a point where its linear form vanishes.
--
--   **Formalization Note** This is not Mathlib's `Real.sign`, which is $0$ at $0$.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §4, p.10

import Mathlib

namespace KhintchineTwoRegime.Supplement

/-- The sign function of §4 (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §4, p.10):
`sgn(x) = 1` for `x ≥ 0` and `sgn(x) = −1` for `x < 0`.

**Formalization Note** `sgn(0) = +1`, as on p.10. This is not Mathlib's `Real.sign`, which
is `0` at `0`. -/
noncomputable def sgn (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

end KhintchineTwoRegime.Supplement



-- Prove2me | Definitions.Def_DRSub4633_hScalar
-- name    : DRSub4633_hScalar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:21.5269+00:00
-- url     : https://prove2.me/theorems/e1aac1c6-869a-4659-92d0-9f92af74497b
-- title:
--   The scalar recovery $h(r)$
-- statement:
--   For a scalar coordinate $r\in[0,1]$, the recovery is
--   $$h(r)=\begin{cases}1-e^{-r},&0\le r\le s,\\ r/(b+r),&s<r\le 1.\end{cases}$$
--   At $r=s$ the exponential branch applies.
--
--   **Formalization Note** The function is defined on all of $\mathbb R$: the exponential branch for $r\le s$ and the linear-fractional branch for $r>s$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4, Eq. (9), p.9

import Mathlib
import Definitions.Def_DRSub4633_sPar
import Definitions.Def_DRSub4633_bPar

namespace DRSub4633

/-- **The scalar recovery `h(r)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4, Eq. (9), p.9:
`h(r) = 1 − e^(−r)` for `0 ≤ r ≤ s` and `h(r) = r/(b + r)` for `s < r ≤ 1`. "At `r = s` the
exponential branch applies".

**Formalization Note.** The function is total on `ℝ`: the exponential branch for every `r ≤ s`, the
linear-fractional branch for every `r > s`. Only `r ∈ [0, 1]` is used. -/
noncomputable def hScalar (r : ℝ) : ℝ := if r ≤ sPar then 1 - Real.exp (-r) else r / (bPar + r)

end DRSub4633



-- Prove2me | Definitions.Def_log_one_plus_series
-- name    : log_one_plus_series
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T10:26:17.259485+00:00
-- url     : https://prove2.me/theorems/d3c73f64-0a48-4774-b355-9151f01e6314
-- title:
--   The formal power series of $\ln(1+x)$
-- statement:
--   The formal power series over $\mathbb{Q}$ associated with $\ln(1+x)$,
--
--   $$ L(x) \;=\; \sum_{k \ge 1} \frac{(-1)^{k+1}}{k}\, x^k \;=\; x - \frac{x^2}{2} + \frac{x^3}{3} - \frac{x^4}{4} + \cdots, $$
--
--   with constant term $0$. It is defined purely by its coefficient sequence, as an element of $\mathbb{Q}[[x]]$; no analytic content (convergence, the real or complex logarithm) is attached to it.
--
--   It is supplied so that the source's worked example — the $[2/2]$ Padé approximant of $\ln(1+x)$ — can be stated over a field in which the coefficients are exact, and it is reusable for any other formal identity involving the logarithmic series.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Examples', subsection 'ln(1+x)'

import Mathlib

/-!
# The formal power series of `ln(1 + x)`

Source: "Padé approximant", Wikipedia (oldid 1374746248), section *Examples*,
subsection `ln(1+x)`.
-/

namespace Pade

/-- The formal power series over `ℚ` of `ln(1 + x)`:
`x - x^2/2 + x^3/3 - x^4/4 + ⋯`, i.e. the coefficient of `X^k` is
`(-1)^(k+1) / k` for `k ≥ 1`, and `0` for `k = 0`. -/
noncomputable def logOnePlus : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k = 0 then 0 else (-1) ^ (k + 1) / (k : ℚ)

end Pade



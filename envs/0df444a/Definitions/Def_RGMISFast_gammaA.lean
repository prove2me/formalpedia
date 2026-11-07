-- Prove2me | Definitions.Def_RGMISFast_gammaA
-- name    : RGMISFast_gammaA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:44.908882+00:00
-- url     : https://prove2.me/theorems/9f863347-def2-4356-b19f-df07fe59455f
-- title:
--   $\gamma(a)=E[\exp(-2\min\{a+X,a_0\}/a)]$, $X\sim\mathrm{Exp}(1)$
-- statement:
--   For $0<a\le a_0$ let
--   $$
--   \gamma(a)=\mathbb E\Big[\exp\Big(-\frac{2\min\{a+X,a_0\}}{a}\Big)\Big],\qquad X\sim\mathrm{Exp}(1).
--   $$
--   It is the average of the conditional failure factor $e^{-2S(A,a)}$ per vertex of $A$, used in the averaging step of §6.2.
--
--   **Formalization Note** The expectation is the integral against Mathlib's Exp(1) law; the integrand is continuous with values in $(0,1]$, so it is integrable and the integral is a true expectation.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), §6.2, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_RGMISFast_rankCharge

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace RGMISFast

/-- `γ(a) = E[exp(−2 min{a + X, a₀}/a)]` for `X ∼ Exp(1)` and `0 < a ≤ a₀` (Dalirrooyfard,
Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*, STOC 2027
submission (manuscript sha256 e93cdfec…), §6.2, p.24).

**Formalization Note** The expectation is the Bochner integral against `expMeasure 1`, the Exp(1)
law. The integrand is continuous with values in `(0, 1]` for `a > 0`, hence integrable against
the probability measure `expMeasure 1`: the integral is never the junk value of a non-integrable
function. -/
noncomputable def gammaA (a : ℝ) : ℝ :=
  ∫ x, Real.exp (-2 * min (a + x) a0 / a) ∂(expMeasure 1)

end RGMISFast



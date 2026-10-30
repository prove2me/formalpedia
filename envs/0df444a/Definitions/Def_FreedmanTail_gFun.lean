-- Prove2me | Definitions.Def_FreedmanTail_gFun
-- name    : FreedmanTail_gFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:06.548045+00:00
-- url     : https://prove2.me/theorems/8352093b-806c-4efc-974a-6d16dd590361
-- title:
--   The function $g(x) = (e^x - 1 - x)/x^2$, $g(0) = 1/2$
-- statement:
--   Define $g : \mathbb R \to \mathbb R$ by
--   $$g(0) = \tfrac12, \qquad g(x) = \frac{e^{x} - 1 - x}{x^{2}} \quad (x \ne 0).$$
--   The value $\tfrac12$ at $0$ is the limit of the quotient, so $g$ is continuous. Lemma (3.1) shows that $g$ is increasing; this monotonicity is the source of the exponential moment bound (3.2).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, (3.1) Lemma, p. 106

import Mathlib

namespace FreedmanTail

/-- **The function `g` of Lemma (3.1).**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118,
(3.1) Lemma, p. 106: "Let g(0) = ½ and g(x) = (e^x − 1 − x)/x² for x ≠ 0."

`gFun x = 1/2` if `x = 0`, and `(Real.exp x - 1 - x) / x ^ 2` otherwise; this is the continuous
extension of `(e^x − 1 − x)/x²` to `x = 0`. -/
noncomputable def gFun (x : ℝ) : ℝ := if x = 0 then 1 / 2 else (Real.exp x - 1 - x) / x ^ 2

end FreedmanTail



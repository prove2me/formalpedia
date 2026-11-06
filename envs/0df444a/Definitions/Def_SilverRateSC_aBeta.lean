-- Prove2me | Definitions.Def_SilverRateSC_aBeta
-- name    : SilverRateSC_aBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:44:57.003726+00:00
-- url     : https://prove2.me/theorems/463b8ab6-541a-4958-996f-ccbf2a4781d7
-- title:
--   The bending constants $R$, $c_\beta$, $a_\beta$, (31) and (34)
-- statement:
--   For a bending parameter $0<\beta\le1/4$ put
--   $$R=1+\beta,\qquad c_\beta=\beta+\sqrt{1+2\beta},\qquad a_\beta:=8+4\beta+4\exp\Bigl[\frac{\sqrt2\,R-\beta}{\beta}\Bigr].$$
--   $R$ is the radius of the circle centred at $(\beta,\beta)$ that carries the bending arc, $(c_\beta,0)$ is the arc's upper endpoint, and $a_\beta$ is the additive constant in the bending transfer bound of Lemma 3.1.
--
--   **Formalization Note** In $a_\beta$ the square root covers only $2$: the exponent is $(\sqrt2\cdot R-\beta)/\beta$.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §A.1, (31), p.29 and (34), p.30

import Mathlib

namespace SilverRateSC

/-- The radius `R = 1 + β` of the circular arc, (31). -/
noncomputable def RBeta (β : ℝ) : ℝ := 1 + β

/-- The constant `c_β = β + √(1 + 2β)`, (31): the first coordinate of the endpoint `(c_β, 0)`
of the arc. -/
noncomputable def cBeta (β : ℝ) : ℝ := β + Real.sqrt (1 + 2 * β)

/-- **The bending constants** (31), (34): `R = 1 + β`, `c_β = β + √(1 + 2β)` and
`a_β := 8 + 4β + 4 exp[(√2·R − β)/β]`, for a bending parameter `0 < β ≤ 1/4`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §A.1, (31), p. 29 and (34), p. 30.

**Formalization Note** In (34) the radical covers only `2`: the exponent is `(√2 · R − β)/β`
(checked on the rendered page). The definitions are used only with `0 < β ≤ 1/4`. -/
noncomputable def aBeta (β : ℝ) : ℝ :=
  8 + 4 * β + 4 * Real.exp ((Real.sqrt 2 * RBeta β - β) / β)

end SilverRateSC



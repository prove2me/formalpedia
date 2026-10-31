-- Prove2me | Definitions.Def_FullPriceTime_mrs
-- name    : FullPriceTime_mrs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:07.135405+00:00
-- url     : https://prove2.me/theorems/7e925366-330a-4591-9910-4ec11ce8787d
-- title:
--   Marginal rate of substitution of time for money $\chi(t_l,c_l)$
-- statement:
--   The **marginal rate of substitution of time for money** at $(t_l,c_l)$ is
--   $$\chi(t_l,c_l)=\frac{\partial U(t_l,c_l)/\partial t_l}{\partial U(t_l,c_l)/\partial c_l}.$$
--   It is the slope of the consumer's indifference trade-off between leisure time and leisure money, i.e. how much money one unit of time is worth to her.
--
--   **Formalization Note** The partial derivatives are the Fréchet derivative of $U:\mathbb R^2\to\mathbb R$ applied to $(1,0)$ and $(0,1)$. Lean returns $0$ for the derivative of a non-differentiable function and for a division by $0$, so every theorem about $\chi$ assumes differentiability and a non-zero denominator at the point.
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, §3.1, p.8 (definition of χ); Appendix A.2, p.32

import Mathlib

namespace FullPriceTime

/-- **The marginal rate of substitution of time for money, `χ(t_l, c_l)`.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §3.1, p.8 (PDF p.8), repeated in Appendix A.2, p.32: "Define
χ(tl,cl) = ∂U(tl,cl)/∂tl / ∂U(tl,cl)/∂cl."

`mrs U x` is the partial derivative of `U` in its first argument (leisure time) divided by its
partial derivative in its second argument (leisure consumption), at the point `x = (t_l, c_l)`.

**Formalization Note** The partial derivatives are the Fréchet derivative of `U : ℝ × ℝ → ℝ`
applied to the unit vectors `(1, 0)` and `(0, 1)`. Lean's `fderiv` is `0` where `U` is not
differentiable and division by `0` is `0`; theorems about `mrs` therefore assume differentiability
and a non-zero denominator at the point, where the paper's quotient is defined. -/
noncomputable def mrs (U : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  fderiv ℝ U x (1, 0) / fderiv ℝ U x (0, 1)

end FullPriceTime



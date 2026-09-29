-- Prove2me | Definitions.Def_RobustMeanCov_OnePoint_OnePointSupportWrt
-- name    : RobustMeanCov_OnePoint_OnePointSupportWrt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:40:01.604347+00:00
-- url     : https://prove2.me/theorems/24d0ba9d-b8c2-4591-a1b4-77c10f45a868
-- title:
--   Definition 3 — one-point support property with respect to $(\mu,\sigma^2)$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$, $m\in\mathbb R$ and $s\ge0$. The function $u$ has the **one-point support property with respect to $(m,s^2)$** if there is a quadratic $q(y)=Ay^2+By+C$ such that
--
--   1. $q$ supports $u$: $q(y)\le u(y)$ for all $y\in\mathbb R$;
--   2. $q$ intersects $u$ at $m$: $q(m)=u(m)$;
--   3. with $r_p$ the two-point law of mean $m$ and variance $s^2$ on $\{m+\sqrt{(1-p)/p}\,s,\ m-\sqrt{p/(1-p)}\,s\}$ (mass $p$ on the first point), either
--
--   $$
--   \lim_{p\to0^+}E[u(r_p)]=E[q(r_p)]\qquad\text{or}\qquad\lim_{p\to1^-}E[u(r_p)]=E[q(r_p)].
--   $$
--
--   Since every $r_p$ has mean $m$ and variance $s^2$, $E[q(r_p)]=A(m^2+s^2)+Bm+C$ does not depend on $p$. The property says that the lower bound given by the supporting quadratic (Proposition 3) is approached by two-point laws that degenerate, one point tending to the mean and the other to $\pm\infty$.
--
--   **Formalization Note** $E[u(r_p)]$ is written as the explicit two-point average `twoPointValue u m s p` of (8), and $E[q(r_p)]$ as $A(m^2+s^2)+Bm+C$. The limits are one-sided limits inside $(0,1)$.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, pp. 102–103, §3.2, Definition 3

import Mathlib
import Definitions.Def_RobustMeanCov_OnePoint_twoPointValue
open Filter Topology

namespace RobustMeanCov.OnePoint

/-- Definition 3 (Popescu 2007, p. 103), with respect to `(m, s²)`: some quadratic
`q(y) = A y² + B y + C` supports `u` (`q ≤ u` on `ℝ`), meets it at `m`, and the expected
utility of the two-point law `r_p` tends to `E[q(r_p)] = A(m² + s²) + B m + C` as `p → 0⁺`
or as `p → 1⁻`. -/
def OnePointSupportWrt (u : ℝ → ℝ) (m s : ℝ) : Prop :=
  ∃ A B C : ℝ, (∀ y : ℝ, A * y ^ 2 + B * y + C ≤ u y) ∧ A * m ^ 2 + B * m + C = u m ∧
    (Tendsto (twoPointValue u m s) (𝓝[>] 0) (𝓝 (A * (m ^ 2 + s ^ 2) + B * m + C)) ∨
      Tendsto (twoPointValue u m s) (𝓝[<] 1) (𝓝 (A * (m ^ 2 + s ^ 2) + B * m + C)))

end RobustMeanCov.OnePoint



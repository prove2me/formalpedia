-- Prove2me | Definitions.Def_FullPriceTime_buyerUtility
-- name    : FullPriceTime_buyerUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:31.774639+00:00
-- url     : https://prove2.me/theorems/f9a7e1e5-fa0f-4023-bc5c-639e87db680e
-- title:
--   Buyer's optimal leisure utility $u^B(\theta,r,\delta)$
-- statement:
--   For a consumer with horizon $T$, utility $U$, overhead time $O$ and compensation $\Pi_\theta$, the **buyer's optimal leisure utility** at price $r$ and time commitment $\delta$ is
--   $$u^B(\theta,r,\delta)=\sup\{\,U(t_l,c_l)\ :\ (t_l,c_l,t_w,c_O)\ \text{feasible for (PC) with } y=1\,\}.$$
--   It is the utility from the continuous leisure activity of a consumer who buys the discrete service; her total utility is $u^B(\theta,r,\delta)+V$.
--
--   **Formalization Note** The type $\theta$ enters through the compensation function. The supremum is taken in the extended reals: it is $-\infty$ when $(r,\delta)$ is infeasible and $+\infty$ when the utilities are unbounded. Attainment is not assumed (the paper does not assume $O$ continuous).
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, §2.2, p.7

import Mathlib
import Definitions.Def_FullPriceTime_IsFeasiblePlan

namespace FullPriceTime

/-- **The buyer's optimal utility from the continuous leisure activity, `u^B(θ, r, δ)`.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §2.2, p.7 (PDF p.7): "Let uB(θ,r,δ) be the optimal utility from the
continuous leisure activity for a type θ who purchases the discrete service at price r and time
commitment δ. That is, uB(θ,r,δ) + V is the optimal total utility of a consumer that buys, i.e.
when y = 1."

`buyerUtility T U O comp r δ` is the supremum of `U(t_l, c_l)` over all plans that are feasible for
(PC) with `y = 1`, computed in the extended reals.

**Formalization Note** The type `θ` enters through the compensation function `comp = Π_θ`. The
paper's "optimal utility" is the supremum; attainment is not assumed (the paper does not assume
`O` continuous). The supremum is taken in `EReal`, so it is `+∞` when the utilities are unbounded
and `⊥ = −∞` when `(r, δ)` is infeasible, instead of a junk real value. -/
noncomputable def buyerUtility (T : ℝ) (U : ℝ × ℝ → ℝ) (O : ℝ → ℝ) (comp : ℝ → ℝ)
    (r δ : ℝ) : EReal :=
  sSup ((fun p : Plan => ((U (p.tl, p.cl) : ℝ) : EReal)) ''
    {p : Plan | IsFeasiblePlan T O comp r δ 1 p})

end FullPriceTime



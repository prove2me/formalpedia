-- Prove2me | Definitions.Def_ReferencePricing_LossAversion_Kinked
-- name    : ReferencePricing_LossAversion_Kinked
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T08:33:49.334407+00:00
-- url     : https://prove2.me/theorems/40f12fdd-212c-4fb3-ad4a-3a87e129c0fb
-- title:
--   Kinked reference effect $R_K$ (4), convex combination $R_\theta$ (8), and Assumptions 4–5 (loss aversion)
-- statement:
--   Under loss aversion the reference effect has a kink at $x=0$. Let $R_G$ (gains) and $R_L$ (losses) be two reference effects. The **kinked reference effect** of equation (4) is
--   $$
--   R_K(x,r)=\begin{cases}R_G(x,r), & x\ge 0,\\ R_L(x,r), & x<0,\end{cases}
--   $$
--   and for $\theta\in[0,1]$ the smooth **convex combination** of equation (8) is $R_\theta(x,r)=\theta R_G(x,r)+(1-\theta)R_L(x,r)$, so that $R_0=R_L$ and $R_1=R_G$.
--
--   With $P=[0,\bar p]$ and $\lambda_G,\lambda_L$ the slopes of $R_G,R_L$ at $x=0$:
--
--   1. **Assumption 4** (Kinked Reference Effect). $R_G$ and $R_L$ are twice differentiable and increasing in $x$. $R_G-R_L$ is single crossing in $x$, meaning it has a unique zero on its domain. And $\lambda_L(r)>\lambda_G(r)$ for all $r$.
--   2. **Assumption 5** (Gain/Loss Profit). The short-term profits $\Pi_G(p,r)=\pi(p)+pR_G(r-p,r)$ and $\Pi_L(p,r)=\pi(p)+pR_L(r-p,r)$ satisfy Assumption 3.
--
--   **Formalization Note** The paper writes $R_K=\mathbf 1_{(x\ge 0)}R_G+\mathbf 1_{(x\le 0)}R_L$, which counts $x=0$ twice. Because $R_G(0,r)=R_L(0,r)=0$ (Remark 1 for each component, carried by Assumption 1 in the theorems), both readings agree. Monotonicity in $x$ and single crossing are required for $r\in P$ on the gains $[r-\bar p,r]$ reachable from $P$, and this interval contains $0$. The slope inequality holds for all real $r$, as printed. Twice differentiability uses the same encoding as Assumption 2.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 421, Assumption 4 and Eq. (4); p. 422, Assumption 5 and Eq. (8)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
open RobustBooking.Shared

namespace ReferencePricing.LossAversion

/-- The kinked reference effect (4), p. 421: `R_K(x, r) = R_G(x, r)` for gains `x ≥ 0` and
`R_L(x, r)` for losses `x < 0`. The page writes `1_{x≥0} R_G + 1_{x≤0} R_L`, which counts
`x = 0` twice; since `R_G(0, r) = R_L(0, r) = 0` both readings agree. -/
noncomputable def RK (RG RL : ℝ → ℝ → ℝ) (x r : ℝ) : ℝ :=
  if 0 ≤ x then RG x r else RL x r

/-- The smooth convex combination (8), p. 422: `R_θ(x, r) = θ R_G(x, r) + (1 − θ) R_L(x, r)`.
`R_0 = R_L` and `R_1 = R_G`. -/
def Rtheta (RG RL : ℝ → ℝ → ℝ) (θ x r : ℝ) : ℝ :=
  θ * RG x r + (1 - θ) * RL x r

/-- Assumption 4 (Kinked Reference Effect), p. 421: `R_L` and `R_G` are twice differentiable,
increasing in `x` (on the gains `[r − p̄, r]` reachable from `P = [0, p̄]`), `R_G − R_L` is single
crossing in `x` (a unique zero on `[r − p̄, r]`, for `r ∈ P`), and `λ_L(r) > λ_G(r)` for all `r`
(loss aversion). -/
structure Assumption4 (pbar : ℝ) (RG RL : ℝ → ℝ → ℝ) : Prop where
  smooth_gain : Assumption2 RG
  smooth_loss : Assumption2 RL
  monotone_gain : ∀ r ∈ Set.Icc (0 : ℝ) pbar, MonotoneOn (fun x => RG x r) (Set.Icc (r - pbar) r)
  monotone_loss : ∀ r ∈ Set.Icc (0 : ℝ) pbar, MonotoneOn (fun x => RL x r) (Set.Icc (r - pbar) r)
  single_crossing : ∀ r ∈ Set.Icc (0 : ℝ) pbar,
    ∃! x : ℝ, x ∈ Set.Icc (r - pbar) r ∧ RG x r - RL x r = 0
  loss_aversion : ∀ r : ℝ, refSlope RG r < refSlope RL r

/-- Assumption 5 (Gain/Loss Profit), p. 422: the short-term profits `Π_G` and `Π_L` of the smooth
reference effects `R_G`, `R_L` satisfy Assumption 3. -/
structure Assumption5 (pbar : ℝ) (d : ℝ → ℝ) (RG RL : ℝ → ℝ → ℝ) : Prop where
  gain : Assumption3 pbar d RG
  loss : Assumption3 pbar d RL

end ReferencePricing.LossAversion



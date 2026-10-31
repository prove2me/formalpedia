-- Prove2me | Definitions.Def_CompInvestBayes_gImmediate
-- name    : CompInvestBayes_gImmediate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:22.331237+00:00
-- url     : https://prove2.me/theorems/5cf9fbc8-f299-4ba1-8046-e94e5057182e
-- title:
--   Immediate-investment profit $g(y,S_2)$ (10), $g(y)$ (11) and the size $S^*_2$ (EC.3)
-- statement:
--   If the follower invests the size $S_2$ immediately at belief $y$, its profit is
--
--   $$
--   g(y,S_2)=\mathbb E\Big[\int_0^\infty e^{-\lambda t}\,dX_{2,t}-c_2S_2\ \Big|\ \pi_0=y\Big],
--   $$
--
--   and the best immediate-investment profit is $g(y)=\max_{S_2\ge0}g(y,S_2)$. The size
--
--   $$
--   S^*_2(y)=\begin{cases}\mu_{2,L} & y\le c_2\lambda,\\ \mu_{2,H} & y>c_2\lambda\end{cases}
--   $$
--
--   is the maximizer of (EC.3).
--
--   **Formalization Note** $g(y,S_2)$ is the follower's profit (7) for $\tau\equiv0$ and constant $S_2$; the maximum is a supremum over $S_2\ge0$, and its attainment is a milestone.
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), (10), (11), p.11 (PDF 11); (EC.3), p.ec2 (PDF 34)

import Mathlib
import Definitions.Def_CompInvestBayes_FollowerStrategy

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Immediate-investment profit** `g(y, S₂) := E[∫_0^∞ e^{-λt} dX_{2,t} − c₂ S₂ | π₀ = y]`
(10) (SSRN 3408260, p.11, PDF 11): the follower's expected total discounted profit if it invests the
size `S₂` at time `0` under the belief `y`. -/
noncomputable def gImm (p : Params) (σ : ℝ) (E : Setup Ω) (y S2 : ℝ) : ℝ :=
  followerValue p σ E y (fun _ => 0) (fun _ => S2)

/-- **Best immediate-investment profit** `g(y) := max_{S₂ ≥ 0} g(y, S₂)` (11) (SSRN 3408260,
p.11, PDF 11).

**Formalization Note.** `max` is `sSup` over `S₂ ≥ 0`; the milestone `eq_EC_2_EC_4` states that
the maximum is attained. -/
noncomputable def gMax (p : Params) (σ : ℝ) (E : Setup Ω) (y : ℝ) : ℝ :=
  sSup ((fun S2 => gImm p σ E y S2) '' Set.Ici (0 : ℝ))

/-- **The maximizer** `S*₂` of (EC.3) (SSRN 3408260, p.ec2, PDF 34): `µ_{2,L}` if `y ≤ c₂λ`,
`µ_{2,H}` if `y > c₂λ`. -/
noncomputable def S2star (p : Params) (y : ℝ) : ℝ :=
  if y ≤ p.c2 * p.lam then p.mu2L else p.mu2H

end CompInvestBayes



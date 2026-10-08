-- Prove2me | Definitions.Def_PoissonDirichlet_Moments_Setting
-- name    : PoissonDirichlet_Moments_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:40.381352+00:00
-- url     : https://prove2.me/theorems/97aba189-8fa6-4fd4-bf6b-3374803a5bdc
-- title:
--   Equations (27), (43), and (51): local-time coordinates, the PD tilt constant, and E(t)
-- statement:
--   This definition file adds three quantities to the shared Poisson–Dirichlet setting. The paper indexes frequencies from $1$; Lean's `v k` denotes $V_{k+1}$.
--
--   1. Given a positive local time $L$ and ranked frequency $V_n$, the variable of (27) is
--      $$X_n=L V_n^{-\alpha}.$$
--      The local time is the limit $L=\lim_{n\to\infty}nV_n^\alpha$ from (24); this file defines the expression for $X_n$ once $L$ is supplied.
--   2. The change-of-measure constant of (43) is
--      $$C_{\alpha,\theta}=\frac{\Gamma(\theta+1)}{\Gamma(\theta/\alpha+1)}\Gamma(1-\alpha)^{\theta/\alpha}.$$
--   3. The exponential integral in Corollary 18 is
--      $$E(t)=\int_t^\infty x^{-1}e^{-x}\,dx.$$
--
--   The constant enters the $\mathrm{PD}(\alpha,\theta)$ change of measure, while $E(t)$ enters the $\alpha=0$ moment formula.
--
--   **Formalization Note** This file imports the shared Ratio and Wendel settings. It defines only $X_n$, $C_{\alpha,\theta}$, and $E(t)$. The formula for $C_{\alpha,\theta}$ is intended for $0<\alpha<1$ and $\theta>-\alpha$; the formula for $E(t)$ is used for $t>0$. Their total Lean definitions carry no probabilistic claim outside those ranges. The identity $C_{\alpha,\theta}=1/E_{\alpha,0}[L^{\theta/\alpha}]$ is a theorem, not a definition.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 862, (27); p. 865, (43); p. 867, Corollary 18, (51)

import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- (27), last expression, 0-based: `Xseq α l v k = l · (v k)^{-α}` is `X_{k+1} = L V_{k+1}^{-α}`
when `l` is the local time `L` of (24). -/
noncomputable def Xseq (α l : ℝ) (v : ℕ → ℝ) (k : ℕ) : ℝ := l * v k ^ (-α)

/-- (43), second expression: `C_{α,θ} = Γ(θ + 1) / Γ(θ/α + 1) · Γ(1 - α)^{θ/α}`. -/
noncomputable def pdConst (α θ : ℝ) : ℝ :=
  Real.Gamma (θ + 1) / Real.Gamma (θ / α + 1) * Real.Gamma (1 - α) ^ (θ / α)

/-- Corollary 18: `E(t) = ∫_t^∞ x^{-1} e^{-x} dx` (used for `t > 0`). -/
noncomputable def expIntE (t : ℝ) : ℝ :=
  ∫ x in Set.Ioi t, x⁻¹ * Real.exp (-x)

end PoissonDirichlet.Moments



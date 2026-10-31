-- Prove2me | Definitions.Def_CryptoMiningMFG_optRate
-- name    : CryptoMiningMFG_optRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:59:46.280302+00:00
-- url     : https://prove2.me/theorems/77555f20-d131-4160-aefb-d5fd313858e5
-- title:
--   Optimal hash rate (feedback) $\alpha^*(t,x;\bar\alpha)$ of eq. (2.6)
-- statement:
--   With $\partial_x v=\partial_x v(t,x;\bar\alpha)$ and $\Delta v=v(t,x+r;\bar\alpha)-v(t,x;\bar\alpha)$, the **optimal hash rate** of eq. (2.6) is
--
--   $$
--   \alpha^*(t,x;\bar\alpha)=\begin{cases}-M\bar\alpha_t+\sqrt{\dfrac{\mathcal K M\bar\alpha_t\,\Delta v}{c\,\partial_x v}}, & \bar\alpha_t<\dfrac{\mathcal K\,\Delta v}{M c\,\partial_x v},\\[8pt] 0, & \text{otherwise}.\end{cases}
--   $$
--
--   It is the pointwise maximizer of the Hamiltonian of the HJB equation (2.5), evaluated on the value function $v$. A miner with wealth $x$ hashes at this rate at time $t$ in the mean field game.
--
--   **Formalization Note** $\partial_x v$ is Lean's `deriv`, which is $0$ where $v(t,\cdot)$ is not differentiable; the equilibrium definition requires differentiability.
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, eq. (2.6) p.11

import Mathlib
import Definitions.Def_CryptoMiningMFG_Value

namespace CryptoMiningMFG

/-- The **optimal hash rate** (feedback) of eq. (2.6), p.11 of Li, Reppen, Sircar,
arXiv:1912.01952v2:
`α*(t, x; ᾱ) = −M ᾱ_t + √(𝒦 M ᾱ_t Δv / (c ∂ₓv))` if `ᾱ_t < 𝒦 Δv / (M c ∂ₓv)`, and `0` otherwise,
with `∂ₓv = ∂ₓ v(t, x; ᾱ)` and `Δv = v(t, x + r; ᾱ) − v(t, x; ᾱ)`, evaluated on the value function
`v` of eq. (2.4).

**Formalization Note.** `∂ₓv` is `deriv`, which is `0` where `v(t, ·)` is not differentiable; the
equilibrium definition requires differentiability, and for exponential utility `∂ₓv > 0` and
`Δv > 0`, so no division by zero or square root of a negative number occurs there. -/
noncomputable def optRate (P : Model) (abar : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if abar t < P.K * (value P t (x + P.r) abar - value P t x abar) /
      (P.M * P.c * deriv (fun y => value P t y abar) x) then
    -P.M * abar t + Real.sqrt (P.K * P.M * abar t * (value P t (x + P.r) abar - value P t x abar) /
      (P.c * deriv (fun y => value P t y abar) x))
  else 0

end CryptoMiningMFG



-- Prove2me | Definitions.Def_NetFeePlatform_InteropFee_Symmetric
-- name    : NetFeePlatform_InteropFee_Symmetric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:42.969785+00:00
-- url     : https://prove2.me/theorems/0b50c020-31a5-47e6-962b-e3e7d8bd3b16
-- title:
--   Proof of Proposition 7, p. 52 — symmetric share, symmetric diversion ratio and the function ξ(t; λ)
-- statement:
--   Closed forms at a symmetric net-fee profile, where all $J$ platforms charge the same net fee $\tau$, in the Logit model with outside-option weight $w \ge 0$.
--
--   1. The common share is
--   $$n(\tau) = \frac{e^{-\tau}}{w + J e^{-\tau}}.$$
--   2. The common diversion ratio (32) is
--   $$\varphi(\tau) = \frac{(J-1)\, n(\tau)}{1 - n(\tau)}.$$
--   3. The function of the proof of Proposition 7 (p. 52), with the Logit markup $n^j/(-\partial n^j/\partial t^j) = 1/(1-n^j)$, is
--   $$\xi(\tau;\lambda) = -\tau + c + \frac{1}{1-n(\tau)} - 2\gamma n(\tau) - \gamma\lambda\big(J - 1 - \varphi(\tau)\big) n(\tau).$$
--
--   The paper characterizes the symmetric equilibrium net fees as the zeros of $\xi(\cdot;\lambda)$, and compares $\xi$ across two levels of interoperability.
--
--   **Formalization Note** $J$ is a natural number cast to $\mathbb R$. When $1 - n(\tau) = 0$ (only for $J = 1$, $w = 0$) Lean's division returns $0$; every theorem using these objects assumes $J \ge 2$, so $n(\tau) \le 1/2 < 1$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 52, proof of Proposition 7 (definition of ξ(t; λ)); p. 39, (32)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropFee

/-- Each platform's Logit share when all `J` platforms charge the same net fee `τ`:
`e^{-τ} / (w + J e^{-τ})`. -/
noncomputable def nSym (w : ℝ) (J : ℕ) (τ : ℝ) : ℝ :=
  Real.exp (-τ) / (w + J * Real.exp (-τ))

/-- The diversion ratio (32) at a constant net-fee profile: (J − 1)·n / (1 − n). -/
noncomputable def phiSym (w : ℝ) (J : ℕ) (τ : ℝ) : ℝ :=
  ((J : ℝ) - 1) * nSym w J τ / (1 - nSym w J τ)

/-- The function ξ(t; λ) of the proof of Proposition 7 (p. 52), Logit markup `1 / (1 - n)`. -/
noncomputable def xi (w c γ lam : ℝ) (J : ℕ) (τ : ℝ) : ℝ :=
  -τ + c + 1 / (1 - nSym w J τ) - 2 * γ * nSym w J τ
    - γ * lam * ((J : ℝ) - 1 - phiSym w J τ) * nSym w J τ

end NetFeePlatform.InteropFee



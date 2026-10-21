-- Prove2me | Definitions.Def_FracRiccati_Radius_Constants
-- name    : FracRiccati_Radius_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:20.037558+00:00
-- url     : https://prove2.me/theorems/6eb16113-0dda-4692-a5fb-74b391df5c99
-- title:
--   Theorem 3.3, pp. 4, 9 — Beta function B, constant c_α, lower bound τ∗, B̃(α) and the upper-bound constant C_α
-- statement:
--   This file defines the explicit constants that appear in Theorem 3.3 of Callegaro, Grasselli and Pagès. Throughout, $x_+=\max(x,0)$ and $a\wedge b=\min(a,b)$.
--
--   1. **Beta function** (Notation, p. 4): for $a,b>0$,
--   $$B(a,b)=\frac{\Gamma(a)\Gamma(b)}{\Gamma(a+b)}.$$
--   2. **The constant $c_\alpha$** (Theorem 3.3 (a)):
--   $$c_\alpha=2^{\,2-(1-2\alpha)_+-2(\alpha-1)_+}\,\alpha^{\alpha-1}\,B(\alpha\wedge1,\alpha\wedge1).$$
--   3. **The lower bound $\tau_*$** of the convergence radius (3.22): for $\lambda,\mu,\nu\in\mathbb C$,
--   $$\tau_*=\frac{2^{\frac1\alpha-(\frac1\alpha-2)_+}\,\alpha}{\Big(|\mu|+\sqrt{|\mu|^2+c_\alpha\frac{|\lambda||\nu|}{\Gamma(\alpha)}}\Big)^{1/\alpha}}.$$
--   4. **The constant $\widetilde B(\alpha)$** (Theorem 3.3 (b)):
--   $$\widetilde B(\alpha)=B(\alpha,\alpha)-2^{1-2\alpha}.$$
--   5. **The constant $C_\alpha$** of the upper bound (Theorem 3.3 (b)):
--   $$C_\alpha=\begin{cases}\big(3\cdot5^{\alpha-1}\big)^{\frac1{2\alpha}}\sqrt\alpha, & \alpha\in(0,1],\\[4pt] \dfrac{\sqrt{2\alpha}}{\widetilde B(\alpha)}, & \alpha\in(1,2].\end{cases}$$
--
--   These constants make the bounds of Theorem 3.3 explicit: $\tau_*\le R_{\psi_{\lambda,\mu,\nu}}$, and $R\le C_\alpha(\Gamma(\alpha+1)/(\lambda\nu))^{1/(2\alpha)}$ for real parameters of equal sign.
--
--   **Formalization Note** The page prints $\mu^2$ under the square root of $\tau_*$; for complex $\mu$ this is read as $|\mu|^2$, the coefficient of the quadratic equation in the proof (p. 28) being $|\mu|$. The paper typesets $C_\alpha$ for $\alpha\le1$ as "$(3.5^{\alpha-1})$", which is $3\cdot5^{\alpha-1}$: the proof's final bound (p. 32) is $(3/5^{1-\alpha})^{1/(2\alpha)}$. The definitions are total functions of real $\alpha$; they are used only for $0<\alpha\le2$, where every Gamma argument is positive and every real power has a positive base. The case split of $C_\alpha$ is `if α ≤ 1`.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 4 (Notation), p. 9, Theorem 3.3 (a), (b), (3.22)

import Mathlib

namespace FracRiccati.Radius

/-- The Beta function `B(a, b) = Γ(a) Γ(b) / Γ(a + b)` (Notation, p. 4). -/
noncomputable def betaFn (a b : ℝ) : ℝ := Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)

/-- `c_α = 2^{2 - (1 - 2α)^+ - 2(α - 1)^+} α^{α - 1} B(α ∧ 1, α ∧ 1)` (Theorem 3.3 (a), p. 9). -/
noncomputable def cAlpha (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 - max (1 - 2 * α) 0 - 2 * max (α - 1) 0) * α ^ (α - 1) *
    betaFn (min α 1) (min α 1)

/-- `τ_* = 2^{1/α - (1/α - 2)^+} α / (|μ| + √(|μ|² + c_α |λ||ν| / Γ(α)))^{1/α}` (3.22). -/
noncomputable def tauStar (α : ℝ) (lam mu nu : ℂ) : ℝ :=
  (2 : ℝ) ^ (1 / α - max (1 / α - 2) 0) * α /
    (‖mu‖ + Real.sqrt (‖mu‖ ^ 2 + cAlpha α * ‖lam‖ * ‖nu‖ / Real.Gamma α)) ^ (1 / α)

/-- `B̃(α) = B(α, α) - 2^{1 - 2α}` (Theorem 3.3 (b), p. 9). -/
noncomputable def BTilde (α : ℝ) : ℝ := betaFn α α - (2 : ℝ) ^ (1 - 2 * α)

/-- `C_α = (3 · 5^{α-1})^{1/(2α)} √α` for `α ∈ (0, 1]` and `C_α = √(2α) / B̃(α)` for
`α ∈ (1, 2]` (Theorem 3.3 (b), p. 9). -/
noncomputable def CAlpha (α : ℝ) : ℝ :=
  if α ≤ 1 then (3 * (5 : ℝ) ^ (α - 1)) ^ (1 / (2 * α)) * Real.sqrt α
  else Real.sqrt (2 * α) / BTilde α

end FracRiccati.Radius



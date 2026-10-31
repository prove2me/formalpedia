-- Prove2me | Definitions.Def_CompInvestBayes_closedForms
-- name    : CompInvestBayes_closedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:46.157555+00:00
-- url     : https://prove2.me/theorems/1751fb8c-e052-4eb9-9dd6-845dcd389dd6
-- title:
--   Closed forms $q$, $\eta$, $a$, $b$, $\xi_1$, $\xi_2$, $H_0$, $\varphi_{\ell^*}$, $\varphi_{h^*}$, $H_1$, $f_1$, $f_2$
-- statement:
--   The closed forms of the paper, for a leader size $S_1$ and volatility $\sigma$:
--
--   1. signal quality $q(S_1)=(\min(S_1,\mu_H)-\min(S_1,\mu_L))^2/\sigma^2$ (6), and $\eta=\sqrt{1+8\lambda/q(S_1)}$ (16);
--   2. $a(x,z)=\big(x^{\frac{1+\eta}2}(1-x)^{\frac{1-\eta}2}-x^{\frac{1-\eta}2}(1-x)^{\frac{1+\eta}2}(\tfrac{z}{1-z})^\eta\big)^{-1}$ (17) and $b(x,z)=\big(x^{\frac{1-\eta}2}(1-x)^{\frac{1+\eta}2}-x^{\frac{1+\eta}2}(1-x)^{\frac{1-\eta}2}(\tfrac{1-z}{z})^\eta\big)^{-1}$ (18);
--   3. $\xi_1(y)=y\min\{S_1,\mu_H\}+(1-y)\min\{S_1,\mu_L\}$ (19) and $\xi_2(y)=y\min\{S_1,\mu_{1,H}\}+(1-y)\min\{S_1,\mu_{1,L}\}$ (20);
--   4. $H_0(S_1,y_0)=y_0\min\{S_1,\mu_{1,H}\}/\lambda+(1-y_0)\min\{S_1,\mu_{1,L}\}/\lambda-c_1S_1$ (22);
--   5. for thresholds $(\ell,h)$, $\varphi_{\ell^*}(y_0)=a(\ell,h)f_1(y_0)+b(\ell,h)f_2(y_0)$ (24), $\varphi_{h^*}(y_0)=a(h,\ell)f_1(y_0)+b(h,\ell)f_2(y_0)$ (25), with $f_1(y)=y^{\frac{1+\eta}2}(1-y)^{\frac{1-\eta}2}$, $f_2(y)=y^{\frac{1-\eta}2}(1-y)^{\frac{1+\eta}2}$;
--   6. $H_1(S_1,y_0)=-\frac{\xi_1(\ell)-\xi_2(\ell)}{\lambda}\varphi_{\ell^*}(y_0)-\frac{\xi_1(h)-\xi_2(h)}{\lambda}\varphi_{h^*}(y_0)+\frac{\xi_1(y_0)}{\lambda}-c_1S_1$ (23).
--
--   Theorem 1 identifies the leader's profit with $H_0$ and $H_1$.
--
--   **Formalization Note** Powers are real powers. The thresholds $(\ell,h)$ (the paper's $\ell^*(S_1),h^*(S_1)$) are explicit arguments of $\varphi$ and $H_1$. $\eta$ is used for $S_1>\mu_L$, where $q(S_1)>0$.
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), (6) p.9, (16)–(20) p.13, (22)–(25) p.14 (PDF 9, 13, 14); f_1, f_2 p.ec24 (PDF 56)

import Mathlib
import Definitions.Def_CompInvestBayes_Params

namespace CompInvestBayes

/-- **Signal quality** `q(S₁) := (min(S₁, µ_H) − min(S₁, µ_L))² / σ²` (6) (SSRN 3408260, p.9,
PDF 9). -/
noncomputable def q (p : Params) (σ S1 : ℝ) : ℝ :=
  (min S1 p.muH - min S1 p.muL) ^ 2 / σ ^ 2

/-- `η := √(1 + 8λ/q(S₁))` (16) (SSRN 3408260, p.13, PDF 13). Used for `S₁ > µ_L`, where
`q(S₁) > 0`. -/
noncomputable def eta (p : Params) (σ S1 : ℝ) : ℝ :=
  Real.sqrt (1 + 8 * p.lam / q p σ S1)

/-- `a(x, z) := ( x^{(1+η)/2} (1−x)^{(1−η)/2} − x^{(1−η)/2} (1−x)^{(1+η)/2} (z/(1−z))^η )^{−1}`
(17) (SSRN 3408260, p.13, PDF 13), with `η` given. -/
noncomputable def aCoef (η x z : ℝ) : ℝ :=
  (x ^ ((1 + η) / 2) * (1 - x) ^ ((1 - η) / 2)
    - x ^ ((1 - η) / 2) * (1 - x) ^ ((1 + η) / 2) * (z / (1 - z)) ^ η)⁻¹

/-- `b(x, z) := ( x^{(1−η)/2} (1−x)^{(1+η)/2} − x^{(1+η)/2} (1−x)^{(1−η)/2} ((1−z)/z)^η )^{−1}`
(18) (SSRN 3408260, p.13, PDF 13), with `η` given. -/
noncomputable def bCoef (η x z : ℝ) : ℝ :=
  (x ^ ((1 - η) / 2) * (1 - x) ^ ((1 + η) / 2)
    - x ^ ((1 + η) / 2) * (1 - x) ^ ((1 - η) / 2) * ((1 - z) / z) ^ η)⁻¹

/-- `ξ₁(y) := y min{S₁, µ_H} + (1 − y) min{S₁, µ_L}` (19) (SSRN 3408260, p.13, PDF 13). -/
noncomputable def xi1 (p : Params) (S1 y : ℝ) : ℝ :=
  y * min S1 p.muH + (1 - y) * min S1 p.muL

/-- `ξ₂(y) := y min{S₁, µ_{1,H}} + (1 − y) min{S₁, µ_{1,L}}` (20) (SSRN 3408260, p.13, PDF 13). -/
noncomputable def xi2 (p : Params) (S1 y : ℝ) : ℝ :=
  y * min S1 p.mu1H + (1 - y) * min S1 p.mu1L

/-- `H₀(S₁, y₀) := y₀ min{S₁, µ_{1,H}}/λ + (1 − y₀) min{S₁, µ_{1,L}}/λ − c₁S₁` (22)
(SSRN 3408260, p.14, PDF 14). -/
noncomputable def H0 (p : Params) (S1 y0 : ℝ) : ℝ :=
  y0 * min S1 p.mu1H / p.lam + (1 - y0) * min S1 p.mu1L / p.lam - p.c1 * S1

/-- `φ_{ℓ*}(y₀; S₁) = a(ℓ, h) y₀^{(1+η)/2} (1−y₀)^{(1−η)/2} + b(ℓ, h) y₀^{(1−η)/2} (1−y₀)^{(1+η)/2}`
(24) (SSRN 3408260, p.14, PDF 14), for thresholds `(ℓ, h)` and `η = η(S₁)`. -/
noncomputable def phiL (p : Params) (σ S1 ℓ h y0 : ℝ) : ℝ :=
  aCoef (eta p σ S1) ℓ h * y0 ^ ((1 + eta p σ S1) / 2) * (1 - y0) ^ ((1 - eta p σ S1) / 2)
    + bCoef (eta p σ S1) ℓ h * y0 ^ ((1 - eta p σ S1) / 2) * (1 - y0) ^ ((1 + eta p σ S1) / 2)

/-- `φ_{h*}(y₀; S₁) = a(h, ℓ) y₀^{(1+η)/2} (1−y₀)^{(1−η)/2} + b(h, ℓ) y₀^{(1−η)/2} (1−y₀)^{(1+η)/2}`
(25) (SSRN 3408260, p.14, PDF 14), for thresholds `(ℓ, h)` and `η = η(S₁)`. -/
noncomputable def phiH (p : Params) (σ S1 ℓ h y0 : ℝ) : ℝ :=
  aCoef (eta p σ S1) h ℓ * y0 ^ ((1 + eta p σ S1) / 2) * (1 - y0) ^ ((1 - eta p σ S1) / 2)
    + bCoef (eta p σ S1) h ℓ * y0 ^ ((1 - eta p σ S1) / 2) * (1 - y0) ^ ((1 + eta p σ S1) / 2)

/-- `H₁(S₁, y₀) = −(ξ₁(ℓ) − ξ₂(ℓ))/λ · φ_{ℓ*}(y₀; S₁) − (ξ₁(h) − ξ₂(h))/λ · φ_{h*}(y₀; S₁)
+ ξ₁(y₀)/λ − c₁S₁` (23) (SSRN 3408260, p.14, PDF 14), with the thresholds `(ℓ, h)` (the paper's
`(ℓ*(S₁), h*(S₁))`) as explicit arguments. -/
noncomputable def H1 (p : Params) (σ S1 ℓ h y0 : ℝ) : ℝ :=
  -((xi1 p S1 ℓ - xi2 p S1 ℓ) / p.lam) * phiL p σ S1 ℓ h y0
    - (xi1 p S1 h - xi2 p S1 h) / p.lam * phiH p σ S1 ℓ h y0
    + xi1 p S1 y0 / p.lam - p.c1 * S1

/-- `f₁(y) := y^{(1+η)/2} (1−y)^{(1−η)/2}` (SSRN 3408260, proof of Theorem 4, Step A, p.ec24,
PDF 56). -/
noncomputable def f1 (η y : ℝ) : ℝ := y ^ ((1 + η) / 2) * (1 - y) ^ ((1 - η) / 2)

/-- `f₂(y) := y^{(1−η)/2} (1−y)^{(1+η)/2}` (SSRN 3408260, proof of Theorem 4, Step A, p.ec24,
PDF 56). -/
noncomputable def f2 (η y : ℝ) : ℝ := y ^ ((1 - η) / 2) * (1 - y) ^ ((1 + η) / 2)

end CompInvestBayes



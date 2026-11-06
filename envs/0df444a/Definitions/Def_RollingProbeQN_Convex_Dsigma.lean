-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Dsigma
-- name    : RollingProbeQN_Convex_Dsigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:38.147197+00:00
-- url     : https://prove2.me/theorems/90a5493e-df6c-403c-8e61-d01557f53ab9
-- title:
--   The $\sigma$-constants $c_0,m_\sigma,p_\sigma,e_\sigma,\alpha_\sigma,\beta_\sigma,d_\sigma,D_\sigma$ of (58)–(65)
-- statement:
--   The constants of the proof of Theorem 3.1, each depending only on $\sigma\in(0,1)$:
--
--   $$c_0=1+\log2,\qquad m_\sigma=(1+C_x)c_0,\qquad p_\sigma=m_\sigma+\sqrt{\frac{c_0}{1-\sigma^2}},\qquad e_\sigma=2p_\sigma+2,$$
--
--   $$\alpha_\sigma=\frac{10e_\sigma}{\sigma}+\Big(\frac{15}{\sigma}+\frac12\sqrt{\frac{10}{\sigma}}\Big)m_\sigma+\sqrt{\frac5\sigma}\Big(\frac{\sqrt{C_x}}{2}+\sqrt{e_\sigma m_\sigma}\Big),\qquad \beta_\sigma=\sqrt{\frac5\sigma}\,\frac{\sqrt{1+\sigma}}{\sigma^{1/4}(1-\sigma^2)^{1/4}},$$
--
--   $$d_\sigma=\max\{(16\alpha_\sigma)^{1/3},(16\beta_\sigma)^{4/9}\},\qquad D_\sigma=\frac{d_\sigma}{1-2^{-1/3}} .$$
--
--   They give the explicit constant $\max\{2/\sigma,D_\sigma^3/2\}$ of the rate (68).
--
--   **Formalization Note** The chain of constants shares one module; `Dsigma` is $D_\sigma$, and $c_0,m_\sigma,\dots,d_\sigma$ are `c0`, `msigma`, `psigma`, `esigma`, `alphasigma`, `betasigma`, `dsigma`.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, (58) p. 49, (60) and (63) p. 50, (65) p. 51

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Cx

namespace RollingProbeQN.Convex

/-- **The constants `c₀, m_σ, p_σ` of (58), `e_σ` of (60), `α_σ, β_σ` of (63) and `d_σ, D_σ` of
(65).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Appendix E.3, (58) p. 49, (60) and (63) p. 50, (65) p. 51:
"`c0 = 1 + log 2`, `mσ = (1 + Cx)c0`, `pσ = mσ + √(c0/(1 − σ²))`"; "Set `eσ = 2pσ + 2`";
"`ασ = 10eσ/σ + (15/σ + ½√(10/σ)) mσ + √(5/σ) (√Cx/2 + √(eσ mσ))`,
`βσ = √(5/σ) √(1 + σ)/(σ^{1/4}(1 − σ²)^{1/4})`"; "`dσ = max{(16ασ)^{1/3}, (16βσ)^{4/9}}`,
`Dσ = dσ/(1 − 2^{−1/3})`".

All depend only on `σ`. This module holds the chain of constants; `Dsigma` is `D_σ`.

**Formalization Note.** The constants form one chain, so they share this module. Real powers
`rpow` are applied to positive bases for `σ ∈ (0, 1)`. -/
noncomputable def c0 : ℝ := 1 + Real.log 2

/-- `m_σ = (1 + C_x) c₀`, (58), p. 49. -/
noncomputable def msigma (σ : ℝ) : ℝ := (1 + Cx σ) * c0

/-- `p_σ = m_σ + √(c₀/(1 − σ²))`, (58), p. 49. -/
noncomputable def psigma (σ : ℝ) : ℝ := msigma σ + Real.sqrt (c0 / (1 - σ ^ 2))

/-- `e_σ = 2 p_σ + 2`, p. 50. -/
noncomputable def esigma (σ : ℝ) : ℝ := 2 * psigma σ + 2

/-- `α_σ`, (63), p. 50. -/
noncomputable def alphasigma (σ : ℝ) : ℝ :=
  10 * esigma σ / σ + (15 / σ + 1 / 2 * Real.sqrt (10 / σ)) * msigma σ
    + Real.sqrt (5 / σ) * (Real.sqrt (Cx σ) / 2 + Real.sqrt (esigma σ * msigma σ))

/-- `β_σ`, (63), p. 50. -/
noncomputable def betasigma (σ : ℝ) : ℝ :=
  Real.sqrt (5 / σ) * (Real.sqrt (1 + σ) / (σ ^ ((1 : ℝ) / 4) * (1 - σ ^ 2) ^ ((1 : ℝ) / 4)))

/-- `d_σ = max{(16α_σ)^{1/3}, (16β_σ)^{4/9}}`, (65), p. 51. -/
noncomputable def dsigma (σ : ℝ) : ℝ :=
  max ((16 * alphasigma σ) ^ ((1 : ℝ) / 3)) ((16 * betasigma σ) ^ ((4 : ℝ) / 9))

/-- `D_σ = d_σ/(1 − 2^{−1/3})`, (65), p. 51. -/
noncomputable def Dsigma (σ : ℝ) : ℝ := dsigma σ / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 3))

end RollingProbeQN.Convex



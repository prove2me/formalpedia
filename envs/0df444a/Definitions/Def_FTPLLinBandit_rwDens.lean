-- Prove2me | Definitions.Def_FTPLLinBandit_rwDens
-- name    : FTPLLinBandit_rwDens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:29.143211+00:00
-- url     : https://prove2.me/theorems/dcba603a-56e4-4df3-b301-0b2c7938c469
-- title:
--   Random-weighting density $\rho_t(z)=\mathbb E_{\xi}[\rho_1(z-\sum_\tau\xi_\tau\hat\theta_\tau)]$
-- statement:
--   Let $\rho_1$ be a density on $\mathbb R^d$, $\varphi$ a density on $\mathbb R$, and $\hat\theta_1,\dots,\hat\theta_{t-1}\in\mathbb R^d$. The **random-weighting density** is
--   $$\rho_t(z)=\mathbb E_{\xi_1,\dots,\xi_{t-1}\overset{\text{iid}}{\sim}\varphi}\Big[\rho_1\Big(z-\sum_{\tau=1}^{t-1}\xi_\tau\hat\theta_\tau\Big)\Big]=\int_{\mathbb R^{t-1}}\prod_{\tau}\varphi(\xi_\tau)\,\rho_1\Big(z-\sum_\tau\xi_\tau\hat\theta_\tau\Big)\,d\xi,$$
--   the density of $Z=Z'+\sum_\tau\xi_\tau\hat\theta_\tau$ with $Z'\sim\rho_1$ and $\xi_\tau\sim\varphi$ independent.
--
--   **Formalization Note** The past is a list of length $t$ indexed from $0$, so it gives the paper's $\rho_{t+1}$; the empty list gives $\rho_1$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Figure 2, Option 1, p.8

import Mathlib

open MeasureTheory

namespace FTPLLinBandit

/-- **The random-weighting density.** Wei, arXiv:2610.17818, Figure 2, Option 1, p.8: "Define
Z ∼ ρ_t to be equivalent to independently drawing Z′ ∼ ρ₁ and ξ_τ ∼ φ for all τ < t, and setting
Z = Z′ + ∑_{τ=1}^{t−1} ξ_τ θ̂_τ. Equivalently, ρ_t(z) = E_{ξ₁∼φ,…,ξ_{t−1}∼φ}[ρ₁(z − ∑ ξ_τ θ̂_τ)]."

For an initializer density `ρ₁`, a scalar density `φ` and past estimates `θs : Fin t → ℝ^d`,
`rwDens ρ₁ φ θs z = ∫_{ℝ^t} (∏_i φ(ξ_i)) ρ₁(z − ∑_i ξ_i θs_i) dξ`.

**Formalization Note.** The past estimates are indexed from `0` (`θs i` is the paper's
`θ̂_{i+1}`), so a list of length `t` gives the paper's `ρ_{t+1}`; the empty list gives `ρ₁`
(`ℝ^0` is a point of Lebesgue measure `1`). The expectation over `t` independent `φ`-weights is
the Lebesgue integral against the product density. -/
noncomputable def rwDens {d t : ℕ} (ρ₁ : EuclideanSpace ℝ (Fin d) → ℝ) (φ : ℝ → ℝ)
    (θs : Fin t → EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ ξ : Fin t → ℝ, (∏ i, φ (ξ i)) * ρ₁ (z - ∑ i, ξ i • θs i)

end FTPLLinBandit



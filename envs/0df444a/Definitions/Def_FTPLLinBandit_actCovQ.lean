-- Prove2me | Definitions.Def_FTPLLinBandit_actCovQ
-- name    : FTPLLinBandit_actCovQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:44.101199+00:00
-- url     : https://prove2.me/theorems/b813b6fb-1499-4e4a-b597-ea6ee8fa0dee
-- title:
--   Action covariance $M=\operatorname{Cov}(p)$ as a quadratic form
-- statement:
--   For an argmax selection $x$, a perturbation density $\rho$ and a point $\Theta$, let $p$ be the law of $x(\Theta+Z)$, $Z\sim\rho$, with mean $\mu$. The **action covariance** is $M=\operatorname{Cov}(p)=\mathbb E_{a\sim p}[(a-\mu)(a-\mu)^\top]$; as a quadratic form,
--   $$u^\top Mu=\int_{\mathbb R^d}\rho(z)\,\big\langle x(\Theta+z)-\mu,\,u\big\rangle^2\,dz,\qquad u\in\mathbb R^d .$$
--   With $\rho=\rho_t$, $\Theta=\hat\Theta_t$ it is the paper's $M_t$, which enters the stability bounds through $\hat\theta_t^\top M_t\hat\theta_t$.
--
--   **Formalization Note** The paper uses $M_t$ only through $\hat\theta^\top M_t\hat\theta$, so the matrix is represented by its quadratic form.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, §5, p.10

import Mathlib
import Definitions.Def_FTPLLinBandit_actMean

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **The action covariance `M_t = Cov(p_t)` as a quadratic form.** Wei, arXiv:2610.17818, §5,
p.10: "M_t = Cov(p_t) = E_{a∼p_t}[(a − µ_t)(a − µ_t)ᵀ]", where `p_t` is the law of `x(Θ̂_t + Z)`,
`Z ∼ ρ_t`.

`actCovQ x ρ Θ u = ∫ ρ(z) ⟨x(Θ + z) − µ, u⟩² dz = uᵀ M u`, with `µ = actMean x ρ Θ`.

**Formalization Note.** The paper uses `M_t` only through `θ̂ᵀ M_t θ̂`, so the covariance matrix is
represented by its quadratic form (`uᵀMu` for every `u` determines the symmetric `M`). -/
noncomputable def actCovQ {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (Θ u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ z, ρ z * ⟪x (Θ + z) - actMean x ρ Θ, u⟫_ℝ ^ 2

end FTPLLinBandit



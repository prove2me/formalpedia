-- Prove2me | Definitions.Def_WassKF_Reform_minimaxValue
-- name    : WassKF_Reform_minimaxValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:11:22.557262+00:00
-- url     : https://prove2.me/theorems/d4b03646-12a1-4e0e-99e3-3b80fcd61cb2
-- title:
--   (2), p. 3 — the optimal value $\inf_{\psi\in\mathcal L}\sup_{\mathbb Q\in\mathcal P}\mathbb E^{\mathbb Q}[\|x-\psi(y)\|^2]$
-- statement:
--   Let $\mathcal P$ be the Wasserstein ambiguity set of normal distributions of radius $\rho$ around $\mathbb P = \mathcal N_d(\mu, \Sigma)$, and let $\mathcal L$ be the family of all measurable functions $\psi : \mathbb R^m \to \mathbb R^n$. The **minimax value** is the optimal value of the distributionally robust minimum mean square error problem (2),
--
--   $$
--   \inf_{\psi \in \mathcal L} \; \sup_{\mathbb Q \in \mathcal P} \; \mathbb E^{\mathbb Q}\bigl[\|x - \psi(y)\|^2\bigr] \in [0, \infty],
--   $$
--
--   the left side of the minimax equality (4). A distributionally robust minimum mean square error estimator is an estimator $\psi \in \mathcal L$ attaining the outer infimum.
--
--   **Formalization Note** The infimum is `⨅ ψ, ⨅ (_ : Measurable ψ), …` and the supremum is `⨆ Q, ⨆ (_ : Q ∈ GaussianBall μ Sig ρ), …`, both in `ENNReal`, with the expectation `expectedLoss`.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 3, (2) and left side of (4)

import Mathlib
import Definitions.Def_WassKF_Reform_GaussianBall
import Definitions.Def_WassKF_Reform_expectedLoss

open MeasureTheory

namespace WassKF.Reform

/-- The optimal value of the minimax problem (2) over the ambiguity set (3), the left side of (4)
in Shafieezadeh-Abadeh et al. (arXiv:1809.08830v3, p. 3):
`inf_{ψ ∈ ℒ} sup_{Q ∈ 𝒫} E^Q[‖x − ψ(y)‖²]`, where `ℒ` is the family of all measurable functions
`ℝ^m → ℝ^n` and `𝒫 = GaussianBall μ Sig ρ`. Valued in `[0, ∞]`. -/
noncomputable def minimaxValue {n m : ℕ} (μ : EuclideanSpace ℝ (Fin n ⊕ Fin m))
    (Sig : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (ρ : ℝ) : ENNReal :=
  ⨅ (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (_ : Measurable ψ),
    ⨆ (Q : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin m))) (_ : Q ∈ GaussianBall μ Sig ρ),
      expectedLoss ψ Q

end WassKF.Reform



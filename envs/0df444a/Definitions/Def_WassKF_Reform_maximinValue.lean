-- Prove2me | Definitions.Def_WassKF_Reform_maximinValue
-- name    : WassKF_Reform_maximinValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:06.877983+00:00
-- url     : https://prove2.me/theorems/84bcd9be-c310-4f4c-847e-786882b256bf
-- title:
--   (4), p. 3 — nature's value $\sup_{\mathbb Q\in\mathcal P}\inf_{\psi\in\mathcal L}\mathbb E^{\mathbb Q}[\|x-\psi(y)\|^2]$
-- statement:
--   With $\mathcal P$ the Wasserstein ambiguity set of normal distributions of radius $\rho$ around $\mathbb P = \mathcal N_d(\mu, \Sigma)$ and $\mathcal L$ the family of all measurable functions $\psi : \mathbb R^m \to \mathbb R^n$, the **maximin value** is the optimal value of nature's problem,
--
--   $$
--   \sup_{\mathbb Q \in \mathcal P} \; \inf_{\psi \in \mathcal L} \; \mathbb E^{\mathbb Q}\bigl[\|x - \psi(y)\|^2\bigr] \in [0, \infty],
--   $$
--
--   the right side of the minimax equality (4). A distribution $\mathbb Q^\star \in \mathcal P$ attaining the outer supremum is a least favorable prior.
--
--   **Formalization Note** Same conventions as `WassKF.Reform.minimaxValue`, with the order of the two optimizations exchanged.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 3, right side of (4); Remark 2.4

import Mathlib
import Definitions.Def_WassKF_Reform_GaussianBall
import Definitions.Def_WassKF_Reform_expectedLoss

open MeasureTheory

namespace WassKF.Reform

/-- The optimal value of nature's problem, the right side of (4) in Shafieezadeh-Abadeh et al.
(arXiv:1809.08830v3, p. 3): `sup_{Q ∈ 𝒫} inf_{ψ ∈ ℒ} E^Q[‖x − ψ(y)‖²]`, where `ℒ` is the family of
all measurable functions `ℝ^m → ℝ^n` and `𝒫 = GaussianBall μ Sig ρ`. Valued in `[0, ∞]`. -/
noncomputable def maximinValue {n m : ℕ} (μ : EuclideanSpace ℝ (Fin n ⊕ Fin m))
    (Sig : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (ρ : ℝ) : ENNReal :=
  ⨆ (Q : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin m))) (_ : Q ∈ GaussianBall μ Sig ρ),
    ⨅ (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (_ : Measurable ψ),
      expectedLoss ψ Q

end WassKF.Reform



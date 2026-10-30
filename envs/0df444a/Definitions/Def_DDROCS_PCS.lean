-- Prove2me | Definitions.Def_DDROCS_PCS
-- name    : DDROCS_PCS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:30:37.843032+00:00
-- url     : https://prove2.me/theorems/83674210-3efa-4953-b46f-29f7af6f6521
-- title:
--   Shawe-Taylor–Cristianini confidence region $\mathcal P^{CS}$
-- statement:
--   Let $R \in \mathbb R$, $\hat\mu \in \mathbb R^d$, $\hat\Sigma \in \mathbb R^{d\times d}$ and $\Gamma_1, \Gamma_2 \in \mathbb R$. Write $\Theta(R)$ for the set of Borel probability measures on $\mathbb R^d$ supported on the closed ball of radius $R$ about the origin. Then
--
--   $$
--   \mathcal P^{CS} \;=\; \Bigl\{\mathbb P \in \Theta(R) \;:\; \bigl\|\mathbb E^{\mathbb P}[\tilde u] - \hat\mu\bigr\|_2 \le \Gamma_1 \ \text{ and }\ \bigl\|\mathbb E^{\mathbb P}[\tilde u\tilde u^\top] - \mathbb E^{\mathbb P}[\tilde u]\mathbb E^{\mathbb P}[\tilde u^\top] - \hat\Sigma\bigr\|_F \le \Gamma_2 \Bigr\}.
--   $$
--
--   With $\hat\mu, \hat\Sigma$ the sample mean and covariance and suitable thresholds (Theorem 9 of the paper, after Shawe-Taylor and Cristianini, or bootstrapped ones), $\mathcal P^{CS}$ is a confidence region for the unknown law $\mathbb P^*$: it contains $\mathbb P^*$ with probability at least $1-\alpha$ over the sample.
--
--   **Formalization Note** The centre, the matrix and the thresholds are parameters, so the same region serves every choice of thresholds. "Supported on the ball of radius $R$" is $\mathbb P(\bar B(0,R)) = 1$. $\|\cdot\|_2$ is the Euclidean norm of `EuclideanSpace ℝ (Fin d)` and $\mathbb E^{\mathbb P}[\tilde u]$ the Bochner integral of the identity.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 9, p. 24 (definition of P^CS and Θ(R)); used in Theorem 10, p. 25

import Mathlib
import Definitions.Def_DDROCS_covMat
import Definitions.Def_DDROCS_frobNorm
open MeasureTheory

namespace DDROCS

/-- **The Shawe-Taylor–Cristianini confidence region `P^CS`.**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 9, p. 24:
"`P^CS = {P ∈ Θ(R) : ‖E^P[ũ] − μ̂‖₂ ≤ Γ1(α/2,N) and ‖E^P[ũũᵀ] − E^P[ũ]E^P[ũᵀ] − Σ̂‖_F ≤
Γ2(α/2,N)}`, … and `Θ(R)` denotes the set of Borel probability measures supported on the ball of
radius `R`." Theorem 10 (p. 25) uses the same region with other thresholds.

`PCS R μhat Sigmahat Γ₁ Γ₂` is the set of probability measures `P` on `ℝ^d` with
`P(closedBall 0 R) = 1`, `‖E^P[ũ] − μhat‖ ≤ Γ₁` and `‖covMat P − Sigmahat‖_F ≤ Γ₂`.

**Formalization Note.** The centre `μ̂`, the matrix `Σ̂` and the thresholds are parameters, so the
same region serves Theorem 9's thresholds and the bootstrapped ones. "Supported on the ball of
radius `R`" is read as `P(closedBall 0 R) = 1` (the ball about the origin, closed because a
support is closed). `‖·‖` on `ℝ^d = EuclideanSpace ℝ (Fin d)` is the Euclidean norm `‖·‖₂`;
`E^P[ũ]` is the Bochner integral of the identity. Measures on `ℝ^d` are Borel. -/
def PCS {d : ℕ} (R : ℝ) (μhat : EuclideanSpace ℝ (Fin d))
    (Sigmahat : Matrix (Fin d) (Fin d) ℝ) (Γ₁ Γ₂ : ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin d))) :=
  {P | IsProbabilityMeasure P ∧ P (Metric.closedBall 0 R) = 1 ∧
    ‖(∫ u, u ∂P) - μhat‖ ≤ Γ₁ ∧ frobNorm (covMat P - Sigmahat) ≤ Γ₂}

end DDROCS



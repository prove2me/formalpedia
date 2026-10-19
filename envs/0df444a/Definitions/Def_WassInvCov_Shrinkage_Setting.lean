-- Prove2me | Definitions.Def_WassInvCov_Shrinkage_Setting
-- name    : WassInvCov_Shrinkage_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:52.688576+00:00
-- url     : https://prove2.me/theorems/6a0cda00-a399-40a9-bac2-5172acfab2fb
-- title:
--   Definitions 1.1, 2.3, (5)–(8), (16a)–(16b), pp. 3–12 — Gaussian Wasserstein ball 𝒫⁰_ρ, worst-case expectation g, problem (5), programs (6), (8), 𝕎_S
-- statement:
--   This file fixes the objects of the Gaussian–Wasserstein robust estimation problem for a precision matrix. Throughout, $p$ is the dimension, $\mathbb R^p$ carries the Euclidean norm, $\mathbb S^p_+$ and $\mathbb S^p_{++}$ are the positive semidefinite and positive definite symmetric $p\times p$ matrices, and $\langle A,B\rangle=\operatorname{Tr}[A^\top B]$ is the trace inner product.
--
--   1. **Induced metric (Definition 2.3).** For $\Sigma_1,\Sigma_2\in\mathbb S^p_+$,
--   $$\mathbb W_S(\Sigma_1,\Sigma_2)=\sqrt{\operatorname{Tr}[\Sigma_1]+\operatorname{Tr}[\Sigma_2]-2\operatorname{Tr}\Big[\sqrt{\sqrt{\Sigma_2}\,\Sigma_1\sqrt{\Sigma_2}}\Big]},$$
--   where $\sqrt{\cdot}$ is the positive semidefinite square root.
--   2. **Ambiguity set (pp. 6–7).** For $\rho\in\mathbb R$ and $\widehat\Sigma\in\mathbb S^p_+$, $\mathcal P^0_\rho$ is the set of centred normal distributions $\mathbb Q=\mathcal N(0,S)$, $S\in\mathbb S^p_+$ (degenerate covariances allowed), whose type-2 Wasserstein distance (Definition 1.1, the infimum over couplings of $(\int\|\xi_1-\xi_2\|^2\,d\Pi)^{1/2}$) to the nominal distribution $\widehat{\mathbb P}=\mathcal N(0,\widehat\Sigma)$ is at most $\rho$.
--   3. **Worst-case expectation (7).** $g(\widehat\Sigma,X)=\sup_{\mathbb Q\in\mathcal P^0_\rho}\mathbb E^{\mathbb Q}[\langle\xi\xi^\top,X\rangle]$.
--   4. **Problem (5).** For a set $\mathcal X\subseteq\mathbb S^p_{++}$ of admissible precision matrices,
--   $$\mathcal J(\widehat\Sigma)=\inf_{X\in\mathcal X}\Big\{-\log\det X+g(\widehat\Sigma,X)\Big\}.$$
--   5. **Program (6).** The objective $f(X,\gamma)=-\log\det X+\gamma(\rho^2-\operatorname{Tr}[\widehat\Sigma])+\gamma^2\langle(\gamma I-X)^{-1},\widehat\Sigma\rangle$ and its infimum over $X\in\mathcal X$, $\gamma\in\mathbb R$ with $\gamma I\succ X\succ0$.
--   6. **Program (8).** $\inf_\gamma\ \gamma(\rho^2-\operatorname{Tr}[\widehat\Sigma])+\gamma^2\langle(\gamma I-X)^{-1},\widehat\Sigma\rangle$ subject to $\gamma I\succ X$.
--   7. **Equations (16a)–(16b).** For eigenvalues $\lambda_1,\dots,\lambda_p$ and $\gamma\in\mathbb R$,
--   $$\varphi(\gamma)=\Big(\rho^2-\tfrac12\sum_{i=1}^p\lambda_i\Big)\gamma-p+\tfrac12\sum_{i=1}^p\sqrt{\lambda_i^2\gamma^2+4\lambda_i\gamma},\qquad x_i(\gamma)=\gamma\Big[1-\tfrac12\Big(\sqrt{\lambda_i^2\gamma^2+4\lambda_i\gamma}-\lambda_i\gamma\Big)\Big],$$
--   and the shrinkage estimator $X(\gamma)=\sum_{i=1}^p x_i(\gamma)\,v_iv_i^\top$ for eigenvectors $v_1,\dots,v_p$.
--
--   These are the objects of every statement of the mission: the goal (Theorem 3.1) is about problem (5) with $\mathcal X=\mathbb S^p_{++}$, and (6), (8) are its reformulations.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)`; $\mathcal N(0,S)$ is Mathlib's `multivariateGaussian 0 S`; the Wasserstein distance is the published coupling distance `WassersteinDRO.Gelbrich.wassersteinDistance 2` with values in $[0,\infty]$, compared with $\rho$ through `ENNReal.ofReal ρ`; $\sqrt{\cdot}$ is the published `psdSqrt` and $\langle\cdot,\cdot\rangle$ the published `WassMMSE.Sandwich.frob`. The suprema and infima $g$, $\mathcal J$, (6) and (8) are computed in the extended reals `EReal`, so an empty or unbounded set never produces a junk value. Every $\mathbb Q\in\mathcal P^0_\rho$ is Gaussian and has finite second moments, so the Bochner integral defining $\mathbb E^{\mathbb Q}[\langle\xi\xi^\top,X\rangle]$ is never the junk value of a non-integrable function. The matrix inverse $(\gamma I-X)^{-1}$ is only used under the constraint $\gamma I\succ X$, which sits inside the index of the infimum. Definition 2.1's density lacks a factor $\tfrac12$ in the exponent (a printed slip); the standard normal distribution is meant and used.
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, pp. 3–12, Definition 1.1 (p. 3), Definition 2.1 (p. 5), Definition 2.3 (p. 6), 𝒫⁰_ρ and (5) (pp. 6–7), (6)–(8) (p. 7), (16a)–(16b) (p. 12)

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_wassersteinDistance
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt
import Definitions.Def_WassMMSE_Sandwich_Programs

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- The metric `𝕎_S` on `𝕊^p_+` induced by the type-2 Wasserstein metric on centred normal
distributions (Definition 2.3, p. 6):
`𝕎_S(Σ₁, Σ₂) = √(Tr[Σ₁] + Tr[Σ₂] − 2 Tr[√(√Σ₂ Σ₁ √Σ₂)])`. Meaningful for `Σ₁, Σ₂ ⪰ 0`. -/
noncomputable def WS {p : ℕ} (S₁ S₂ : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  Real.sqrt (S₁.trace + S₂.trace - 2 * (WassersteinDRO.Gelbrich.psdSqrt
    (WassersteinDRO.Gelbrich.psdSqrt S₂ * S₁ * WassersteinDRO.Gelbrich.psdSqrt S₂)).trace)

/-- The Gaussian Wasserstein ambiguity set `𝒫⁰_ρ` (pp. 6–7): all centred normal distributions
`ℚ = 𝒩(0, S)`, `S ⪰ 0`, on `ℝ^p` whose type-2 Wasserstein distance (Definition 1.1) to the
nominal distribution `ℙ̂ = 𝒩(0, Σ̂)` is at most `ρ`. -/
noncomputable def ambiguitySet {p : ℕ} (ρ : ℝ) (Sh : Matrix (Fin p) (Fin p) ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin p))) :=
  {Q | ∃ S : Matrix (Fin p) (Fin p) ℝ, S.PosSemidef ∧ Q = multivariateGaussian 0 S ∧
    WassersteinDRO.Gelbrich.wassersteinDistance 2 Q (multivariateGaussian 0 Sh) ≤
      ENNReal.ofReal ρ}

/-- The worst-case expectation `g(Σ̂, X) = sup_{ℚ ∈ 𝒫⁰_ρ} 𝔼^ℚ[⟨ξξᵀ, X⟩]` of (7), p. 7, as an
`EReal` supremum. -/
noncomputable def worstCaseExp {p : ℕ} (ρ : ℝ) (Sh X : Matrix (Fin p) (Fin p) ℝ) : EReal :=
  ⨆ Q ∈ ambiguitySet ρ Sh,
    ((∫ ξ, WassMMSE.Sandwich.frob (Matrix.vecMulVec ξ.ofLp ξ.ofLp) X ∂Q : ℝ) : EReal)

/-- The objective of problem (5), p. 7: `−log det X + g(Σ̂, X)`. Meaningful for `X ≻ 0`. -/
noncomputable def robustObjective {p : ℕ} (ρ : ℝ) (Sh X : Matrix (Fin p) (Fin p) ℝ) : EReal :=
  ((-Real.log X.det : ℝ) : EReal) + worstCaseExp ρ Sh X

/-- The optimal value `𝒥(Σ̂) = inf_{X ∈ 𝒳} {−log det X + g(Σ̂, X)}` of problem (5), p. 7, for a set
`𝒳 ⊆ 𝕊^p_{++}` of admissible precision matrices, as an `EReal` infimum. -/
noncomputable def J {p : ℕ} (𝒳 : Set (Matrix (Fin p) (Fin p) ℝ)) (ρ : ℝ)
    (Sh : Matrix (Fin p) (Fin p) ℝ) : EReal :=
  ⨅ X ∈ 𝒳, robustObjective ρ Sh X

/-- The objective of the convex program (6), p. 7:
`−log det X + γ(ρ² − Tr[Σ̂]) + γ²⟨(γI − X)⁻¹, Σ̂⟩`. -/
noncomputable def obj6 {p : ℕ} (ρ : ℝ) (Sh X : Matrix (Fin p) (Fin p) ℝ) (γ : ℝ) : ℝ :=
  -Real.log X.det + γ * (ρ ^ 2 - Sh.trace) +
    γ ^ 2 * WassMMSE.Sandwich.frob (γ • (1 : Matrix (Fin p) (Fin p) ℝ) - X)⁻¹ Sh

/-- The optimal value of the convex program (6), p. 7: the infimum of `obj6` over
`X ∈ 𝒳`, `γ ∈ ℝ` with `γI ≻ X ≻ 0`, as an `EReal` infimum. -/
noncomputable def value6 {p : ℕ} (𝒳 : Set (Matrix (Fin p) (Fin p) ℝ)) (ρ : ℝ)
    (Sh : Matrix (Fin p) (Fin p) ℝ) : EReal :=
  ⨅ (X ∈ 𝒳) (γ : ℝ) (_ : (γ • (1 : Matrix (Fin p) (Fin p) ℝ) - X).PosDef ∧ X.PosDef),
    (obj6 ρ Sh X γ : EReal)

/-- The optimal value of the one-dimensional semidefinite program (8), p. 7:
`inf_γ γ(ρ² − Tr[Σ̂]) + γ²⟨(γI − X)⁻¹, Σ̂⟩` subject to `γI ≻ X`, as an `EReal` infimum. -/
noncomputable def sdp8 {p : ℕ} (ρ : ℝ) (Sh X : Matrix (Fin p) (Fin p) ℝ) : EReal :=
  ⨅ (γ : ℝ) (_ : (γ • (1 : Matrix (Fin p) (Fin p) ℝ) - X).PosDef),
    ((γ * (ρ ^ 2 - Sh.trace) +
      γ ^ 2 * WassMMSE.Sandwich.frob (γ • (1 : Matrix (Fin p) (Fin p) ℝ) - X)⁻¹ Sh : ℝ) : EReal)

/-- The left-hand side of the algebraic equation (16b), p. 12:
`φ(γ) = (ρ² − ½ Σᵢ λᵢ) γ − p + ½ Σᵢ √(λᵢ² γ² + 4 λᵢ γ)`. -/
noncomputable def phi16b {p : ℕ} (ρ : ℝ) (lam : Fin p → ℝ) (γ : ℝ) : ℝ :=
  (ρ ^ 2 - (1 / 2) * ∑ i, lam i) * γ - p +
    (1 / 2) * ∑ i, Real.sqrt (lam i ^ 2 * γ ^ 2 + 4 * lam i * γ)

/-- The eigenvalue map (16a), p. 12: `x_i = γ [1 − ½ (√(λᵢ² γ² + 4 λᵢ γ) − λᵢ γ)]`. -/
noncomputable def x16a {p : ℕ} (lam : Fin p → ℝ) (γ : ℝ) (i : Fin p) : ℝ :=
  γ * (1 - (1 / 2) * (Real.sqrt (lam i ^ 2 * γ ^ 2 + 4 * lam i * γ) - lam i * γ))

/-- The shrinkage estimator of Theorem 3.1, p. 12: `X = Σᵢ xᵢ vᵢ vᵢᵀ` with `xᵢ` from (16a) at `γ`,
for eigenvalues `λᵢ` and eigenvectors `vᵢ` of `Σ̂`. -/
noncomputable def shrinkageEstimator {p : ℕ} (lam : Fin p → ℝ)
    (v : Fin p → EuclideanSpace ℝ (Fin p)) (γ : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  ∑ i, x16a lam γ i • Matrix.vecMulVec (v i).ofLp (v i).ofLp

end WassInvCov.Shrinkage



-- Prove2me | Definitions.Def_WassMMSE_Sandwich_Setting
-- name    : WassMMSE_Sandwich_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:18:40.339986+00:00
-- url     : https://prove2.me/theorems/057f189e-49b0-47a6-a57d-22f1f19ab3b3
-- title:
--   §1–§4, pp. 1–16 — 𝓜(ℝ^d), estimators 𝓕 and 𝓐, average risk 𝓡, ambiguity sets 𝔹(ℙ̂), 𝔾(ℙ̂), 𝔹_𝒩(ℙ̂), and the optimal values of (1.7), (2.1), (3.1), (3.3)
-- statement:
--   This file fixes the estimation model of Nguyen, Shafieezadeh-Abadeh, Kuhn and Mohajerin Esfahani. An unknown parameter $x\in\mathbb R^n$ is observed through the linear measurement $y=Hx+w$, where $H\in\mathbb R^{m\times n}$ is known and $w\in\mathbb R^m$ is noise independent of $x$.
--
--   1. **Distributions with finite second moments.** $\mathcal M(\mathbb R^d)$ is the family of probability measures $\mathbb Q$ on $\mathbb R^d$ with $\mathbb E_{\mathbb Q}[\|\xi\|^2]<\infty$.
--   2. **Estimators.** $\mathcal F$ is the family of measurable maps $\psi:\mathbb R^m\to\mathbb R^n$ that grow at most linearly: there is $C>0$ with $\|\psi(y)\|\le C(1+\|y\|)$ for all $y$. The affine estimators are
--   $$\mathcal A=\{\psi\in\mathcal F:\ \exists A\in\mathbb R^{n\times m},\ b\in\mathbb R^n \text{ with } \psi(y)=Ay+b\ \forall y\}.$$
--   3. **Average risk.** For a joint distribution $\mathbb Q$ of $(x,w)$, $\mathcal R(\psi,\mathbb Q)=\mathbb E_{\mathbb Q}[\|x-\psi(Hx+w)\|^2]\in[0,\infty]$.
--   4. **Wasserstein ambiguity set** (1.8). Given nominal marginals $\widehat{\mathbb P}_x$, $\widehat{\mathbb P}_w$ and radii $\rho_x,\rho_w$,
--   $$\mathbb B(\widehat{\mathbb P})=\{\mathbb Q_x\times\mathbb Q_w:\ \mathbb Q_x\in\mathcal M(\mathbb R^n),\ \mathbb W(\mathbb Q_x,\widehat{\mathbb P}_x)\le\rho_x;\ \mathbb Q_w\in\mathcal M(\mathbb R^m),\ \mathbb W(\mathbb Q_w,\widehat{\mathbb P}_w)\le\rho_w\},$$
--   where $\mathbb W$ is the type-2 Wasserstein distance (Definition 1.1).
--   5. **Gelbrich ambiguity set** (p. 8). With nominal moments $(\widehat\mu_x,\widehat\Sigma_x)$, $(\widehat\mu_w,\widehat\Sigma_w)$, $\mathbb G(\widehat{\mathbb P})$ is the set of products $\mathbb Q_x\times\mathbb Q_w$ with $\mathbb Q_x\in\mathcal M(\mathbb R^n)$, $\mathbb Q_w\in\mathcal M(\mathbb R^m)$ whose mean–covariance pairs satisfy $\mathbb G((\mu_x,\Sigma_x),(\widehat\mu_x,\widehat\Sigma_x))\le\rho_x$ and $\mathbb G((\mu_w,\Sigma_w),(\widehat\mu_w,\widehat\Sigma_w))\le\rho_w$, where
--   $$\mathbb G((\mu_1,\Sigma_1),(\mu_2,\Sigma_2))=\sqrt{\|\mu_1-\mu_2\|^2+\operatorname{Tr}\big[\Sigma_1+\Sigma_2-2(\Sigma_2^{1/2}\Sigma_1\Sigma_2^{1/2})^{1/2}\big]}$$
--   is the Gelbrich distance (Definition 2.1).
--   6. **Normal ambiguity set** (p. 13). For normal nominal marginals $\widehat{\mathbb P}_x=\mathcal N(\widehat\mu_x,\widehat\Sigma_x)$ and $\widehat{\mathbb P}_w=\mathcal N(\widehat\mu_w,\widehat\Sigma_w)$, $\mathbb B_{\mathcal N}(\widehat{\mathbb P})$ is the set of products $\mathcal N(\widehat\mu_x,\Sigma_x)\times\mathcal N(\widehat\mu_w,\Sigma_w)$ with $\Sigma_x\succeq0$, $\Sigma_w\succ0$, $\mathbb W(\mathcal N(\widehat\mu_x,\Sigma_x),\widehat{\mathbb P}_x)\le\rho_x$ and $\mathbb W(\mathcal N(\widehat\mu_w,\Sigma_w),\widehat{\mathbb P}_w)\le\rho_w$. The means stay at their nominal values.
--   7. **Optimal values**, all in $[0,\infty]$: the Wasserstein MMSE problem (1.7) $\inf_{\psi\in\mathcal F}\sup_{\mathbb Q\in\mathbb B(\widehat{\mathbb P})}\mathcal R(\psi,\mathbb Q)$; its dual (3.1) $\sup_{\mathbb Q\in\mathbb B(\widehat{\mathbb P})}\inf_{\psi\in\mathcal F}\mathcal R(\psi,\mathbb Q)$; the Gelbrich MMSE problem (2.1) $\inf_{\psi\in\mathcal A}\sup_{\mathbb Q\in\mathbb G(\widehat{\mathbb P})}\mathcal R(\psi,\mathbb Q)$; and the dual over normal priors (3.3) $\sup_{\mathbb Q\in\mathbb B_{\mathcal N}(\widehat{\mathbb P})}\inf_{\psi\in\mathcal F}\mathcal R(\psi,\mathbb Q)$.
--
--   These objects are shared by every statement of the mission: the sandwich theorem compares (2.1) with (3.3), and the corollaries transfer the result to (1.7) and (3.1).
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. The risk is a lower Lebesgue integral of $\|x-\psi(Hx+w)\|^2$, valued in `ENNReal`, and all four optimal values are `ENNReal` infima and suprema restricted by membership predicates, so no junk value of a real `sSup` or Bochner integral enters. Means and covariances are the published Bochner-integral definitions `meanVector`, `covarianceMatrix`; they are used only for measures in $\mathcal M$, where they are the true moments (and $\Sigma=\mathbb E[xx^\top]-\mu\mu^\top$ equals the centred form). The Gelbrich condition is the published `meanCovarianceUncertaintySet` (squared form, equivalent for $\rho\ge0$), with the page's order $\widehat\Sigma^{1/2}\Sigma\widehat\Sigma^{1/2}$ and the published PSD square root `psdSqrt`. $\mathcal N(\mu,\Sigma)$ is Mathlib's `multivariateGaussian μ Σ`, the push-forward of the standard Gaussian under $\xi\mapsto\mu+\Sigma^{1/2}\xi$; for $\Sigma\succeq0$ this is the law of Definition 3.1 (whose printed density lacks the factor $\tfrac12$ in the exponent, a slip of the page). The parametrizations are: $\mathbb B$ by the nominal marginals, $\mathbb G$ by the nominal moments, $\mathbb B_{\mathcal N}$ by the nominal normal parameters, since each set depends on exactly that data. The membership $\mathbb Q_x\times\mathbb Q_w\in\mathcal M\times\mathcal M$ in $\mathbb B_{\mathcal N}$ is kept as on the page, although it holds automatically for normal laws.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, pp. 1–4 (𝓕, (1.3), 𝓡, Definition 1.1, (1.7), (1.8)), pp. 7–8 (Definition 2.1, 𝔾(ℙ̂), (2.1)), pp. 12–13 (Definition 3.1, (3.1), (3.2), 𝔹_𝒩(ℙ̂), (3.3))

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_wassersteinDistance
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector
import Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix
import Definitions.Def_WassersteinDRO_Gelbrich_meanCovarianceUncertaintySet

open MeasureTheory ProbabilityTheory

namespace WassMMSE.Sandwich

/-- `ℝ^d`, the Euclidean space of dimension `d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `Q ∈ 𝓜(ℝ^d)` (Nguyen et al., arXiv:1911.03539v2, p. 3): `Q` is a probability measure on `ℝ^d`
with finite second-order moments. -/
def HasFiniteSecondMoment {d : ℕ} (Q : Measure (E d)) : Prop :=
  IsProbabilityMeasure Q ∧ MemLp (fun x : E d => x) 2 Q

/-- `ψ ∈ 𝓕` (p. 1): an estimator of `x ∈ ℝⁿ` given `y ∈ ℝᵐ` is a measurable function
`ψ : ℝᵐ → ℝⁿ` that grows at most linearly, i.e. `‖ψ(y)‖ ≤ C(1 + ‖y‖)` for some `C > 0`. -/
def IsEstimator {n m : ℕ} (ψ : E m → E n) : Prop :=
  Measurable ψ ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, ‖ψ y‖ ≤ C * (1 + ‖y‖)

/-- `ψ ∈ 𝓐` (1.3), p. 2: an estimator that is affine, `ψ(y) = A y + b` with `A ∈ ℝ^{n×m}`,
`b ∈ ℝⁿ`. -/
def IsAffineEstimator {n m : ℕ} (ψ : E m → E n) : Prop :=
  IsEstimator ψ ∧
    ∃ (A : Matrix (Fin n) (Fin m) ℝ) (b : E n), ∀ y, ψ y = Matrix.toEuclideanLin A y + b

/-- The average risk `𝓡(ψ, ℚ) = E_ℚ[‖x − ψ(Hx + w)‖²]` (p. 3) of an estimator `ψ` under a joint
distribution `ℚ` of `(x, w) ∈ ℝⁿ × ℝᵐ`, where `y = Hx + w` (1.1). A lower Lebesgue integral,
valued in `[0, ∞]`. -/
noncomputable def risk {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ψ : E m → E n)
    (Q : Measure (E n × E m)) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (‖p.1 - ψ (Matrix.toEuclideanLin H p.1 + p.2)‖ ^ 2) ∂Q

/-- The Wasserstein ambiguity set `𝔹(ℙ̂)` (1.8), p. 4: all products `ℚ_x × ℚ_w` with
`ℚ_x ∈ 𝓜(ℝⁿ)`, `𝕎(ℚ_x, ℙ̂_x) ≤ ρ_x` and `ℚ_w ∈ 𝓜(ℝᵐ)`, `𝕎(ℚ_w, ℙ̂_w) ≤ ρ_w`, around the nominal
marginals `ℙ̂_x`, `ℙ̂_w`. -/
def wassersteinSet {n m : ℕ} (ρx ρw : ℝ) (Px : Measure (E n)) (Pw : Measure (E m)) :
    Set (Measure (E n × E m)) :=
  {Q | ∃ (Qx : Measure (E n)) (Qw : Measure (E m)),
    HasFiniteSecondMoment Qx ∧ HasFiniteSecondMoment Qw ∧
    WassersteinDRO.Gelbrich.wassersteinDistance 2 Qx Px ≤ ENNReal.ofReal ρx ∧
    WassersteinDRO.Gelbrich.wassersteinDistance 2 Qw Pw ≤ ENNReal.ofReal ρw ∧
    Q = Qx.prod Qw}

/-- The Gelbrich ambiguity set `𝔾(ℙ̂)`, p. 8: all products `ℚ_x × ℚ_w` with `ℚ_x ∈ 𝓜(ℝⁿ)`,
`ℚ_w ∈ 𝓜(ℝᵐ)` whose mean–covariance pairs lie within Gelbrich distance `ρ_x`, `ρ_w` of the
nominal moments `(μ̂_x, Σ̂_x)`, `(μ̂_w, Σ̂_w)` (Definition 2.1, p. 7). -/
def gelbrichSet {n m : ℕ} (ρx ρw : ℝ) (μx : E n) (Shx : Matrix (Fin n) (Fin n) ℝ)
    (μw : E m) (Shw : Matrix (Fin m) (Fin m) ℝ) : Set (Measure (E n × E m)) :=
  {Q | ∃ (Qx : Measure (E n)) (Qw : Measure (E m)),
    HasFiniteSecondMoment Qx ∧ HasFiniteSecondMoment Qw ∧
    (WassersteinDRO.Gelbrich.meanVector Qx, WassersteinDRO.Gelbrich.covarianceMatrix Qx) ∈
      WassersteinDRO.Gelbrich.meanCovarianceUncertaintySet ρx μx Shx ∧
    (WassersteinDRO.Gelbrich.meanVector Qw, WassersteinDRO.Gelbrich.covarianceMatrix Qw) ∈
      WassersteinDRO.Gelbrich.meanCovarianceUncertaintySet ρw μw Shw ∧
    Q = Qx.prod Qw}

/-- The restricted ambiguity set `𝔹_𝒩(ℙ̂)`, p. 13, for normal nominal marginals
`ℙ̂_x = 𝒩(μ̂_x, Σ̂_x)`, `ℙ̂_w = 𝒩(μ̂_w, Σ̂_w)` (3.2): all products `𝒩(μ̂_x, Σ_x) × 𝒩(μ̂_w, Σ_w)` in
`𝓜(ℝⁿ) × 𝓜(ℝᵐ)` with `Σ_x ⪰ 0`, `Σ_w ≻ 0`, `𝕎(ℚ_x, ℙ̂_x) ≤ ρ_x`, `𝕎(ℚ_w, ℙ̂_w) ≤ ρ_w`.
`𝒩(μ, Σ)` (Definition 3.1, p. 12) is Mathlib's `multivariateGaussian μ Σ`. -/
noncomputable def normalSet {n m : ℕ} (ρx ρw : ℝ) (μx : E n) (Shx : Matrix (Fin n) (Fin n) ℝ)
    (μw : E m) (Shw : Matrix (Fin m) (Fin m) ℝ) : Set (Measure (E n × E m)) :=
  {Q | ∃ (Sx : Matrix (Fin n) (Fin n) ℝ) (Sw : Matrix (Fin m) (Fin m) ℝ),
    Sx.PosSemidef ∧ Sw.PosDef ∧
    HasFiniteSecondMoment (multivariateGaussian μx Sx) ∧
    HasFiniteSecondMoment (multivariateGaussian μw Sw) ∧
    WassersteinDRO.Gelbrich.wassersteinDistance 2 (multivariateGaussian μx Sx)
      (multivariateGaussian μx Shx) ≤ ENNReal.ofReal ρx ∧
    WassersteinDRO.Gelbrich.wassersteinDistance 2 (multivariateGaussian μw Sw)
      (multivariateGaussian μw Shw) ≤ ENNReal.ofReal ρw ∧
    Q = (multivariateGaussian μx Sx).prod (multivariateGaussian μw Sw)}

/-- Optimal value of the Gelbrich MMSE estimation problem (2.1), p. 8:
`inf_{ψ ∈ 𝓐} sup_{ℚ ∈ 𝔾(ℙ̂)} 𝓡(ψ, ℚ)`, in `[0, ∞]`. -/
noncomputable def gelbrichMinimax {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ) (μx : E n)
    (Shx : Matrix (Fin n) (Fin n) ℝ) (μw : E m) (Shw : Matrix (Fin m) (Fin m) ℝ) : ENNReal :=
  ⨅ (ψ : E m → E n) (_ : IsAffineEstimator ψ),
    ⨆ (Q : Measure (E n × E m)) (_ : Q ∈ gelbrichSet ρx ρw μx Shx μw Shw), risk H ψ Q

/-- Optimal value of the dual Wasserstein MMSE estimation problem over normal priors (3.3),
p. 13: `sup_{ℚ ∈ 𝔹_𝒩(ℙ̂)} inf_{ψ ∈ 𝓕} 𝓡(ψ, ℚ)`, in `[0, ∞]`. -/
noncomputable def normalMaximin {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ) (μx : E n)
    (Shx : Matrix (Fin n) (Fin n) ℝ) (μw : E m) (Shw : Matrix (Fin m) (Fin m) ℝ) : ENNReal :=
  ⨆ (Q : Measure (E n × E m)) (_ : Q ∈ normalSet ρx ρw μx Shx μw Shw),
    ⨅ (ψ : E m → E n) (_ : IsEstimator ψ), risk H ψ Q

/-- Optimal value of the Wasserstein MMSE estimation problem (1.7), p. 3:
`inf_{ψ ∈ 𝓕} sup_{ℚ ∈ 𝔹(ℙ̂)} 𝓡(ψ, ℚ)`, in `[0, ∞]`. -/
noncomputable def wassMinimax {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ)
    (Px : Measure (E n)) (Pw : Measure (E m)) : ENNReal :=
  ⨅ (ψ : E m → E n) (_ : IsEstimator ψ),
    ⨆ (Q : Measure (E n × E m)) (_ : Q ∈ wassersteinSet ρx ρw Px Pw), risk H ψ Q

/-- Optimal value of the dual Wasserstein MMSE estimation problem (3.1), p. 12:
`sup_{ℚ ∈ 𝔹(ℙ̂)} inf_{ψ ∈ 𝓕} 𝓡(ψ, ℚ)`, in `[0, ∞]`. -/
noncomputable def wassMaximin {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ)
    (Px : Measure (E n)) (Pw : Measure (E m)) : ENNReal :=
  ⨆ (Q : Measure (E n × E m)) (_ : Q ∈ wassersteinSet ρx ρw Px Pw),
    ⨅ (ψ : E m → E n) (_ : IsEstimator ψ), risk H ψ Q

end WassMMSE.Sandwich



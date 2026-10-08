-- Prove2me | Definitions.Def_StochKriging_Unbiased_Model
-- name    : StochKriging_Unbiased_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:10.167358+00:00
-- url     : https://prove2.me/theorems/47936028-4d33-45e2-862c-6cafb0e50d43
-- title:
--   §2–§3, pp. 363–365 — the stochastic kriging model (3), sample means (4), sample variances (12), Σ_M, Σ_M(x₀,·) and Assumption 1
-- statement:
--   Fix a probability space $(\Omega,\mathcal F,P)$, a dimension $d$ and design variables $\mathbf x\in\mathbb R^d$. A **stochastic simulation** at design setting $\mathbf x$ produces, on replication $j=1,2,\dots$, the output
--   $$\mathcal Y_j(\mathbf x)=\beta_0+\mathsf M(\mathbf x)+\varepsilon_j(\mathbf x),$$
--   where $\beta_0\in\mathbb R$ is the overall surface mean, $\mathsf M$ is a mean-zero random field on $\mathbb R^d$ (the **extrinsic** uncertainty) and $\varepsilon_j(\mathbf x)$ is the sampling noise of replication $j$ (the **intrinsic** uncertainty). This is model (3) with the trend $\mathbf f(\mathbf x)^\top\beta=\beta_0$. The quantity to predict at a point $\mathbf x_0$ is the noise-free response $\mathsf Y(\mathbf x_0)=\beta_0+\mathsf M(\mathbf x_0)$.
--
--   An **experiment design** consists of pairs $(\mathbf x_i,n_i)$, $i=1,\dots,k$: $n_i$ replications are run at the design point $\mathbf x_i$. For a sequence of outputs, the **sample mean** (4) and **sample variance** (12) of the first $m$ replications are
--   $$\bar{\mathcal Y}=\frac1m\sum_{j=1}^m\mathcal Y_j,\qquad \mathcal S^2=\frac1{m-1}\sum_{j=1}^m\big(\mathcal Y_j-\bar{\mathcal Y}\big)^2 .$$
--   At the design they give the vector $\bar{\mathcal Y}=(\bar{\mathcal Y}(\mathbf x_1),\dots,\bar{\mathcal Y}(\mathbf x_k))^\top$, with $\bar{\mathcal Y}(\mathbf x_i)$ the mean of $\mathcal Y_1(\mathbf x_i),\dots,\mathcal Y_{n_i}(\mathbf x_i)$, and the sample variances $\mathcal S^2(\mathbf x_i)$ computed from the same replications.
--
--   The extrinsic covariances are the $k\times k$ matrix $\Sigma_{\mathsf M}=\big(\mathrm{Cov}[\mathsf M(\mathbf x_h),\mathsf M(\mathbf x_i)]\big)_{h,i}$ and the vector $\Sigma_{\mathsf M}(\mathbf x_0,\cdot)=\big(\mathrm{Cov}[\mathsf M(\mathbf x_0),\mathsf M(\mathbf x_i)]\big)_{i=1}^k$.
--
--   **Assumption 1.** For a noise-variance function $\mathsf V\ge0$ and design points $\mathbf x_1,\dots,\mathbf x_k$:
--   1. $\mathsf M$ is a Gaussian random field: every finite vector $(\mathsf M(\mathbf y_1),\dots,\mathsf M(\mathbf y_m))$ is multivariate normal; its mean is $0$ at every point;
--   2. $\mathsf M$ is stationary: $\mathrm{Cov}[\mathsf M(\mathbf y),\mathsf M(\mathbf y')]=\tau^2R(\mathbf y-\mathbf y')$ for some $\tau^2>0$ and some function $R$ with $R(\mathbf 0)=1$, so the variance is the constant $\tau^2$ and the correlation depends only on $\mathbf y-\mathbf y'$;
--   3. at any finite family of distinct points the covariance matrix of $\mathsf M$ is positive definite;
--   4. for each design point, $\varepsilon_1(\mathbf x_i),\varepsilon_2(\mathbf x_i),\dots$ are $N(0,\mathsf V(\mathbf x_i))$;
--   5. the whole family $\{\varepsilon_j(\mathbf x_i)\}_{i\le k,\,j\ge1}$ is mutually independent: i.i.d. at each design point and independent across design points (no common random numbers);
--   6. this whole noise family is independent of the whole field $\mathsf M$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Design points are indexed by `Fin k` (the paper's $i$ is `i.val + 1`) and lie in `EuclideanSpace ℝ (Fin d)`; replication $j\ge1$ of the paper is index `j - 1` of a sequence `ℕ → Ω → ℝ`, so (4) and (12) sum over `Finset.range m`. (12) divides by $m-1$ and is only meaningful for $m\ge2$, which the theorems assume. Gaussianity of the field is Mathlib's `IsGaussianProcess` (all finite-dimensional laws Gaussian); covariances are `ProbabilityTheory.covariance`. Items 5 and 6 are one `iIndepFun` over the index type `Fin k × ℕ` plus one `IndepFun` between the noise family (as a random element of `Fin k × ℕ → ℝ`) and the field (as a random element of `ℝ^d → ℝ`, product σ-algebra). The variance function takes values in `ℝ≥0`; positivity at the design points is a separate hypothesis of the theorems.
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, pp. 363–365, displays (3), (4), (8), (12), §2 (definition of Σ_M, Σ_M(x₀,·)) and §3, Assumption 1 with the paragraph following it

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochKriging.Unbiased

variable {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}

/-- Display (3) with `f(x)ᵀβ = β₀`: the output of replication `j + 1` at design setting `x`,
`𝒴_{j+1}(x) = β₀ + M(x) + ε_{j+1}(x)` (replication `j ≥ 1` of the paper is index `j - 1`). -/
noncomputable def output (β₀ : ℝ) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (j : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    Ω → ℝ :=
  fun ω => β₀ + M x ω + ε j x ω

/-- Display (4): the sample mean of the first `m` replications of a sequence of outputs,
`(1/m) ∑_{j=1}^{m} 𝒴_j`. -/
noncomputable def sampleMean (Y : ℕ → Ω → ℝ) (m : ℕ) : Ω → ℝ :=
  fun ω => (1 / (m : ℝ)) * ∑ j ∈ Finset.range m, Y j ω

/-- Display (12): the sample variance of the first `m` replications,
`(1/(m-1)) ∑_{j=1}^{m} (𝒴_j - 𝒴̄)²` (meaningful for `m ≥ 2`). -/
noncomputable def sampleVar (Y : ℕ → Ω → ℝ) (m : ℕ) : Ω → ℝ :=
  fun ω => (1 / ((m : ℝ) - 1)) * ∑ j ∈ Finset.range m, (Y j ω - sampleMean Y m ω) ^ 2

/-- The vector `𝒴̄ = (𝒴̄(x₁), …, 𝒴̄(x_k))` of sample means at the design `(xᵢ, nᵢ)` (display (4)). -/
noncomputable def Ybar (β₀ : ℝ) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (x : Fin k → EuclideanSpace ℝ (Fin d))
    (n : Fin k → ℕ) : Ω → Fin k → ℝ :=
  fun ω i => sampleMean (fun j => output β₀ M ε j (x i)) (n i) ω

/-- The sample variances `𝒮²(xᵢ)` at the design points (display (12)). -/
noncomputable def S2 (β₀ : ℝ) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (x : Fin k → EuclideanSpace ℝ (Fin d))
    (n : Fin k → ℕ) : Ω → Fin k → ℝ :=
  fun ω i => sampleVar (fun j => output β₀ M ε j (x i)) (n i) ω

/-- `Σ_M`, the `k × k` matrix `(Cov[M(x_h), M(x_i)])_{h,i}` (p. 364). -/
noncomputable def SigmaM (P : Measure Ω) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (x : Fin k → EuclideanSpace ℝ (Fin d)) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun h i => cov[M (x h), M (x i); P]

/-- `Σ_M(x₀, ·)`, the vector `(Cov[M(x₀), M(x₁)], …, Cov[M(x₀), M(x_k)])` (p. 364). -/
noncomputable def SigmaM0 (P : Measure Ω) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (x : Fin k → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d)) : Fin k → ℝ :=
  fun i => cov[M x₀, M (x i); P]

/-- Assumption 1 (p. 365), with the paper's gloss of "stationary Gaussian random field":
1. `M` is a Gaussian random field (all finite-dimensional laws are Gaussian), with mean `0`;
2. stationarity: `Cov[M(x), M(x')] = τ² R(x - x')` with `τ² > 0` and `R(0) = 1`;
3. at any finite family of distinct points the covariance matrix of `M` is positive definite;
4. for each design point `xᵢ`, the noises `ε₁(xᵢ), ε₂(xᵢ), …` are `N(0, V(xᵢ))`;
5. the whole noise family `{ε_j(xᵢ)}_{i,j}` is mutually independent (i.i.d. at each point, and
   no CRN across points);
6. the whole noise family is independent of the whole field `M`. -/
structure Assumption1 (P : Measure Ω) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (V : EuclideanSpace ℝ (Fin d) → ℝ≥0)
    (x : Fin k → EuclideanSpace ℝ (Fin d)) : Prop where
  gaussian : IsGaussianProcess M P
  mean_zero : ∀ y, ∫ ω, M y ω ∂P = 0
  stationary : ∃ τ2 : ℝ, 0 < τ2 ∧ ∃ R : EuclideanSpace ℝ (Fin d) → ℝ, R 0 = 1 ∧
    ∀ y y', cov[M y, M y'; P] = τ2 * R (y - y')
  posDef : ∀ (m : ℕ) (y : Fin m → EuclideanSpace ℝ (Fin d)), Function.Injective y →
    (Matrix.of fun a b => cov[M (y a), M (y b); P]).PosDef
  noise_law : ∀ (i : Fin k) (j : ℕ), HasLaw (ε j (x i)) (gaussianReal 0 (V (x i))) P
  noise_indep : iIndepFun (fun (p : Fin k × ℕ) => ε p.2 (x p.1)) P
  noise_indep_field : IndepFun (fun ω (p : Fin k × ℕ) => ε p.2 (x p.1) ω)
    (fun ω y => M y ω) P

end StochKriging.Unbiased



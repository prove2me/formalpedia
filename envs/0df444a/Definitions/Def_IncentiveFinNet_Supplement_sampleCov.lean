-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_sampleCov
-- name    : IncentiveFinNet_Supplement_sampleCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:36:46.941558+00:00
-- url     : https://prove2.me/theorems/d1f02c34-8b6a-41f2-bf10-391f11ae2021
-- title:
--   Spectral norm, sample covariance, Gaussian data with $m=\lceil n\log n\rceil$, and the dampening factor $\eta^*$ with all edges allowed
-- statement:
--   The objects of Theorem 5 (§2.3, p.16) and Theorem 11 (A.10, p.44).
--
--   - $\|A\|$ is the spectral norm (the $\ell^2$ operator norm) of a square matrix $A$.
--   - For samples $x_1,\dots,x_m\in\mathbb R^n$ (the columns of $X_i$), with $\hat\mu=\frac1m\sum_k x_k$, the sample covariance is
--   $$
--   \hat\Sigma = \frac{1}{m-1}\sum_{k=1}^m (x_k-\hat\mu)(x_k-\hat\mu)^{\top}.
--   $$
--   - The sample size is $m=\lceil n\log n\rceil$ (natural logarithm).
--   - The data law: each of the $n$ agents observes $m$ samples in $\mathbb R^n$, and all $nm$ samples are independent with law $\mathcal N(0,\Sigma)$.
--   - For risk aversions $\gamma_i>0$ and positive definite covariances $\Sigma_1,\dots,\Sigma_n$, $\eta^*=2/\lambda_{\max}$ is the maximum dampening factor of Theorem 4 for the network setting with these covariances and all edges allowed.
--
--   **Formalization Note** The printed $\hat\mu=\frac1m\sum_iX_i$ and $\hat\Sigma_i=\frac1{m-1}\sum_i(X_i-\hat\mu)(X_i-\hat\mu)^{\top}$ reuse the index $i$ for the samples, as the proof of Theorem 11 writes it. $\eta^*$ does not depend on $M$, so the setting uses $M=0$; when some $\Sigma_i$ is not positive definite the value is the junk $0$.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, §2.3, p.16 (setting of Theorem 5); proof of Theorem 11, A.10, p.44

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Supplement_lamMax

open Matrix MeasureTheory ProbabilityTheory

namespace IncentiveFinNet.Supplement

/-- The spectral (`ℓ²` operator) norm `‖A‖` of a square matrix, the norm of Theorems 5 and 11
(Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, p.16 and A.10, p.44, where it is written `‖·‖₂`).

**Formalization Note** `A` acts on `EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanCLM`; the
norm is the operator norm of that map. It is not Mathlib's default (entrywise sup) norm on
`Matrix`. -/
noncomputable def opNorm2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- The sample covariance of Theorem 5 (arXiv:2212.06808v3, p.16): for samples
`x₁, …, x_m ∈ ℝⁿ` (the columns of `X_i`), with `µ̂ = (1/m) Σ_k x_k`,
`Σ̂ = 1/(m − 1) · Σ_k (x_k − µ̂)(x_k − µ̂)ᵀ`.

**Formalization Note** The printed formulas `µ̂ = (1/m) Σ_i X_i` and
`Σ̂_i := 1/(m − 1) Σ_i (X_i − µ̂)(X_i − µ̂)ᵀ` reuse the agent index `i` for the sum over the samples
(the columns of `X_i`), as the proof of Theorem 11 (A.10, p.44) writes it with `X_1, …, X_m`. -/
noncomputable def sampleCov {n m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  let μhat : Fin n → ℝ := fun a => (m : ℝ)⁻¹ * ∑ k, x k a
  ((m : ℝ) - 1)⁻¹ • ∑ k, vecMulVec (fun a => x k a - μhat a) (fun a => x k a - μhat a)

/-- The sample size `m = ⌈n log n⌉` of Theorem 5 (p.16), with the natural logarithm. -/
noncomputable def sampleSize (n : ℕ) : ℕ :=
  ⌈(n : ℝ) * Real.log n⌉₊

/-- The law of the data of Theorem 5 (p.16): each agent `i ∈ [n]` observes `m` samples
`x_{i,1}, …, x_{i,m} ∈ ℝⁿ`, and every sample is drawn independently from `N(0, Σ)`.

**Formalization Note** `N(0, Σ)` is Mathlib's `multivariateGaussian 0 Σ`; the product measure makes
all `n · m` samples independent. -/
noncomputable def dataLaw (n m : ℕ) (Sig : Matrix (Fin n) (Fin n) ℝ) :
    Measure (Fin n → Fin m → EuclideanSpace ℝ (Fin n)) :=
  Measure.pi fun _ => Measure.pi fun _ => multivariateGaussian 0 Sig

/-- The maximum dampening factor `η* = 2/λ_max` of Theorem 4 (p.15) for the network setting with
**all edges allowed**, risk aversions `γ` and covariances `Σ_i = Sigs i`. It is the `η̂*` (for the
sample covariances) and the `η*` (for `Σ_i = Σ`) of Theorem 5 (p.16).

**Formalization Note** `η*` does not depend on `M` (only `Q_i` enters `K` and `L`), so the setting is
built with `M = 0`. When some `Sigs i` is not positive definite there is no network setting and
the value is the junk `0`; Theorem 5 states positive definiteness of the sample covariances
explicitly. The `if` is decided classically. -/
noncomputable def etaStarAll {n : ℕ} (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i)
    (Sigs : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  haveI := Classical.propDecidable (∀ i, (Sigs i).PosDef)
  if h : ∀ i, (Sigs i).PosDef then
    2 / lamMax (⟨0, γ, Sigs, fun _ => Finset.univ, hγ, h, by simp⟩ : NetworkSetting n)
  else 0

end IncentiveFinNet.Supplement



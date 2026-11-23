-- Prove2me | Definitions.Def_MaxSpectralRisk_Duality_Supplement_Sampling
-- name    : MaxSpectralRisk_Duality_Supplement_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:08:29.317816+00:00
-- url     : https://prove2.me/theorems/17e2325d-a2db-4242-822a-cc76e5972ed3
-- title:
--   (17) — empirical probability vectors, independent samples and multinomial Gaussian limits
-- statement:
--   For observations $X_0,\ldots,X_k$ in a finite carrier, define the empirical vector by
--   $$
--   \widehat\mu_{k+1}(i)=\frac1{k+1}\sum_{j=0}^k\mathbf1_{\{X_j=i\}}.
--   $$
--   The sampling predicate requires each $X_j$ and $Y_j$ to be measurable with laws $\mu$ and $\nu$, independence within each sequence, and independence of the two whole sequences. Both empirical vectors use the same sample size.
--
--   For a probability vector $p$, set
--   $$
--   \Sigma_p(i,j)=\begin{cases}p_i(1-p_i)&i=j,\\-p_ip_j&i\ne j.\end{cases}
--   $$
--   A multinomial Gaussian limit is a measurable vector with Mathlib's Gaussian law, coordinate means zero and covariance matrix $\Sigma_p$. These are exactly the limiting vectors specified in (17) and Theorem 3.
--
--   **Formalization Note** Zero variances and singular covariance matrices are allowed. Gaussian coordinates have finite second moments, so the displayed means and covariances are genuine integrals. The positive sample sizes are reindexed by $k+1$; no empty-sample convention enters the theorem.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, pp. 19–20, empirical measures, (17), Theorem 3(2)

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Finite

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory ProbabilityTheory

/-- Empirical probability vector from n+1 observations; indexing n+1 removes
only the undefined empty-sample convention and does not change the limit law. -/
noncomputable def empirical {Ω : Type*} {k : ℕ} (X : ℕ → Ω → Fin k)
    (n : ℕ) (ω : Ω) : Fin k → ℝ :=
  fun i => (∑ j : Fin (n + 1), if X j ω = i then (1 : ℝ) else 0) / (n + 1 : ℝ)

/-- Independent i.i.d. samples from the two marginals, p. 19. Independence of
entire sequences enforces independence across every cross-sample pair as well. -/
def IndependentSamples {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (P : Measure Ω) (θ : Marginals m n)
    (X : ℕ → Ω → Fin (m + 1)) (Y : ℕ → Ω → Fin (n + 1)) : Prop :=
  (∀ k, Measurable (X k) ∧ P.map (X k) = vectorMeasure θ.1) ∧
  (∀ k, Measurable (Y k) ∧ P.map (Y k) = vectorMeasure θ.2) ∧
  iIndepFun X P ∧ iIndepFun Y P ∧
  IndepFun (fun ω => fun k => X k ω) (fun ω => fun k => Y k ω) P

/-- (17), p. 19: the multinomial covariance matrix; it may be singular. -/
noncomputable def Sigma {k : ℕ} (p : Fin k → ℝ) (i j : Fin k) : ℝ :=
  if i = j then p i * (1 - p i) else -(p i * p j)

/-- A centred Gaussian vector with covariance (17). HasGaussianLaw is Mathlib's
multivariate Gaussian notion and permits zero variances. Gaussian coordinates
have finite second moments, so all displayed moments are genuine integrals. -/
def MultinomialGaussian {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (Q : Measure Ω) (p : Fin k → ℝ) (Z : Ω → Fin k → ℝ) : Prop :=
  Measurable Z ∧ HasGaussianLaw Z Q ∧
  (∀ i, ∫ ω, Z ω i ∂Q = 0) ∧
  ∀ i j, covariance (fun ω => Z ω i) (fun ω => Z ω j) Q = Sigma p i j

end MaxSpectralRisk.Duality.Supplement



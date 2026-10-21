-- Prove2me | Definitions.Def_GenEllipPot_Potential_Model
-- name    : GenEllipPot_Potential_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:14.730984+00:00
-- url     : https://prove2.me/theorems/e1361856-a8ca-434d-85e3-2419e5483179
-- title:
--   §2 model: filtered observations and posterior covariance
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $(\mathcal F_t)_{t\ge1}$ an increasing filtration. The unknown vector $\Theta^\star\in\mathbb R^d$ and each action $A_t\in\mathbb R^d$ lie in the Euclidean unit ball almost surely; $A_t$ is $\mathcal F_t$-measurable. Each real observation $Y_t$ is $\mathcal F_{t+1}$-measurable and satisfies
--
--   $$\mathbb E[Y_t\mid\mathcal F_t,\Theta^\star]=\langle\Theta^\star,A_t\rangle,\qquad \operatorname{Var}(Y_t\mid\mathcal F_t,\Theta^\star)\le\sigma^2.$$
--
--   The **posterior covariance** $\Gamma_t$ is the entrywise conditional covariance of $\Theta^\star$ given $\mathcal F_t$. The **potential** is $f(\Sigma,x)=\log\det(I+x\Sigma)$. The accumulated quadratic form is $\sum_{t=1}^T A_t^\top\Gamma_t A_t$. These definitions supply one shared model for Theorem 2.1 and its supporting results.
--
--   **Formalization Note.** Time starts at $t=1$. Each $Y_t$ is square-integrable, an explicit condition needed for the conditional variance to represent the paper's variance. Vector unit balls use the Euclidean dot product. Matrix conditional expectations are defined entrywise.
-- source:
--   Hamidi & Bayati, The Elliptical Potential Lemma for General Distributions with an Application to Linear Thompson Sampling, arXiv:2102.07987v3, pp. 3–4, §2 and Lemma 2.2

import Mathlib

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped MeasureTheory

namespace GenEllipPot.Potential

/-- The information at time `t` together with the unknown parameter. -/
def condSigma {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (Θ : Ω → Fin d → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  F t ⊔ MeasurableSpace.comap Θ inferInstance

/-- The conditional covariance matrix of the parameter, entry by entry. -/
def postCov {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (Θ : Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => μ[fun ω' =>
    (Θ ω' i - μ[fun x => Θ x i | F t] ω') *
    (Θ ω' j - μ[fun x => Θ x j | F t] ω') | F t] ω

/-- Entrywise conditional expectation of the next posterior covariance. -/
def meanPostCov {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (Θ : Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => μ[fun ω' => postCov μ F Θ (t + 1) ω' i j | F t] ω

/-- The log-determinant potential `f(Σ,x)` of Lemma 2.2. -/
def potF {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (x : ℝ) : ℝ :=
  Real.log ((1 + x • S).det)

/-- The standing probabilistic assumptions of Section 2, with square integrability
of each observation made explicit to rule out the totalized zero variance. -/
structure Model (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : ℕ) where
  F : Filtration ℕ (inferInstance : MeasurableSpace Ω)
  Θ : Ω → Fin d → ℝ
  A : ℕ → Ω → Fin d → ℝ
  Y : ℕ → Ω → ℝ
  σ : ℝ
  measurable_Θ : Measurable Θ
  norm_Θ : ∀ᵐ ω ∂μ, Θ ω ⬝ᵥ Θ ω ≤ 1
  measurable_A : ∀ t, 1 ≤ t → Measurable[F t] (A t)
  norm_A : ∀ t, 1 ≤ t → ∀ᵐ ω ∂μ, A t ω ⬝ᵥ A t ω ≤ 1
  measurable_Y : ∀ t, 1 ≤ t → Measurable[F (t + 1)] (Y t)
  memLp_Y : ∀ t, 1 ≤ t → MemLp (Y t) 2 μ
  mean_Y : ∀ t, 1 ≤ t →
    μ[Y t | condSigma F Θ t] =ᵐ[μ] fun ω => Θ ω ⬝ᵥ A t ω
  variance_Y : ∀ t, 1 ≤ t →
    ∀ᵐ ω ∂μ, condVar (condSigma F Θ t) (Y t) μ ω ≤ σ ^ 2

/-- The accumulated posterior quadratic form from rounds one through `T`. -/
def rewardSum {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (Θ : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T,
    A t ω ⬝ᵥ (postCov μ F Θ t ω *ᵥ A t ω)

end GenEllipPot.Potential



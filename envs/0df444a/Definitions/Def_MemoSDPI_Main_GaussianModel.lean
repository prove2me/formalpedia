-- Prove2me | Definitions.Def_MemoSDPI_Main_GaussianModel
-- name    : MemoSDPI_Main_GaussianModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:41:03.954781+00:00
-- url     : https://prove2.me/theorems/ab7da48c-d058-409e-a950-d615a3f03290
-- title:
--   Gaussian prior N(0, σ²I_d) and Gaussian location family N(θ, I_d)
-- statement:
--   For $\sigma \in \mathbb R$ and $d \in \mathbb N$, the **Gaussian prior** is $N(0, \sigma^2 I_d)$ on $\mathbb R^d$: $d$ independent coordinates with law $N(0,\sigma^2)$. The **Gaussian location family** assigns to $\theta \in \mathbb R^d$ the law $N(\theta, I_d)$, the law of $X = \theta + Z$ with $Z \sim N(0, I_d)$, i.e. independent coordinates $X_j \sim N(\theta_j, 1)$.
--
--   Together they form the average-case problem of Theorem 3.1: $\theta \sim N(0,\sigma^2 I_d)$ and, given $\theta$, records $X_i = \theta + Z_i$ with $Z_1,\dots,Z_n$ independent $N(0, I_d)$.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ`; Mathlib's `gaussianReal μ v` takes the variance $v$ in $\mathbb R_{\ge 0}$, so the prior variance is `(σ^2).toNNReal`. The module records that $N(\theta, I_d)$ is a probability measure.
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 11, Theorem 3.1

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- **Gaussian prior `N(0, σ² I_d)`** (Feldman, Lyu, Talwar, *Lower Bounds for Memorization,
Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission
(manuscript sha256 dbb300da…), p. 11, Theorem 3.1): `d` independent `N(0, σ²)` coordinates.

**Formalization Note.** `ℝ^d` is `Fin d → ℝ`; the variance is `σ²` as an `ℝ≥0`. -/
noncomputable def gaussPrior (σ : ℝ) (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => gaussianReal 0 (σ ^ 2).toNNReal

/-- **Gaussian location family `N(θ, I_d)`** (p. 11, Theorem 3.1): the law of `X = θ + Z` with
`Z ∼ N(0, I_d)`, that is, `d` independent coordinates `N(θ_j, 1)`. -/
noncomputable def gaussLocation {d : ℕ} (θ : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun j => gaussianReal (θ j) 1

/-- `N(θ, I_d)` is a probability measure. -/
instance gaussLocation_isProb {d : ℕ} (θ : Fin d → ℝ) :
    IsProbabilityMeasure (gaussLocation θ) := by
  unfold gaussLocation; infer_instance

end MemoSDPI.Main



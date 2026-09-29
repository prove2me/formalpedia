-- Prove2me | Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
-- name    : StochLinOpt_UpperBound_confidenceBall2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:27:45.807799+00:00
-- url     : https://prove2.me/theorems/1c26c4fd-ed34-4f7a-bcb5-c3e967fc20d3
-- title:
--   ConfidenceBall₂ (Algorithm 3.1): $A_t$, $\hat\mu_t$, $\beta_t$, $B^2_t$ and the selection rule
-- statement:
--   This file defines the algorithm ConfidenceBall₂$(D,\delta)$ of Dani, Hayes and Kakade (Algorithm 3.1), in the coordinates of their Section 5, where the barycentric spanner of the decision set $D\subseteq\mathbb R^n$ is the standard basis $e_1,\dots,e_n$.
--
--   Rounds are numbered $t=1,2,\dots$. Given the decisions $x_1,x_2,\dots\in\mathbb R^n$ and the observed losses $\ell_1,\ell_2,\dots\in\mathbb R$, and a parameter $\delta$:
--
--   1. **Confidence radius.** $$\beta_t=\max\Big(128\,n\ln t\,\ln(t^2/\delta),\ \big(\tfrac83\ln(t^2/\delta)\big)^2\Big).$$
--   2. **Design matrix.** $A_t=I+\sum_{\tau=1}^{t-1}x_\tau x_\tau^{\top}$, so $A_1=\sum_i e_ie_i^\top=I$ and $A_{t+1}=A_t+x_tx_t^\top$.
--   3. **Least-squares estimate.** $\hat\mu_t=A_t^{-1}\sum_{\tau=1}^{t-1}\ell_\tau x_\tau$, so $\hat\mu_1=0$.
--   4. **Confidence ellipsoid.** $B^2_t=\{\nu\in\mathbb R^n:\ (\nu-\hat\mu_t)^\top A_t(\nu-\hat\mu_t)\le\beta_t\}$, i.e. $\|\nu-\hat\mu_t\|_{2,A_t}\le\sqrt{\beta_t}$.
--   5. **Run of the algorithm.** The sequence $(x_t)$ is a run of ConfidenceBall₂$(D,\delta)$ with losses $(\ell_t)$ when, for every $t\ge1$, $x_t\in D$ and there is $\tilde\mu_t\in B^2_t$ with $$\tilde\mu_t^\top x_t\le\nu^\top y\quad\text{for all }\nu\in B^2_t,\ y\in D,$$ that is, $x_t\in\operatorname{argmin}_{x\in D}\min_{\nu\in B^2_t}\nu^\top x$ for some choice among ties.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and matrices `Matrix (Fin n) (Fin n) ℝ`; sequences are indexed by `ℕ` with round $t\ge1$, and the value at index $0$ is never used. Section 5 of the paper takes the barycentric spanner to be the standard basis without loss of generality (the algorithm is equivariant under the linear change of coordinates taking a spanner to the standard basis), which is why $A_1=I$. The matrix $A_t$ is always positive definite, so Lean's `⁻¹` is the true inverse. The ball is written with the quadratic form rather than $A_t^{1/2}$; the two are equivalent since both sides are nonnegative. The argmin is encoded as a joint minimiser, which admits every tie-breaking rule and avoids an `sInf` junk value.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 4, Algorithm 3.1; PDF p. 3 (norm ‖·‖_{2,A}); PDF p. 6, Section 5 (standard-basis spanner)

import Mathlib

open Matrix

namespace StochLinOpt.UpperBound

/-- The squared confidence radius of ConfidenceBall₂ (Algorithm 3.1):
`β_t = max (128 n ln t ln (t² / δ), ((8/3) ln (t² / δ))²)`. -/
noncomputable def beta (n : ℕ) (δ : ℝ) (t : ℕ) : ℝ :=
  max (128 * (n : ℝ) * Real.log (t : ℝ) * Real.log ((t : ℝ) ^ 2 / δ))
    ((8 / 3 * Real.log ((t : ℝ) ^ 2 / δ)) ^ 2)

/-- The design matrix `A_t = I + ∑_{τ=1}^{t-1} x_τ x_τᵀ` (the barycentric spanner is the standard
basis, so `A_1 = ∑ e_i e_iᵀ = I`). Rounds are numbered `1, 2, …`; `x 0` is never used. -/
noncomputable def designMatrix {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + ∑ τ ∈ Finset.Ico 1 t, vecMulVec (x τ) (x τ)

/-- The least-squares estimate `µ̂_t = A_t⁻¹ ∑_{τ=1}^{t-1} ℓ_τ x_τ` (so `µ̂_1 = 0`). -/
noncomputable def muHat {n : ℕ} (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) : Fin n → ℝ :=
  (designMatrix x t)⁻¹ *ᵥ ∑ τ ∈ Finset.Ico 1 t, ℓ τ • x τ

/-- The confidence ellipsoid `B²_t = {ν : (ν - µ̂_t)ᵀ A_t (ν - µ̂_t) ≤ β_t}`, i.e.
`‖ν - µ̂_t‖_{2,A_t} ≤ √β_t`. -/
def confBall {n : ℕ} (δ : ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) : Set (Fin n → ℝ) :=
  {ν | (ν - muHat x ℓ t) ⬝ᵥ (designMatrix x t *ᵥ (ν - muHat x ℓ t)) ≤ beta n δ t}

/-- The decision sequence `x` (with observed losses `ℓ`) is a run of ConfidenceBall₂(D, δ):
on every round `t ≥ 1`, `x_t ∈ D` and, for some `µ̃_t ∈ B²_t`, the pair `(x_t, µ̃_t)` minimises
`ν ⬝ᵥ y` jointly over `ν ∈ B²_t` and `y ∈ D`, i.e.
`x_t ∈ argmin_{y ∈ D} min_{ν ∈ B²_t} νᵀ y` with any tie-breaking. -/
def IsConfidenceBall2Run {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ) (x : ℕ → Fin n → ℝ)
    (ℓ : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → x t ∈ D ∧
    ∃ μt ∈ confBall δ x ℓ t, ∀ ν ∈ confBall δ x ℓ t, ∀ y ∈ D, μt ⬝ᵥ x t ≤ ν ⬝ᵥ y

end StochLinOpt.UpperBound



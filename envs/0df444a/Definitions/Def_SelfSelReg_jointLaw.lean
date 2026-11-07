-- Prove2me | Definitions.Def_SelfSelReg_jointLaw
-- name    : SelfSelReg_jointLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:35.703126+00:00
-- url     : https://prove2.me/theorems/a8c4a01b-9a9c-4b6d-88f7-b4c10f3b5cbb
-- title:
--   The Gaussian maximum self-selection model: covariate, noises, responses, slices
-- statement:
--   Fix integers $n\ge1$ and $2\le k\le n$ and unknown regressors $w_1,\dots,w_k\in\mathbb R^n$. In the **maximum self-selection model** one draws a covariate $X\sim N(0,I_n)$ and, independently, a noise vector $\xi=(\xi_i)_{i\in[k]}$ with i.i.d. $N(0,1)$ coordinates. The latent responses and the observed maximum are
--   $$Y_i=\langle w_i,X\rangle+\xi_i,\qquad Y_{\max}=\max_{i\in[k]}Y_i .$$
--   The maximizing index is not observed. For an index set $I\subseteq[k]$ write $Y_{\max,I}=\max_{i\in I}Y_i$, with $Y_{\max,\emptyset}=-\infty$, and call $\{T\le Y_{\max,I}\le T+1\}$ the **slice** of $I$ at threshold $T$.
--
--   This file fixes the joint law of $(X,\xi)$ (the product of the standard Gaussians on $\mathbb R^n$ and $\mathbb R^k$), the responses $Y_i$, the maximum $Y_{\max}$ and the slice events. Every expectation of the paper over $X$ and (some of) the noises is an integral against this joint law.
--
--   **Formalization Note** The slice $T\le Y_{\max,I}\le T+1$ is written without the maximum: some $Y_i$ with $i\in I$ is at least $T$, and all $Y_i$ with $i\in I$ are at most $T+1$. For $I=\emptyset$ the slice is empty. $Y_{\max}$ is the supremum over the finite index type, which is the maximum whenever $k\ge1$.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Definition 1.1, (1), p.2 (PDF p.5); §5, p.18 (PDF p.21); §8.1.1, p.56 (PDF p.59)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **The Gaussian maximum self-selection model** (Definition 1.1).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Definition 1.1, p.2 (PDF p.5): "X ∼ N(0, I_n), Y_max = max_{i∈[k]} Y_i,
Y_i = w_iᵀX + ξ_i, ξ_i ∼ i.i.d. N(0, 1). The noise vector ξ = (ξ_i)_{i∈[k]} is independent of X."

`jointLaw n k` is the joint law of the covariate `X ∼ N(0, I_n)` and the noise vector
`ξ ∼ N(0, I_k)`, independent: the product of the standard Gaussians on `ℝⁿ` and `ℝᵏ`.

**Formalization Note.** `stdGaussian` is Mathlib's standard Gaussian on a finite-dimensional inner
product space; on `EuclideanSpace ℝ (Fin m)` it is the product of `m` copies of `N(0, 1)`
(`map_pi_eq_stdGaussian`). Every expectation `E_{X,ξ}`, `E_{X,ξ_i}`, `E_{X,ξ_Q}` of the paper is an
integral against `jointLaw n k`; integrating out noises the integrand does not depend on changes
nothing. -/
noncomputable def jointLaw (n k : ℕ) :
    Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))

/-- The latent response `Y_i = ⟨w_i, X⟩ + ξ_i` (Definition 1.1, (1), p.2). -/
noncomputable def response {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (ξ : EuclideanSpace ℝ (Fin k)) (i : Fin k) : ℝ :=
  inner ℝ (w i) x + ξ i

/-- The observed maximum response `Y_max = max_{i∈[k]} Y_i` (Definition 1.1, (1), p.2).

**Formalization Note.** For `k ≥ 1` the supremum over the finite type `Fin k` is the maximum;
every statement using it assumes `2 ≤ k`, as Definition 1.1 does. -/
noncomputable def yMax {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (ξ : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ⨆ i, response w x ξ i

/-- The slice event `T ≤ Y_max,I ≤ T + 1` for an index set `I ⊆ [k]`, where
`Y_max,I = max_{i∈I} Y_i` (§5, p.18, PDF p.21, and §8.1.1, p.56, PDF p.59).

**Formalization Note.** Written without the maximum: `T ≤ max_{i∈I} Y_i` iff some `Y_i ≥ T`, and
`max_{i∈I} Y_i ≤ T + 1` iff every `Y_i ≤ T + 1`. For `I = ∅` the event is empty, matching the
convention `Y_max,∅ = −∞`. -/
def inSlice {n k : ℕ} (T : ℝ) (w : Fin k → EuclideanSpace ℝ (Fin n)) (I : Finset (Fin k))
    (x : EuclideanSpace ℝ (Fin n)) (ξ : EuclideanSpace ℝ (Fin k)) : Prop :=
  (∃ i ∈ I, T ≤ response w x ξ i) ∧ ∀ i ∈ I, response w x ξ i ≤ T + 1

end SelfSelReg



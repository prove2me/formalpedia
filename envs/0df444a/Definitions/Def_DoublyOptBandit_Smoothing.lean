-- Prove2me | Definitions.Def_DoublyOptBandit_Smoothing
-- name    : DoublyOptBandit_Smoothing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:47.716486+00:00
-- url     : https://prove2.me/theorems/9991635c-b08f-44fc-a375-2d750dc4a8b3
-- title:
--   Uniform law on the unit ball, smoothed reward $\hat u_i$ and $\sigma_{\max}$ (Lemma 3.5)
-- statement:
--   Let $A_j\in\mathbb R^{n_j\times n_j}$ be matrices, $w_i$ uniform on the unit ball $\mathbb B^{n_i}$ and $z_j$ uniform on the unit spheres $\mathbb S^{n_j}$, all independent. The **smoothed reward** of player $i$ with respect to $(A_j)$ is
--   $$
--   \hat u_i(x)=\mathbb E_{w_i\sim\mathbb B^{n_i}}\,\mathbb E_{z_{-i}\sim\prod_{j\ne i}\mathbb S^{n_j}}\big[u_i(x_i+A_iw_i;\hat x_{-i})\big],\qquad \hat x_j=x_j+A_jz_j .
--   $$
--   A random vector $W$ is **uniform on the unit ball** if it is measurable and its law is Lebesgue measure on the ball, normalized. For a square matrix $A$, $\sigma_{\max}(A)$ is its largest singular value, the operator norm on Euclidean space.
--
--   These objects state Lemma 3.5, the bias–variance properties of the ellipsoidal estimator.
--
--   **Formalization Note** The expectation is a Bochner integral on a probability space carrying $W$ and the directions; the integrand reads the direction $z_i$ of player $i$ nowhere, so integrating over all directions gives the paper's expectation over $z_{-i}$. The paper calls $\sigma_{\max}(A)$ the largest eigenvalue; the two agree for the symmetric positive definite matrices of Algorithm 2 (see the correction on Lemma 3.5).
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Lemma 3.5, p.14; (F.4), p.34

import Mathlib
import Definitions.Def_DoublyOptBandit_Components

open scoped InnerProductSpace
open MeasureTheory

namespace DoublyOptBandit

/-- `W` is **uniformly distributed on the unit ball** `Bⁿ = {w ∈ ℝⁿ : ‖w‖ < 1}` (Ba, Lin, Zhang &
Zhou, arXiv:2112.02856v4, p.14, "Bⁿⁱ is a nᵢ-dimensional unit ball", `wᵢ ∼ Bⁿⁱ` in Lemma 3.5):
`W` is measurable and its law is Lebesgue measure on the ball, normalized.

**Formalization Note** The open ball is used; the unit sphere is Lebesgue-null, so the closed ball
gives the same law. Measurability is required so that `Measure.map W P` is the law of `W` (for a
non-measurable map Mathlib's pushforward is `0`). -/
def IsUniformOnUnitBall {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m : ℕ}
    (W : Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  Measurable W ∧
    Measure.map W P = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1))⁻¹ •
      volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)

/-- The **smoothed reward** of player `i` with respect to the matrices `A = (A_j)`
(arXiv:2112.02856v4, Lemma 3.5, p.14):
`ûᵢ(x) = E_{wᵢ∼Bⁿⁱ} E_{z₋ᵢ∼∏_{j≠i}Sⁿʲ}[uᵢ(xᵢ + Aᵢwᵢ; x̂₋ᵢ)]` with `x̂ⱼ = xⱼ + Aⱼzⱼ`, realized on a
probability space carrying `W` (for `wᵢ`) and the directions `Z j` (for `zⱼ`).

**Formalization Note** The expectation is the Bochner integral over the probability space. The
integrand reads `Z j` only for `j ≠ i` (coordinate `i` is overwritten by `xᵢ + AᵢW`), so the
integral over the whole family `Z` equals the paper's expectation over `z₋ᵢ` when the laws are
as in Lemma 3.5. -/
noncomputable def smoothedReward {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    {n : Fin N → ℕ} (i : Fin N) (W : Ω → EuclideanSpace ℝ (Fin (n i)))
    (Z : ∀ j, Ω → EuclideanSpace ℝ (Fin (n j))) (A : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℝ)
    (ui : Joint n → ℝ) (x : Joint n) : ℝ :=
  ∫ ω, ui (update (perturb A x (fun j => Z j ω)) i (x i + Matrix.toEuclideanLin (A i) (W ω))) ∂P

/-- `σ_max(A)`, the largest singular value (operator norm on `ℝᵐ` with the Euclidean norm) of a
square matrix `A` (arXiv:2112.02856v4, Lemma 3.5 part 2, p.14, and Appendix F, (F.4), p.34).

**Formalization Note** The paper calls `σ_max(A)` "the largest eigenvalue of A". For the
symmetric positive definite matrices `Aᵢᵗ` of Algorithm 2 the two coincide; for a general invertible
`A` the bound of Lemma 3.5 part 2 is false with the largest eigenvalue and its proof (p.33) uses
`‖Aw‖ ≤ σ_max(A)‖w‖`, which is the operator norm (see the correction recorded on Lemma 3.5). -/
noncomputable def sigmaMax {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) A‖

end DoublyOptBandit



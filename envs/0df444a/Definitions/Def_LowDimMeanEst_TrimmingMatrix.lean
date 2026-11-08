-- Prove2me | Definitions.Def_LowDimMeanEst_TrimmingMatrix
-- name    : LowDimMeanEst_TrimmingMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:47:16.355205+00:00
-- url     : https://prove2.me/theorems/617ef50f-3427-46c5-8506-2f8c1fb7b393
-- title:
--   Trimming matrix of Lemma 3: $A\succeq0$, $\sum_i\min(1,x_i^\top Ax_i)=\frac13\log\frac1\delta$, variance maximality; trimmed mean
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ and weights $w\in\mathbb R^n$. A matrix $A$ is a **KKT matrix** for $w$ (the conclusion of Lemma 3) if $A\succeq0$, $w_i=\min(1,x_i^\top Ax_i)$ for all $i$, and for every unit eigenvector $v$ of $A$ with strictly positive eigenvalue and every unit vector $z$,
--
--   $$z^\top\hat\Sigma_{\rm trimmed}z\le v^\top\hat\Sigma_{\rm trimmed}v,\qquad \hat\Sigma_{\rm trimmed}=\sum_i(1-w_i)\,x_ix_i^\top .$$
--
--   $A$ is a **trimming matrix** for the samples and $\delta$ if it is a KKT matrix for its own weights $w_i=\min(1,x_i^\top Ax_i)$ and these weights sum to the target of Algorithm 2,
--
--   $$\sum_i\min(1,x_i^\top Ax_i)=\tfrac13\log\tfrac1\delta .$$
--
--   The **trimmed mean** of the samples under $A$ is $\frac1n\sum_i\big(1-\min(1,x_i^\top Ax_i)\big)x_i$.
--
--   Several results speak of "the trimming matrix $A$ implicitly computed by Algorithm 2 (Lemma 3)". Such an $A$ need not be unique; the statements of the mission are made for every trimming matrix, so they apply to whichever matrix the algorithm induces.
--
--   **Formalization Note** The trimmed quadratic form $z\mapsto\sum_i(1-\min(1,x_i^\top Ax_i))\langle x_i,z\rangle^2$ is unnormalized, like $\hat\Sigma_{\rm trimmed}$. $A$ may be singular, or $0$.
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 3, p.9; Lemmas 43–44, Corollary 7, Theorems 8 and 26 (pp.13, 31, 83)

import Mathlib
import Definitions.Def_LowDimMeanEst_Basic

open MeasureTheory

namespace LowDimMeanEst

/-!
# The trimming matrix of Lemma 3 and the trimmed mean

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…), Lemma 3, p.9:

"… there exists a symmetric positive semidefinite trimming matrix A satisfying wᵢ = min(1, x′ᵢ⊤Ax′ᵢ)
and the property in the paragraph below: Let v be any unit eigenvector of A with strictly positive
eigenvalue, and consider any other unit vector z ∈ ℝᵈ. Defining the trimmed empirical covariance
Σ̂_trimmed = Σᵢ (1 − wᵢ) x′ᵢx′ᵢ⊤, then it holds that v⊤Σ̂_trimmed v ≥ z⊤Σ̂_trimmed z."

**Formalization Note.**
* `IsKKTMatrix x w A` is the conclusion of Lemma 3 for weights `w`.
* The later statements speak of "the trimming matrix A implicitly computed by Algorithm 2
  (Lemma 3)". Such an `A` is not unique (p.9). `IsTrimmingMatrix x δ A` collects exactly the
  properties the proofs use: `A` is symmetric positive semidefinite, `Σᵢ min(1, xᵢ⊤Axᵢ) = (1/3)
  log(1/δ)` (the weight sum of Algorithm 2), and the maximality condition of Lemma 3 for the weights
  `min(1, xᵢ⊤Axᵢ)`. The statements quantify over every such `A`, so they hold for whichever matrix
  the algorithm induces. `A` may be singular, or `0`.
* `trimmedQuad x A z = z⊤ (Σᵢ (1 − min(1, xᵢ⊤Axᵢ)) xᵢxᵢ⊤) z` is unnormalized, as `Σ̂_trimmed`.
-/

/-- Lemma 3's conclusion for weights `w`: `A` is symmetric positive semidefinite,
`wᵢ = min(1, xᵢ⊤Axᵢ)` for every `i`, and for every unit eigenvector `v` of `A` with strictly
positive eigenvalue and every unit vector `z`, `z⊤Σ̂ z ≤ v⊤Σ̂ v` where `Σ̂ = Σᵢ (1 − wᵢ) xᵢxᵢ⊤`. -/
def IsKKTMatrix {d N : ℕ} (x : Fin N → E d) (w : Fin N → ℝ) (A : E d →L[ℝ] E d) : Prop :=
  A.IsPositive ∧ (∀ i, w i = trim A (x i)) ∧
    ∀ (v z : E d) (lam : ℝ), 0 < lam → A v = lam • v → ‖v‖ = 1 → ‖z‖ = 1 →
      ∑ i, (1 - w i) * (inner ℝ (x i) z) ^ 2 ≤ ∑ i, (1 - w i) * (inner ℝ (x i) v) ^ 2

/-- `z⊤ Σ̂_trimmed z = Σᵢ (1 − min(1, xᵢ⊤Axᵢ)) ⟨xᵢ, z⟩²` (unnormalized). -/
noncomputable def trimmedQuad {d n : ℕ} (x : Fin n → E d) (A : E d →L[ℝ] E d) (z : E d) : ℝ :=
  ∑ i, (1 - trim A (x i)) * (inner ℝ (x i) z) ^ 2

/-- `A` is a trimming matrix of Algorithm 2 for the samples `x` and parameter `δ`: symmetric
positive semidefinite, trimming weights `min(1, xᵢ⊤Axᵢ)` summing to `(1/3) log(1/δ)`, and the
maximality (KKT) condition of Lemma 3. -/
def IsTrimmingMatrix {d n : ℕ} (x : Fin n → E d) (δ : ℝ) (A : E d →L[ℝ] E d) : Prop :=
  IsKKTMatrix x (fun i => trim A (x i)) A ∧ ∑ i, trim A (x i) = logInv δ / 3

/-- The trimmed mean `(1/n) Σᵢ (1 − min(1, xᵢ⊤Axᵢ)) xᵢ`. -/
noncomputable def trimmedMean {d n : ℕ} (x : Fin n → E d) (A : E d →L[ℝ] E d) : E d :=
  (1 / (n : ℝ)) • ∑ i, (1 - trim A (x i)) • x i

end LowDimMeanEst



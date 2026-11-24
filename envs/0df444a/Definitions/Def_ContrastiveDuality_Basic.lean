-- Prove2me | Definitions.Def_ContrastiveDuality_Basic
-- name    : ContrastiveDuality_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T06:28:48.734826+00:00
-- url     : https://prove2.me/theorems/549050ff-721f-4689-98f0-73c58d4bcf73
-- title:
--   Sample-contrastive and dimension-contrastive criteria of an embedding matrix
-- statement:
--   Objects of Section 3 and Appendix C of Garrido, Chen, Bardes, Najman and LeCun (ICLR 2023).
--
--   1. **Embedding matrix.** A batch of $N$ embeddings of dimension $M$ is a real matrix $\mathcal K\in\mathbb{R}^{M\times N}$ whose $i$-th column $\mathcal K_{\cdot,i}$ is the embedding of the $i$-th sample and whose $j$-th row $\mathcal K_{j,\cdot}$ is the $j$-th embedding dimension across the batch. $\|\mathcal K_{\cdot,i}\|_2$ and $\|\mathcal K_{j,\cdot}\|_2$ are the Euclidean norms of a column and a row.
--   2. **Extracted diagonal (Definition 3.1).** For $A\in\mathbb{R}^{n\times n}$, $\operatorname{diag}(A)\in\mathbb{R}^{n\times n}$ has entries $\operatorname{diag}(A)_{i,i}=A_{i,i}$ and $\operatorname{diag}(A)_{i,j}=0$ for $i\ne j$.
--   3. **Frobenius norm.** $\|A\|_F^2=\sum_{i,j}A_{i,j}^2$ for a real matrix $A$ of any shape.
--   4. **Criteria (Definition 3.2).** The sample-contrastive criterion is $L_c=\|\mathcal K^T\mathcal K-\operatorname{diag}(\mathcal K^T\mathcal K)\|_F^2$, the sum of the squared off-diagonal entries of the Gram matrix $\mathcal K^T\mathcal K\in\mathbb{R}^{N\times N}$. The dimension-contrastive criterion is $L_{nc}=\|\mathcal K\mathcal K^T-\operatorname{diag}(\mathcal K\mathcal K^T)\|_F^2$, the sum of the squared off-diagonal entries of $\mathcal K\mathcal K^T\in\mathbb{R}^{M\times M}$.
--   5. **Uniform law on the sphere (Lemma C.1).** $\sigma^{D-1}$ is the uniform probability measure on the unit sphere $S^{D-1}\subset\mathbb{R}^D$, viewed as a measure on $\mathbb{R}^D$.
--
--   **Formalization Note** Matrices are indexed by $\{0,\dots,M-1\}\times\{0,\dots,N-1\}$. The uniform law is the normalised rotation-invariant surface measure of the sphere, built from Lebesgue measure by Mathlib's `Measure.toSphere`; for $D=0$ the sphere is empty and the construction gives the zero measure, a case no statement uses.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Section 3, Definitions 3.1-3.2, eq. (1), p. 3; Appendix C, Lemma C.1, p. 14

import Mathlib

/-!
Garrido, Chen, Bardes, Najman and LeCun, *On the duality between contrastive and non-contrastive
self-supervised learning*, arXiv:2206.02574v3 (ICLR 2023): the extracted diagonal, the
sample-contrastive and dimension-contrastive criteria and the row and column norms of an
embedding matrix (Section 3, Definitions 3.1 and 3.2), and the uniform law on the unit sphere
(Appendix C, Lemma C.1).
-/

open MeasureTheory Matrix

noncomputable section

namespace ContrastiveDuality

/-- Definition 3.1 (Section 3, eq. (1), p. 3): the extracted diagonal `diag(A)` of a square
matrix `A`, which keeps the diagonal entries of `A` and sets every other entry to `0`. -/
def extractedDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => A i i

/-- The squared Frobenius norm `‖A‖_F² = ∑_{i,j} A_{i,j}²` used in Definition 3.2
(Section 3, p. 3). -/
def frobSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Section 3, p. 3: the Euclidean norm `‖K_{·,i}‖₂` of the `i`-th column of the embedding matrix
`K ∈ ℝ^{M×N}`, that is, of the embedding of the `i`-th sample of the batch. -/
def colNorm {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) (i : Fin N) : ℝ :=
  Real.sqrt (∑ j, K j i ^ 2)

/-- Section 3, p. 3: the Euclidean norm `‖K_{j,·}‖₂` of the `j`-th row of the embedding matrix
`K ∈ ℝ^{M×N}`, that is, of the `j`-th embedding dimension across the batch. -/
def rowNorm {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) (j : Fin M) : ℝ :=
  Real.sqrt (∑ i, K j i ^ 2)

/-- Definition 3.2 (Section 3, p. 3): the sample-contrastive (contrastive) criterion
`L_c = ‖KᵀK - diag(KᵀK)‖_F²` of an embedding matrix `K ∈ ℝ^{M×N}`. -/
def contrastiveCriterion {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) : ℝ :=
  frobSq (Kᵀ * K - extractedDiag (Kᵀ * K))

/-- Definition 3.2 (Section 3, p. 3): the dimension-contrastive (non-contrastive) criterion
`L_nc = ‖KKᵀ - diag(KKᵀ)‖_F²` of an embedding matrix `K ∈ ℝ^{M×N}`. -/
def nonContrastiveCriterion {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) : ℝ :=
  frobSq (K * Kᵀ - extractedDiag (K * Kᵀ))

/-- Lemma C.1 (Appendix C, p. 14): the uniform probability law `σ^{D-1}` on the unit sphere
`S^{D-1} ⊂ ℝ^D`, as a measure on `ℝ^D`: the rotation-invariant surface measure of the sphere
(Mathlib's `Measure.toSphere` of Lebesgue measure), pushed into `ℝ^D` and normalised to total
mass `1`. -/
def uniformSphere (D : ℕ) : Measure (EuclideanSpace ℝ (Fin D)) :=
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin D))).toSphere.map Subtype.val
  (μ Set.univ)⁻¹ • μ

end ContrastiveDuality



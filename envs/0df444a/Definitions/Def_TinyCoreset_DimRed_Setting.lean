-- Prove2me | Definitions.Def_TinyCoreset_DimRed_Setting
-- name    : TinyCoreset_DimRed_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:48.79867+00:00
-- url     : https://prove2.me/theorems/43e1a729-224d-41fc-a3fe-69b123c9eb20
-- title:
--   §2, pp. 603–605 — rows, squared distances, Frobenius norm and singular values
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ have rows $a_1,\ldots,a_n\in\mathbb R^d$. For a nonempty set $C\subseteq\mathbb R^d$, define the sum of squared row distances by
--
--   $$\operatorname{dist}^2(A,C)=\sum_{i=1}^n\inf_{c\in C}\|a_i-c\|_2^2.$$
--
--   For nonnegative weights $w_i$, the weighted version inserts $w_i$ in each summand. For a matrix $M$, set $\|M\|_F^2=\sum_{i,k}M_{ik}^2$. For an $n\times d$ rectangular SVD matrix $\Sigma$, $\sigma_i(\Sigma)$ is its $i$th diagonal entry when $1\le i\le\min\{n,d\}$, and zero otherwise.
--
--   These definitions fix the data geometry used in the dimensionality reduction result and can be reused for the companion affine subspace coreset mission.
--
--   **Formalization Note** Mathlib's real-valued distance to the empty set is zero. The statements using $\operatorname{dist}^2(A,C)$ therefore explicitly require $C$ to be nonempty. The weighted helper accepts arbitrary real weights; applications use the paper's nonnegative weights. The singular-value index is one-based; the value at index zero is defined as zero. The SVD truncation keeps zero-based diagonal positions below $m$.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), pp. 603–605, §2 and Definition 1, https://doi.org/10.1137/18M1209854

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD

namespace TinyCoreset.DimRed

open scoped Matrix

/-- The `i`-th row of a data matrix as a point of Euclidean space. -/
def row {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (A i)

/-- Sum of squared distances from the rows of `A` to a nonempty shape `C`. -/
noncomputable def distSq {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (C : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ∑ i, Metric.infDist (row A i) C ^ 2

/-- Weighted sum of squared distances from the rows of `S` to `C`. -/
noncomputable def wDistSq {r d : ℕ} (w : Fin r → ℝ)
    (S : Matrix (Fin r) (Fin d) ℝ) (C : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ∑ i, w i * Metric.infDist (row S i) C ^ 2

/-- Square of the Frobenius norm of a real matrix. -/
def frobSq {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  ∑ i, ∑ k, M i k ^ 2

/-- The `i`-th diagonal entry of a rectangular SVD matrix, with 1-based indexing. -/
def sigma {n d : ℕ} (S : Matrix (Fin n) (Fin d) ℝ) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ min n d then
    S ⟨i - 1, by omega⟩ ⟨i - 1, by omega⟩
  else 0

end TinyCoreset.DimRed



-- Prove2me | Definitions.Def_ShapleyNV_shapleyA
-- name    : ShapleyNV_shapleyA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:54.021083+00:00
-- url     : https://prove2.me/theorems/770c8e9e-2bd9-4e7f-ab9d-508898666085
-- title:
--   Pairwise interpolation matrix $A_{jk}(x)$ of the Shapley extension
-- statement:
--   Given an in-sample policy $\hat f$ and a point $x \in \mathcal X$, define for $j \ne k$
--
--   $$
--   A_{jk}(x) := \frac{\|x - \hat x_k\|}{\|x - \hat x_j\| + \|x - \hat x_k\|}\, \hat f(\hat x_j) + \frac{\|x - \hat x_j\|}{\|x - \hat x_j\| + \|x - \hat x_k\|}\, \hat f(\hat x_k),
--   $$
--
--   and $A_{kk}(x) := \hat f(\hat x_k)$. On the segment between $\hat x_j$ and $\hat x_k$ this is linear interpolation; elsewhere it is a two-point inverse-distance weighting. The matrix is symmetric: $A_{jk} = A_{kj}$.
--
--   **Formalization Note** For $j \ne k$ the denominator is positive because the $\hat x_k$ are distinct.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma 1, (S), p.7; Theorem 1 (II), p.6

import Mathlib
import Definitions.Def_ShapleyNV_Data

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **The matrix `A_jk(x)` of the Shapley extension**, (S).
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma 1, (S), p.7; Theorem 1 (II), p.6:
`A_jk(x) := ‖x − x̂_k‖/(‖x − x̂_j‖ + ‖x − x̂_k‖) f̂(x̂_j) + ‖x − x̂_j‖/(‖x − x̂_j‖ + ‖x − x̂_k‖) f̂(x̂_k)`
when `j ≠ k`, and `A_kk(x) := f̂(x̂_k)`.

**Formalization Note.** `f̂(x̂_k)` is `y k`. The diagonal case is the `if`, as in Lemma 1 (S)
(Theorem 1's single formula is `0/0` at `j = k`, `x = x̂_k`). For `j ≠ k` the denominator is
positive because the `x̂_k` are distinct, so Lean's `x / 0 = 0` never occurs. By construction
`A_jk = A_kj`. -/
noncomputable def shapleyA {X : Type*} [MetricSpace X] (D : Data X) (y : Fin D.K → ℝ) (j k : Fin D.K)
    (x : X) : ℝ :=
  if j = k then y k else
    dist x (D.xhat k) / (dist x (D.xhat j) + dist x (D.xhat k)) * y j +
      dist x (D.xhat j) / (dist x (D.xhat j) + dist x (D.xhat k)) * y k

end ShapleyNV



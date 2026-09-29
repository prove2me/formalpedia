-- Prove2me | Definitions.Def_HighDimStat_Pca_L2Norm
-- name    : HighDimStat_Pca_L2Norm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:11:16.519335+00:00
-- url     : https://prove2.me/theorems/78a05e17-3bd1-4fd3-ae49-0dc23bf80e4c
-- title:
--   The l2-norm of a vector in R^d
-- statement:
--   This is the **Euclidean (`ℓ²`) norm** of a vector, used throughout Wainwright's
--   *High-Dimensional Statistics* Chapter 8 to measure eigenvector estimation error, e.g.
--   `‖θ̂ − θ*‖₂` in Theorem 8.5.
--
--   For $v = (v_1,\dots,v_d) \in \mathbb R^d$,
--
--   $$
--   \|v\|_2 \;:=\; \Bigl(\sum_{j=1}^d v_j^2\Bigr)^{1/2}.
--   $$
--
--   **Formalization Note** Defined directly as `Real.sqrt` of the sum of squares over the
--   finite index type `Fin d`, matching the book's own Euclidean norm notation.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, Chapter 8

import Mathlib

namespace HighDimStat.Pca

/-- The Euclidean (`ℓ²`) norm of a vector `v ∈ ℝ^d`, `‖v‖₂ := (∑ⱼ vⱼ²)^{1/2}`, as used throughout
Wainwright, *High-Dimensional Statistics* (2019), Chapter 8 (e.g. Theorem 8.5's error bound
`‖θ̂ − θ*‖₂`). -/
noncomputable def l2Norm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ j, (v j) ^ 2)

end HighDimStat.Pca



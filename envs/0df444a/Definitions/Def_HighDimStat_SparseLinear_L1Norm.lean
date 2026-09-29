-- Prove2me | Definitions.Def_HighDimStat_SparseLinear_L1Norm
-- name    : HighDimStat_SparseLinear_L1Norm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:04:20.285936+00:00
-- url     : https://prove2.me/theorems/561e9c88-6ed2-46c4-abdf-6f51b3eb96b6
-- title:
--   The l1-norm of a vector in R^d
-- statement:
--   This is the **`ℓ¹`-norm** of a vector, used throughout Wainwright's *High-Dimensional
--   Statistics* Chapter 7 to define both the basis pursuit program (7.9) and the penalty term
--   of the Lagrangian Lasso (7.18).
--
--   For $\theta = (\theta_1, \dots, \theta_d) \in \mathbb R^d$,
--
--   $$
--   \|\theta\|_1 \;:=\; \sum_{j=1}^d |\theta_j|.
--   $$
--
--   **Formalization Note** Defined directly as the sum of absolute values over the finite
--   index type `Fin d`, matching the book's own notation; this is not tied to any Mathlib
--   `Norm` instance, so it composes freely with the other norms this mission defines.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 200 (PDF p. 220), Eq. (7.9)

import Mathlib

namespace HighDimStat.SparseLinear

/-- The `ℓ¹`-norm of a vector `θ ∈ ℝ^d`, `‖θ‖₁ := ∑ⱼ |θⱼ|`, as used throughout Wainwright,
*High-Dimensional Statistics* (2019), Chapter 7 (e.g. the basis pursuit program (7.9) and the
Lagrangian Lasso (7.18)). -/
noncomputable def l1Norm {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ j, |θ j|

end HighDimStat.SparseLinear



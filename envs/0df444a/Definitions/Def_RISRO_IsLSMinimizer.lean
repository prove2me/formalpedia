-- Prove2me | Definitions.Def_RISRO_IsLSMinimizer
-- name    : RISRO_IsLSMinimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:32:04.480995+00:00
-- url     : https://prove2.me/theorems/a0b8e3dd-5b5a-4c9c-8d5e-3bb80ba73722
-- title:
--   Solution of the least squares problem (5)
-- statement:
--   The triple $(B,D_1,D_2)$ is a **solution of (5)** when it minimizes the sketched objective over all $B\in\mathbb R^{r\times r}$, $D_1\in\mathbb R^{(p_1-r)\times r}$, $D_2\in\mathbb R^{(p_2-r)\times r}$.
--
--   **Formalization Note.** This is a predicate rather than a function, since without a restricted isometry hypothesis the minimizer need not be unique.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Algorithm 1, step 4, display (5), p.6

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_sketchObjective

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- `(B, D₁, D₂)` is a solution of the unconstrained least squares problem (5).

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Algorithm 1, step 4, display (5), p.6.

Formalization Note: a predicate, not a function: without an RIP hypothesis the minimizer need not
be unique, and every minimizer is admitted. A minimizer always exists. -/
def IsLSMinimizer {p₁ p₂ n r : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) (D₁ : Matrix (Fin (p₁ - r)) (Fin r) ℝ)
    (D₂ : Matrix (Fin (p₂ - r)) (Fin r) ℝ) : Prop :=
  ∀ (B' : Matrix (Fin r) (Fin r) ℝ) (D₁' : Matrix (Fin (p₁ - r)) (Fin r) ℝ)
    (D₂' : Matrix (Fin (p₂ - r)) (Fin r) ℝ),
    sketchObjective A y U Uc V Vc B D₁ D₂ ≤ sketchObjective A y U Uc V Vc B' D₁' D₂'

end RISRO



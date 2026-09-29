-- Prove2me | Definitions.Def_HighDimStat_TailBounds_IsLLipschitz
-- name    : HighDimStat_TailBounds_IsLLipschitz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:00.528271+00:00
-- url     : https://prove2.me/theorems/8d1c30d9-f30f-4af2-bd34-7459123a3777
-- title:
--   An L-Lipschitz function with respect to the Euclidean norm
-- statement:
--   A function $f:\mathbb R^n\to\mathbb R$ is $L$-**Lipschitz** with respect to the Euclidean
--   norm $\|\cdot\|_2$ if
--
--   $$
--   |f(x)-f(y)| \;\le\; L\|x-y\|_2 \qquad \text{for all } x,y\in\mathbb R^n.
--   $$
--
--   This is the regularity condition Theorem 2.26 concludes dimension-free Gaussian
--   concentration from.
--
--   **Formalization Note** Realized on `EuclideanSpace ℝ (Fin n)` (rather than the bare product
--   type `Fin n → ℝ`) so that `‖·‖` is genuinely the Euclidean norm the book's Eq. (2.38) uses.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 40 (PDF p. 60), Eq. (2.38)

import Mathlib

namespace HighDimStat.TailBounds

/-- Eq. (2.38), Wainwright, *High-Dimensional Statistics* (2019), p. 40. A function
`f : ℝ^n → ℝ` is `L`-Lipschitz with respect to the Euclidean norm `‖·‖₂` if
`|f(x) - f(y)| ≤ L‖x-y‖₂` for all `x, y ∈ ℝ^n`. Realized on `EuclideanSpace ℝ (Fin n)`, so `‖·‖`
is genuinely the Euclidean norm the book uses. -/
def IsLLipschitz {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin n), |f x - f y| ≤ L * ‖x - y‖

end HighDimStat.TailBounds



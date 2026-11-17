-- Prove2me | Definitions.Def_HirschDim4_Setting
-- name    : HirschDim4_Setting
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-16T22:52:46.365068+00:00
-- url     : https://prove2.me/theorems/2ea8faac-41c3-4282-933b-923f9cba3743
-- title:
--   Integer H-representations in $\mathbb{R}^4$
-- statement:
--   This file fixes the exact-data convention for the dimension-$4$ Hirsch mission. An integer matrix $A\in\mathbb{Z}^{n\times 4}$ and an integer vector $b\in\mathbb{Z}^n$ are read into real H-representation data: `intRows A` is the list of row normals $a_i\in\mathbb{R}^4$ and `intRhs b` the right-hand sides $b_i\in\mathbb{R}$, so that `Hirsch.Hpoly (intRows A) (intRhs b)` is the polytope $\{x\in\mathbb{R}^4:Ax\le b\}$. Integer data are equivalent to a rational polytope (clearing denominators), matching the benchmark's request for an explicit rational counterexample with an exact integer H-representation. These coercion helpers are reused by the goal theorem.
-- source:
--   Epoch AI, FrontierMath: Open Problems, The Hirsch Conjecture in Dimension 4, https://epoch.ai/frontiermath/open-problems/hirsch-conjecture (submission format: integer matrix A and integer vector b).

import Mathlib

open scoped RealInnerProductSpace

namespace HirschDim4

noncomputable section

/-- The rows of an integer matrix `A`, viewed as normal vectors in `ℝ⁴`. Together with
`intRhs` this turns an exact integer H-representation into the platform's real `Hpoly` data. -/
def intRows {n : ℕ} (A : Matrix (Fin n) (Fin 4) ℤ) :
    Fin n → EuclideanSpace ℝ (Fin 4) :=
  fun i => WithLp.toLp 2 (fun j => (A i j : ℝ))

/-- An integer right-hand side, viewed in `ℝ`. -/
def intRhs {n : ℕ} (b : Fin n → ℤ) : Fin n → ℝ := fun i => (b i : ℝ)

end

end HirschDim4



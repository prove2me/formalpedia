-- Prove2me | Definitions.Def_ProjNewton_Superlinear_Geometry
-- name    : ProjNewton_Superlinear_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:33.669362+00:00
-- url     : https://prove2.me/theorems/de2efe98-7b62-4f7e-a62e-38c872b6b5e0
-- title:
--   Euclidean vectors, nonnegative orthant, positive-part projection, gradient and Hessian
-- statement:
--   Represent $\mathbb R^n$ with its Euclidean norm for a finite dimension $n$. The feasible set of problem (1) is the nonnegative orthant,
--
--   $$\mathbb R_+^n=\{x\in\mathbb R^n:x^i\ge0\text{ for every }i\}.$$
--
--   The positive-part projection is $[z]^+=(\max(0,z^i))_i$. The $i$th partial derivative is the $i$th coordinate of $\nabla f(x)$; the $ij$ Hessian entry is the $i$th coordinate of the derivative of $\nabla f$ in the $j$th coordinate direction. The Hessian quadratic form is $z^\top\nabla^2f(x)z$. These definitions supply the shared Euclidean objects used by the paper's algorithm and results.
--
--   **Formalization Note** Coordinates use `Fin n`, indexed from zero in Lean rather than from one as in the paper. The derivative operations have default values where derivatives do not exist; theorems include $n\ge1$ and the differentiability required by the source.
-- source:
--   Bertsekas, Projected Newton Methods for Optimization Problems with Simple Constraints, SIAM J. Control Optim. 20(2) (1982), pp. 221–225, problem (1), (3), positive-part projection, notation

import Mathlib

namespace ProjNewton.Superlinear

open Matrix Filter Topology Finset

variable {n : ℕ}

/-- The paper's Euclidean space of coordinate vectors. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Coordinatewise positive part, displayed on p. 222. -/
def posPart (z : Vec n) : Vec n := WithLp.toLp 2 (fun i => max 0 (z i))

/-- The feasible set in problem (1). -/
def orthant (n : ℕ) : Set (Vec n) := {x | ∀ i, 0 ≤ x i}

/-- The ith component of the gradient. -/
noncomputable def pd (f : Vec n → ℝ) (x : Vec n) (i : Fin n) : ℝ := gradient f x i

/-- The ij entry of the Hessian, as the derivative of the gradient. -/
noncomputable def pd2 (f : Vec n → ℝ) (x : Vec n) (i j : Fin n) : ℝ :=
  fderiv ℝ (gradient f) x (EuclideanSpace.single j 1) i

/-- The Hessian quadratic form. -/
noncomputable def hessForm (f : Vec n → ℝ) (x : Vec n) (z : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, z i * pd2 f x i j * z j

end ProjNewton.Superlinear



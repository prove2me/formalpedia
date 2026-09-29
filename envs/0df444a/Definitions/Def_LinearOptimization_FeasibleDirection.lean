-- Prove2me | Definitions.Def_LinearOptimization_FeasibleDirection
-- name    : LinearOptimization_FeasibleDirection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T17:22:04.9077+00:00
-- url     : https://prove2.me/theorems/0a788134-aebe-4ed6-87eb-4b7125d93205
-- title:
--   Feasible direction at a point of a polyhedron
-- statement:
--   **(Definition 3.1)** Let $x$ be an element of a polyhedron $P$. A vector $d \in \mathbb{R}^n$ is said to be a *feasible direction* at $x$, if there exists a positive scalar $\theta$ for which
--
--   $$x + \theta d \in P.$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 3.1, p. 83

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_BasicSolution

/-!
Feasible directions and the basic directions of the simplex method.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997:

- **Definition 3.1 (p. 83).** "Let `x` be an element of a polyhedron `P`.
  A vector `d ∈ ℝⁿ` is said to be a *feasible direction* at `x`, if there
  exists a positive scalar `θ` for which `x + θd ∈ P`."
- **Eq. (3.1) (p. 83)** and surrounding text: at a basic feasible solution
  `x` of the standard-form problem with basis `B`, the `j`th *basic
  direction* `d` (for a nonbasic index `j`) is defined by `d_j = 1`,
  `d_i = 0` for every other nonbasic index `i`, and `d_B = −B⁻¹A_j`.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Definition 3.1 (p. 83).** `d` is a feasible direction at `x`:
there is a positive scalar `θ` with `x + θ • d ∈ S`. (Stated for an
arbitrary set `S` so that it applies to `polyhedron` and `stdPolyhedron`
alike.) -/
def IsFeasibleDirection {n : ℕ} (S : Set (Fin n → ℝ)) (x d : Fin n → ℝ) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ x + θ • d ∈ S

/-- **Bertsimas & Tsitsiklis, Eq. (3.1) (p. 83).** The `j`th basic direction at the basis `B`:
the `j`th component is `1`, the basic components are `d_B = −B⁻¹A_j`
(so `d (B i) = −(B⁻¹A_j) i`), and every other component is `0`. The book
uses this only for nonbasic `j`; for `j` in the range of `B` the formula is
never invoked, and `B⁻¹` is Lean's `Matrix.inv`, guarded by `IsStdBasis A B`
(which makes `basisMatrix A B` invertible) wherever the direction is used. -/
noncomputable def basicDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Fin m ↪ Fin n) (j : Fin n) : Fin n → ℝ :=
  Pi.single j 1 -
    ∑ i : Fin m, Pi.single (B i) ((basisMatrix A B)⁻¹.mulVec (fun i' => A i' j) i)

end LinearOptimization



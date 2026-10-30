-- Prove2me | Definitions.Def_CubicRegNewton_LocalQuad_cubicModel
-- name    : CubicRegNewton_LocalQuad_cubicModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:25:05.362396+00:00
-- url     : https://prove2.me/theorems/0103097b-9223-482f-a29d-d710f3296d28
-- title:
--   Cubic regularization of the quadratic model (2.4)
-- statement:
--   For a point $x$, a parameter $M$ and $y\in\mathbb R^n$, the **cubic model** of $f$ at $x$ is
--
--   $$
--   \langle f'(x),y-x\rangle+\tfrac12\langle f''(x)(y-x),y-x\rangle+\frac M6\|y-x\|^3 .
--   $$
--
--   For $M>0$ the modified Newton step $T_M(x)$ of (2.4) is a global minimizer of this function of $y$ over $\mathbb R^n$; the paper's "Arg" means that any global minimizer may be chosen.
--
--   **Formalization Note** "$T$ is a value of $T_M(x)$" is written `IsMinOn (cubicModel f' f'' M x) Set.univ T`.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, doi:10.1007/s10107-006-0706-8, (2.4), p. 181 (PDF p. 5)

import Mathlib

open scoped InnerProductSpace

namespace CubicRegNewton.LocalQuad

/-- **The cubic regularization of the quadratic model, (2.4).**
Nesterov & Polyak, *Cubic regularization of Newton method and its global performance*,
Math. Program. Ser. A 108 (2006) 177–205, (2.4), p. 181: "Let M be a positive parameter. Define a
modified Newton step using the following cubic regularization of quadratic approximation of
function f(x): T_M(x) ∈ Arg min_y [⟨f'(x), y − x⟩ + ½⟨f''(x)(y − x), y − x⟩ + (M/6)‖y − x‖³],
(2.4) where “Arg” indicates that T_M(x) is chosen from the set of global minima of corresponding
minimization problem."

`cubicModel f' f'' M x y` is the bracket of (2.4) at the point `y`.

**Formalization Note.** Reading 7: "T is a value of T_M(x)" is written
`IsMinOn (cubicModel f' f'' M x) Set.univ T`, i.e. `T` is any global minimizer over all of ℝⁿ. The
inner product is the real inner product of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def cubicModel {n : ℕ}
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪f' x, y - x⟫_ℝ + (1 / 2) * ⟪f'' x (y - x), y - x⟫_ℝ + M / 6 * ‖y - x‖ ^ 3

end CubicRegNewton.LocalQuad



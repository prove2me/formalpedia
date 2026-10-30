-- Prove2me | Definitions.Def_CubicRegNewton_LocalQuad_IsRelaxedCubicRun
-- name    : CubicRegNewton_LocalQuad_IsRelaxedCubicRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:26:26.42007+00:00
-- url     : https://prove2.me/theorems/73ffe962-ea8a-4669-917e-f6ef56c4d691
-- title:
--   A run of the relaxed cubic Newton scheme (3.5)
-- statement:
--   Sequences of points $(x_k)_{k\ge0}$ in $\mathbb R^n$ and parameters $(M_k)_{k\ge0}$ form a **run of the relaxed cubic Newton scheme** (3.5) when, for every $k\ge0$,
--
--   $$
--   M_k\in(0,2L]\quad\text{and}\quad x_{k+1}=T_{M_k}(x_k),
--   $$
--
--   that is, $x_{k+1}$ is a global minimizer of the cubic model (2.4) at $x_k$ with parameter $M_k$.
--
--   Unlike the basic scheme (3.3), there is no lower bound $M_k\ge L_0$ and no acceptance test: any parameter in $(0,2L]$ may be used at each step.
--
--   **Formalization Note** The starting point is not part of the predicate; theorems add $x_0$ separately.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, doi:10.1007/s10107-006-0706-8, (3.5), p. 186 (PDF p. 10)

import Mathlib
import Definitions.Def_CubicRegNewton_LocalQuad_cubicModel

namespace CubicRegNewton.LocalQuad

/-- **A run of the relaxed cubic Newton scheme (3.5).**
Nesterov & Polyak, *Cubic regularization of Newton method and its global performance*,
Math. Program. Ser. A 108 (2006) 177–205, (3.5), p. 186: "Let us analyze a relaxed version of
(3.3): xk+1 = TMk(xk), k ≥ 0 (3.5) where Mk ∈ (0, 2L]."

`IsRelaxedCubicRun f' f'' L x M` says that for every `k`, `0 < M k ≤ 2L` and `x (k+1)` is a global
minimizer over ℝⁿ of the cubic model (2.4) at `x k` with parameter `M k`.

**Formalization Note.**
* Reading 7: `T_{M_k}(x_k)` is any global minimizer of the model; the run picks one per step.
* There is no lower bound `L₀ ≤ M_k` and no acceptance test: those belong to scheme (3.3), not
  to (3.5).
* The starting point is not part of the predicate; the theorems add `x 0 = x₀` (Reading 9). -/
def IsRelaxedCubicRun {n : ℕ}
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < M k ∧ M k ≤ 2 * L ∧ IsMinOn (cubicModel f' f'' (M k) (x k)) Set.univ (x (k + 1))

end CubicRegNewton.LocalQuad



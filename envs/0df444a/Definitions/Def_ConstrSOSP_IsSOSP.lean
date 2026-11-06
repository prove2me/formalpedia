-- Prove2me | Definitions.Def_ConstrSOSP_IsSOSP
-- name    : ConstrSOSP_IsSOSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:21.055027+00:00
-- url     : https://prove2.me/theorems/1d476a29-db3b-4fd8-beb8-bf4951ad3401
-- title:
--   $(\epsilon_G,\epsilon_H)$-SOSP at an interior point (Definition 4.9)
-- statement:
--   A point $x^*\in\operatorname{int}\mathcal X$ is an **$(\epsilon_G,\epsilon_H)$-SOSP** if
--   $$
--   \|\nabla f(x^*)\|\le\epsilon_G,\qquad \nabla^2f(x^*)\succeq-\epsilon_H I,
--   $$
--   the second condition being $y^\top\nabla^2f(x^*)y\ge-\epsilon_H$ for every unit vector $y$ (11b).
--
--   **Formalization Note** The interior is the topological interior of $\mathcal X$ in $\mathbb R^d$; gradient and Hessian values are data.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.9, p.21; (11a)–(11b), p.21

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ConstrSOSP_Poly

namespace ConstrSOSP

/-- **(ϵG, ϵH)-SOSP at an interior point** (arXiv:2604.02285, 2 Nov 2026, Definition 4.9, p.21:
"For ϵG, ϵH > 0, a point x* ∈ int X is an (ϵG, ϵH)-SOSP if ‖∇f(x*)‖ ≤ ϵG, ∇²f(x*) ⪰ −ϵH I.
(10)"; in Definition 4.10, p.21, the same as (11a)–(11b): "yᵀ∇²f(x*)y ≥ −ϵH, ∀ y ∈ ℝ^d s.t.
‖y‖ = 1").

`IsSOSP A b ϵG ϵH x g H` holds iff `x` is in the (topological) interior of `X = {Ax ≤ b}`, the
Euclidean norm of `g` is at most `ϵG`, and `yᵀHy ≥ −ϵH` for every Euclidean unit vector `y`.

**Formalization Note** `∇²f ⪰ −ϵH I` is written as the quadratic-form inequality (11b) over unit
vectors. `g`, `H` are the gradient and Hessian values at `x`. The topology of `Fin d → ℝ` is the
Euclidean one. -/
def IsSOSP {m d : ℕ} (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (ϵG ϵH : ℝ)
    (x g : Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  x ∈ interior (Poly A b) ∧ ApproxVI.euclNorm g ≤ ϵG ∧ ∀ y : Fin d → ℝ, ApproxVI.euclNorm y = 1 → -ϵH ≤ y ⬝ᵥ (Matrix.mulVec H y)

end ConstrSOSP



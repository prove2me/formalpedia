-- Prove2me | Definitions.Def_ConstrSOSP_IsSOSP1
-- name    : ConstrSOSP_IsSOSP1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:57.446901+00:00
-- url     : https://prove2.me/theorems/c6486bc4-d5a8-4d8b-a140-caf643f922b7
-- title:
--   $(\epsilon_G,\epsilon_H)$-SOSP1 (Definition 4.4)
-- statement:
--   Let $\mathcal X=\{Ax\le b\}$ and let $\mathcal A(x)=\{j: A_jx=b_j\}$ be the active constraints at $x$. A point $x^*\in\mathcal X$ is an **$(\epsilon_G,\epsilon_H)$-SOSP1** if
--
--   1. $\|g_\pi(x^*)\|\le\epsilon_G$ (first order), and
--   2. $y^\top\nabla^2f(x^*)\,y\ge-\epsilon_H$ for every unit vector $y$ with $A_jy=0$ for all $j\in\mathcal A(x^*)$ (second order).
--
--   **Formalization Note** The objective enters through its gradient value $g$ and Hessian value $H$ at $x^*$; norms are Euclidean.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.4, p.19; active set, p.8

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ConstrSOSP_Poly
import Definitions.Def_ConstrSOSP_ProxGradLE

namespace ConstrSOSP

/-- **(ϵG, ϵH)-SOSP1** (arXiv:2604.02285, 2 Nov 2026, Definition 4.4, p.19): "a point x* ∈ X is
an (ϵG, ϵH)-SOSP1 of problem (3) if: • ‖g_π(x*)‖ ≤ ϵG, (first order) (5a)
• yᵀ∇²f(x*)y ≥ −ϵH, ∀y s.t. A′(x*)y = 0, ‖y‖ = 1, (second order) (5b) where A′(x*) is the matrix
that collects the active constraints at x*." The active set is (p.8) `A(x) = {j : A_j x = b_j}`.

`IsSOSP1 A b L1 ϵG ϵH x g H` holds iff `x ∈ X = {Ax ≤ b}`, `‖g_π(x)‖ ≤ ϵG` (proximal gradient
with constant `L₁` and gradient value `g`), and `yᵀHy ≥ −ϵH` for every Euclidean unit vector `y`
with `A_j y = 0` for all active rows `j`.

**Formalization Note** The objective enters only through its gradient value `g = ∇f(x)` and
Hessian value `H = ∇²f(x)` at `x`. Norms are Euclidean (`ApproxVI.euclNorm`). -/
def IsSOSP1 {m d : ℕ} (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (L1 ϵG ϵH : ℝ)
    (x g : Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  x ∈ Poly A b ∧ ProxGradLE (Poly A b) L1 g x ϵG ∧
    ∀ y : Fin d → ℝ, (∀ j, A j ⬝ᵥ x = b j → A j ⬝ᵥ y = 0) → ApproxVI.euclNorm y = 1 → -ϵH ≤ y ⬝ᵥ (Matrix.mulVec H y)

end ConstrSOSP



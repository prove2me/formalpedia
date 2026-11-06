-- Prove2me | Definitions.Def_ConstrSOSP_IsSOSP2
-- name    : ConstrSOSP_IsSOSP2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:28.610457+00:00
-- url     : https://prove2.me/theorems/c95b9549-2d43-41f8-852b-d4b554ad4f80
-- title:
--   $(\epsilon_G,\epsilon_H)$-SOSP2 (Definition 4.7)
-- statement:
--   A point $x^*\in\mathcal X$ is an **$(\epsilon_G,\epsilon_H)$-SOSP2** if for every displacement $s$ with $x^*+s\in\mathcal X$ and $\|s\|\le1$:
--   $$
--   \nabla f(x^*)^\top s\ge-\epsilon_G,\qquad \nabla f(x^*)^\top s\le0\ \Longrightarrow\ s^\top\nabla^2f(x^*)\,s\ge-\epsilon_H .
--   $$
--
--   **Formalization Note** Gradient and Hessian values at $x^*$ are given as data; norms are Euclidean.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.7, p.20

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ConstrSOSP_Poly

namespace ConstrSOSP

/-- **(ϵG, ϵH)-SOSP2** (arXiv:2604.02285, 2 Nov 2026, Definition 4.7, p.20): "A point x* ∈ X is an
(ϵG, ϵH)-SOSP2 if, for every displacement s ∈ ℝ^d satisfying x* + s ∈ X and ‖s‖ ≤ 1, the following
conditions hold: ∇f(x*)ᵀs ≥ −ϵG, (8a) ∇f(x*)ᵀs ≤ 0 ⟹ sᵀ∇²f(x*)s ≥ −ϵH. (8b)"

`IsSOSP2 A b ϵG ϵH x g H` holds iff `x ∈ X = {Ax ≤ b}` and for every `s` with `x + s ∈ X` and
Euclidean `‖s‖ ≤ 1`: `gᵀs ≥ −ϵG`, and `gᵀs ≤ 0` implies `sᵀHs ≥ −ϵH`.

**Formalization Note** `g = ∇f(x)`, `H = ∇²f(x)` are the values at `x`. -/
def IsSOSP2 {m d : ℕ} (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (ϵG ϵH : ℝ)
    (x g : Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  x ∈ Poly A b ∧ ∀ s : Fin d → ℝ, x + s ∈ Poly A b → ApproxVI.euclNorm s ≤ 1 →
    -ϵG ≤ g ⬝ᵥ s ∧ (g ⬝ᵥ s ≤ 0 → -ϵH ≤ s ⬝ᵥ (Matrix.mulVec H s))

end ConstrSOSP



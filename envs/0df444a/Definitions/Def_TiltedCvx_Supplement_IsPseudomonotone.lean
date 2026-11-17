-- Prove2me | Definitions.Def_TiltedCvx_Supplement_IsPseudomonotone
-- name    : TiltedCvx_Supplement_IsPseudomonotone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:20:41.176519+00:00
-- url     : https://prove2.me/theorems/be21b9d9-6297-4f17-9ea1-f8a0e2d41cc4
-- title:
--   Pseudomonotone operator (Definition 11)
-- statement:
--   A set-valued operator $F:\mathbb R^d\rightrightarrows\mathbb R^d$ is **pseudomonotone** if for all $x,y\in\operatorname{dom}(F)$, $x^*\in F(x)$ and $y^*\in F(y)$,
--
--   $$
--   \langle x^*,y-x\rangle\ge0\ \Longrightarrow\ \langle y^*,y-x\rangle\ge0 .
--   $$
--
--   Pseudomonotonicity of the Clarke subdifferential characterizes pseudoconvexity of radially continuous functions (Theorem 3).
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 11, p.17

import Mathlib

open scoped InnerProductSpace

namespace TiltedCvx.Supplement

/-- **Pseudomonotone operator (Definition 11).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Definition 11, p.17: a set-valued operator `F : ℝ^d ⇒ ℝ^d` is pseudomonotone
if, for all `x, y ∈ dom(F)`, `x* ∈ F(x)` and `y* ∈ F(y)`, `⟨x*, y − x⟩ ≥ 0 ⟹ ⟨y*, y − x⟩ ≥ 0`.

**Formalization Note** `F : E → Set E`; `x ∈ dom F` is implied by `x* ∈ F x`. -/
def IsPseudomonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → Set E) : Prop :=
  ∀ x y xs ys : E, xs ∈ F x → ys ∈ F y → 0 ≤ ⟪xs, y - x⟫_ℝ → 0 ≤ ⟪ys, y - x⟫_ℝ

end TiltedCvx.Supplement



-- Prove2me | Definitions.Def_TiltedCvx_Supplement_IsQuasimonotone
-- name    : TiltedCvx_Supplement_IsQuasimonotone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:20:24.079455+00:00
-- url     : https://prove2.me/theorems/3a3410cb-d68f-485b-abf8-134529c85db5
-- title:
--   Quasimonotone operator (Definition 9)
-- statement:
--   A set-valued operator $F:\mathbb R^d\rightrightarrows\mathbb R^d$ is **quasimonotone** if for all $x,y\in\operatorname{dom}(F)$, $x^*\in F(x)$ and $y^*\in F(y)$,
--
--   $$
--   \langle x^*,y-x\rangle>0\ \Longrightarrow\ \langle y^*,y-x\rangle\ge0 .
--   $$
--
--   Quasimonotonicity of the Clarke subdifferential characterizes quasiconvexity of radially continuous functions (Theorem 2).
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 9, p.16

import Mathlib

open scoped InnerProductSpace

namespace TiltedCvx.Supplement

/-- **Quasimonotone operator (Definition 9).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Definition 9, p.16: a set-valued operator `F : ℝ^d ⇒ ℝ^d` is quasimonotone if, for all
`x, y ∈ dom(F)`, `x* ∈ F(x)` and `y* ∈ F(y)`, `⟨x*, y − x⟩ > 0 ⟹ ⟨y*, y − x⟩ ≥ 0`.

**Formalization Note** `F : E → Set E`; `x ∈ dom F` is implied by `x* ∈ F x`. -/
def IsQuasimonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → Set E) : Prop :=
  ∀ x y xs ys : E, xs ∈ F x → ys ∈ F y → 0 < ⟪xs, y - x⟫_ℝ → 0 ≤ ⟪ys, y - x⟫_ℝ

end TiltedCvx.Supplement



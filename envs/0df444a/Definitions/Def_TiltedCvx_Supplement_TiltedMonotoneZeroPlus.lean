-- Prove2me | Definitions.Def_TiltedCvx_Supplement_TiltedMonotoneZeroPlus
-- name    : TiltedCvx_Supplement_TiltedMonotoneZeroPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:22:26.095425+00:00
-- url     : https://prove2.me/theorems/975a20f4-624a-4fc4-8121-5dc25052d81f
-- title:
--   $0^+$–tilted monotone operator (Definition 12)
-- statement:
--   A set-valued operator $F:\mathbb R^d\rightrightarrows\mathbb R^d$ is **$0^+$–tilted monotone** if for all $x,y\in\operatorname{dom}(F)$, $x^*\in F(x)$ and $y^*\in F(y)$,
--
--   $$
--   \langle y^*,y-x\rangle\ \ge\ \psi_{0^+}\big(\langle x^*,y-x\rangle\big),
--   $$
--
--   which is the implication $\langle x^*,y-x\rangle\ge0\Rightarrow\langle y^*,y-x\rangle\ge0$, i.e. pseudomonotonicity.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 12, p.17

import Mathlib
import Definitions.Def_TiltedCvx_Supplement_psiZeroPlus

open scoped InnerProductSpace

namespace TiltedCvx.Supplement

/-- **0⁺–tilted monotone operator (Definition 12).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Definition 12, p.17: a set-valued operator `F : ℝ^d ⇒ ℝ^d` is 0⁺–tilted
monotone if, for all `x, y ∈ dom(F)`, `x* ∈ F(x)` and `y* ∈ F(y)`,
`⟨y*, y − x⟩ ≥ ψ_{0+}(⟨x*, y − x⟩)`.

**Formalization Note** `F : E → Set E`; `x ∈ dom F` is implied by `x* ∈ F x`. -/
def TiltedMonotoneZeroPlus {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → Set E) : Prop :=
  ∀ x y xs ys : E, xs ∈ F x → ys ∈ F y →
    psiZeroPlus ((⟪xs, y - x⟫_ℝ : ℝ) : EReal) ≤ ((⟪ys, y - x⟫_ℝ : ℝ) : EReal)

end TiltedCvx.Supplement



-- Prove2me | Definitions.Def_TiltedCvx_TiltedMonotone
-- name    : TiltedCvx_TiltedMonotone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:10.268882+00:00
-- url     : https://prove2.me/theorems/43fe596c-e3b7-4d0b-bffb-9dd484190cd1
-- title:
--   $\gamma$-tilted monotone operator
-- statement:
--   For $\gamma\in[0,1]$, a multi-valued operator $F:\mathbb R^d\rightrightarrows\mathbb R^d$ is **$\gamma$–tilted monotone** if for all $x,y\in\operatorname{dom}F$, $x^*\in F(x)$ and $y^*\in F(y)$,
--
--   $$
--   \langle y^*,y-x\rangle\ \ge\ \psi_\gamma\big(\langle x^*,y-x\rangle\big)=\gamma^{\operatorname{sign}\langle x^*,y-x\rangle}\langle x^*,y-x\rangle,
--   $$
--
--   whenever both sides are defined. For $\gamma=1$ this is monotonicity of $F$.
--
--   **Formalization Note** Membership $x\in\operatorname{dom}F$ is implied by $x^*\in F(x)$. The left side is always defined, so the proviso is `TiltDefined γ ⟨x*, y − x⟩`.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 4, (5), p.14

import Mathlib
import Definitions.Def_TiltedCvx_psi
import Definitions.Def_TiltedCvx_TiltDefined

open scoped InnerProductSpace

namespace TiltedCvx

/-- **γ–tilted monotone operator.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Definition 4, (5), p.14: `F : ℝ^d ⇒ ℝ^d` is γ–tilted monotone if for all `x, y ∈ dom F`,
`x* ∈ F(x)` and `y* ∈ F(y)`, `⟨y*, y − x⟩ ≥ ψγ(⟨x*, y − x⟩)` whenever both sides are
well-defined.

**Formalization Note** `F : E → Set E`; `x ∈ dom F` is implied by `x* ∈ F x`. The left side is
always defined, so the only definedness condition is `TiltDefined γ ⟨x*, y − x⟩`. -/
def TiltedMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (F : E → Set E) : Prop :=
  ∀ x y xs ys : E, xs ∈ F x → ys ∈ F y →
    TiltDefined γ ((⟪xs, y - x⟫_ℝ : ℝ) : EReal) →
      psi γ ((⟪xs, y - x⟫_ℝ : ℝ) : EReal) ≤ ((⟪ys, y - x⟫_ℝ : ℝ) : EReal)

end TiltedCvx



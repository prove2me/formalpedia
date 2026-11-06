-- Prove2me | Definitions.Def_TiltedCvx_TiltedConvexWrt
-- name    : TiltedCvx_TiltedConvexWrt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:14.988119+00:00
-- url     : https://prove2.me/theorems/c18873af-742d-4d4d-822e-bc21b23f435b
-- title:
--   $\gamma$-tilted convexity with respect to an operator
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$, let $F:\mathbb R^d\rightrightarrows\mathbb R^d$ be a multi-valued operator and $\gamma\in[0,1]$. The function $f$ is **$\gamma$–tilted convex with respect to $F$** if for all $x,y\in\operatorname{dom}(f)$ and $v\in F(x)$,
--
--   $$
--   f(y)-f(x)\ \ge\ \psi_\gamma\big(\langle y-x,v\rangle\big)
--   $$
--
--   whenever the right-hand side is defined. For $\gamma=1$ and $F$ a subdifferential this is the affine support inequality of a convex function.
--
--   **Formalization Note** $F$ is a map `E → Set E`. The paper states the definition for proper lsc $f$; these hypotheses belong to the classes and theorems that use the predicate, not to the predicate itself.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 3, (4), p.13

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_psi
import Definitions.Def_TiltedCvx_TiltDefined

open scoped InnerProductSpace

namespace TiltedCvx

/-- **γ–tilted convexity with respect to an operator.** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Definition 3, (4), p.13: `f` is γ–tilted convex with respect to
`F : ℝ^d ⇒ ℝ^d` if, for all `x, y ∈ dom(f)` and `v ∈ F(x)`,
`f(y) − f(x) ≥ ψγ(⟨y − x, v⟩)` whenever the right-hand side is well-defined.

**Formalization Note** A multi-valued operator is `F : E → Set E`. The paper states the
definition for proper lsc `f`; those hypotheses are not part of this predicate and are added
where it is used (the classes `classF` etc.). For `x, y ∈ dom f` the difference `f y − f x` is a
real number. -/
def TiltedConvexWrt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (f : E → EReal) (F : E → Set E) : Prop :=
  ∀ x ∈ effDom f, ∀ y ∈ effDom f, ∀ v ∈ F x,
    TiltDefined γ ((⟪y - x, v⟫_ℝ : ℝ) : EReal) →
      psi γ ((⟪y - x, v⟫_ℝ : ℝ) : EReal) ≤ f y - f x

end TiltedCvx



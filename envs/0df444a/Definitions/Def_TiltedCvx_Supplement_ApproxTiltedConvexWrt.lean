-- Prove2me | Definitions.Def_TiltedCvx_Supplement_ApproxTiltedConvexWrt
-- name    : TiltedCvx_Supplement_ApproxTiltedConvexWrt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:24:36.431175+00:00
-- url     : https://prove2.me/theorems/9bfb7fdd-2564-402f-841a-781c507e2ce8
-- title:
--   Approximate γ–tilted convexity (Definition 16)
-- statement:
--   Let $\gamma\in(0,1]$, $f:\mathbb R^d\to\overline{\mathbb R}$ proper and lower semicontinuous, and $F:\mathbb R^d\rightrightarrows\mathbb R^d$. The function $f$ is **approximately $\gamma$–tilted convex with respect to $F$** if for every $x\in\operatorname{dom}(f)\cap\operatorname{dom}(F)$ and every $\epsilon>0$ there is $v\in F(x)$ with
--
--   $$
--   f(y)-f(x)\ \ge\ \psi_\gamma(\langle y-x,v\rangle)-\epsilon\qquad\text{for all }y\in\operatorname{dom}(f).
--   $$
--
--   The supporting vector may depend on $\epsilon$; exact $\gamma$–tilted convexity with respect to $F$ implies the approximate version. It is the tool behind the regularity results (Theorems 35 and 36).
--
--   **Formalization Note** $\operatorname{dom}(F)=\{x:F(x)\ne\emptyset\}$. Properness, lower semicontinuity and $\gamma\in(0,1]$ are hypotheses of the theorems that use the predicate.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 16, p.54

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_psi

open scoped InnerProductSpace

namespace TiltedCvx.Supplement

/-- **Approximate γ–tilted convexity (Definition 16).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Definition 16, p.54: let `γ ∈ (0, 1]`, `f : ℝ^d → ℝ̄` proper lsc and
`F : ℝ^d ⇒ ℝ^d`. `f` is approximately γ–tilted convex with respect to `F` if, for every
`x ∈ dom(f) ∩ dom(F)` and every `ε > 0`, there is `v ∈ F(x)` such that
`f(y) − f(x) ≥ ψγ(⟨y − x, v⟩) − ε` for all `y ∈ dom(f)`.

**Formalization Note** `dom F = {x | F x ≠ ∅}`; the vector `v` may depend on `ε`. The inequality
is in `EReal`; for `γ > 0` and `x, y ∈ dom f` all its terms are real. "Proper lsc" and
`γ ∈ (0, 1]` are hypotheses of the theorems that use the predicate. -/
def ApproxTiltedConvexWrt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (f : E → EReal) (F : E → Set E) : Prop :=
  ∀ x ∈ TiltedCvx.effDom f, (F x).Nonempty → ∀ ε : ℝ, 0 < ε →
    ∃ v ∈ F x, ∀ y ∈ TiltedCvx.effDom f,
      TiltedCvx.psi γ ((⟪y - x, v⟫_ℝ : ℝ) : EReal) - (ε : EReal) ≤ f y - f x

end TiltedCvx.Supplement



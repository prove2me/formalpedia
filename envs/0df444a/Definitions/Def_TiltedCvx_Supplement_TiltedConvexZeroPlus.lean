-- Prove2me | Definitions.Def_TiltedCvx_Supplement_TiltedConvexZeroPlus
-- name    : TiltedCvx_Supplement_TiltedConvexZeroPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:21:55.290243+00:00
-- url     : https://prove2.me/theorems/6dfa7219-055e-47de-ab61-3160cd237828
-- title:
--   $0^+$–tilted convexity (Definition 12)
-- statement:
--   A proper lower semicontinuous $f:\mathbb R^d\to\overline{\mathbb R}$ is **$0^+$–tilted convex** if for all $x,y\in\operatorname{dom}(f)$ and $v\in\overline\partial f(x)$,
--
--   $$
--   f(y)-f(x)\ \ge\ \psi_{0^+}\big(\langle y-x,v\rangle\big),
--   $$
--
--   that is, $f(y)\ge f(x)$ whenever $\langle y-x,v\rangle\ge0$. Here $\overline\partial f$ is the Clarke–Rockafellar subdifferential.
--
--   **Formalization Note** "Proper lsc" is not part of the predicate; it is part of the class $\mathcal F^{0^+}$. There is no definedness clause, since $\psi_{0^+}$ is defined everywhere.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 12, p.17

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_ClarkeStrat_Proj_Setting
import Definitions.Def_TiltedCvx_Supplement_psiZeroPlus

open scoped InnerProductSpace
open ClarkeStrat.Proj

namespace TiltedCvx.Supplement

/-- **0⁺–tilted convexity (Definition 12).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Definition 12, p.17: a proper lsc `f : ℝ^d → ℝ̄` is 0⁺–tilted convex if, for all `x, y ∈ dom(f)`
and `v ∈ ∂̄f(x)`, `f(y) − f(x) ≥ ψ_{0+}(⟨y − x, v⟩)`.

**Formalization Note** `∂̄f` is the published `ClarkeStrat.Proj.ClarkeSubdiff`. There is no
definedness clause: `ψ_{0+}` is defined everywhere. "Proper lsc" is not part of this predicate; it
is part of the class `classZeroPlus`. -/
def TiltedConvexZeroPlus {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) : Prop :=
  ∀ x ∈ TiltedCvx.effDom f, ∀ y ∈ TiltedCvx.effDom f, ∀ v ∈ ClarkeSubdiff f x,
    psiZeroPlus ((⟪y - x, v⟫_ℝ : ℝ) : EReal) ≤ f y - f x

end TiltedCvx.Supplement



-- Prove2me | Definitions.Def_TiltedCvx_TiltedConvex
-- name    : TiltedCvx_TiltedConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:16.443206+00:00
-- url     : https://prove2.me/theorems/35846fd1-234e-4418-9076-3a082e36603c
-- title:
--   $\gamma$-tilted convexity
-- statement:
--   A function $f:\mathbb R^d\to\overline{\mathbb R}$ is **$\gamma$–tilted convex** if it is $\gamma$–tilted convex with respect to its Clarke–Rockafellar subdifferential
--
--   $$
--   \bar\partial f(x)=\operatorname{cl}\big(\operatorname{conv}\partial f(x)+\operatorname{conv}\partial^\infty f(x)\big),
--   $$
--
--   that is, $f(y)-f(x)\ge\psi_\gamma(\langle y-x,v\rangle)$ for all $x,y\in\operatorname{dom}(f)$ and $v\in\bar\partial f(x)$, whenever the right side is defined. Here $\partial f$ is the limiting and $\partial^\infty f$ the horizon subdifferential.
--
--   **Formalization Note** $\bar\partial f$ is the published `ClarkeStrat.Proj.ClarkeSubdiff`: the closed convex hull of $\partial f(x)+\partial^\infty f(x)$ where $f(x)<+\infty$ and $\emptyset$ otherwise. This equals the paper's formula because $\operatorname{conv}(A+B)=\operatorname{conv}A+\operatorname{conv}B$; the published horizon subdifferential asks the scaling sequence to be nonincreasing, which restricts nothing (pass to a subsequence). Both facts are checked in the mission's verification files.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 3, p.13; Definition 2, p.11

import Mathlib
import Definitions.Def_TiltedCvx_TiltedConvexWrt
import Definitions.Def_ClarkeStrat_Proj_Setting

open ClarkeStrat.Proj

namespace TiltedCvx

/-- **γ–tilted convexity.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Definition 3,
p.13: `f` is γ–tilted convex if it is γ–tilted convex with respect to its Clarke–Rockafellar
subdifferential `∂̄f`.

**Formalization Note** `∂̄f` is the published `ClarkeStrat.Proj.ClarkeSubdiff`: the closed convex
hull of `∂f(x) + ∂^∞f(x)` for `f x ≠ +∞`, and `∅` otherwise. This equals the paper's
`cl(conv ∂f(x) + conv ∂^∞f(x))` (Definition 2, p.11), since `conv(A + B) = conv A + conv B`. -/
def TiltedConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (f : E → EReal) : Prop :=
  TiltedConvexWrt γ f (ClarkeSubdiff f)

end TiltedCvx



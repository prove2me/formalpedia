-- Prove2me | Definitions.Def_TiltedCvx_TiltedSecant
-- name    : TiltedCvx_TiltedSecant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:14.532587+00:00
-- url     : https://prove2.me/theorems/797a2e75-2cb8-4dc9-bf5f-c3d269e0d88a
-- title:
--   $\gamma$-tilted secant convexity
-- statement:
--   Let $\gamma\in[0,1]$ and $f:\mathbb R^d\to\mathbb R\cup\{+\infty\}$. The function $f$ is **$\gamma$–tilted secant convex** if for all $y\neq z$ in $\operatorname{dom}(f)$ and $\lambda\in(0,1)$, the point $x:=\lambda y+(1-\lambda)z$ lies in $\operatorname{dom}(f)$ and the secant slopes
--
--   $$
--   s_-:=\frac{f(x)-f(z)}{\|x-z\|},\qquad s_+:=\frac{f(y)-f(x)}{\|y-x\|}
--   $$
--
--   satisfy $s_+\ge\psi_\gamma(s_-)$ whenever $\psi_\gamma(s_-)$ is defined. For $\gamma=1$ this is the increase of secant slopes, i.e. convexity.
--
--   **Formalization Note** The function is `E → EReal` and the predicate is used for proper functions; the slopes are real numbers computed from values at points of the domain.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 6, (6)–(7), p.14

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_psi
import Definitions.Def_TiltedCvx_TiltDefined

namespace TiltedCvx

/-- **γ–tilted secant convexity.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Definition 6, (6)–(7), p.14: `f` is γ–tilted secant convex if, for all `y ≠ z` in `dom(f)` and
`λ ∈ (0, 1)`, the point `x := λy + (1 − λ)z` lies in `dom(f)` and the secant slopes
`s₋ := (f(x) − f(z))/‖x − z‖`, `s₊ := (f(y) − f(x))/‖y − x‖` satisfy `s₊ ≥ ψγ(s₋)` whenever
`ψγ(s₋)` is defined.

**Formalization Note** The paper states it for `f : K → ℝ ∪ {+∞}`; here `f : E → EReal` and the
predicate is used for proper `f` (never `−∞`), with `dom f` the finite values. The slopes are
real: `toReal` is applied only to values at points of `dom f` (the first conjunct puts `x` in
`dom f`). -/
def TiltedSecant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (f : E → EReal) : Prop :=
  ∀ y ∈ effDom f, ∀ z ∈ effDom f, y ≠ z → ∀ l : ℝ, 0 < l → l < 1 →
    (l • y + (1 - l) • z ∈ effDom f) ∧
    (TiltDefined γ ((((f (l • y + (1 - l) • z)).toReal - (f z).toReal) /
        ‖l • y + (1 - l) • z - z‖ : ℝ) : EReal) →
      psi γ ((((f (l • y + (1 - l) • z)).toReal - (f z).toReal) /
        ‖l • y + (1 - l) • z - z‖ : ℝ) : EReal) ≤
      ((((f y).toReal - (f (l • y + (1 - l) • z)).toReal) /
        ‖y - (l • y + (1 - l) • z)‖ : ℝ) : EReal))

end TiltedCvx



-- Prove2me | Definitions.Def_TiltedCvx_Supplement_lscEnv
-- name    : TiltedCvx_Supplement_lscEnv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:23:13.61524+00:00
-- url     : https://prove2.me/theorems/86c063ba-4bc6-4fa8-9455-26512dd949a1
-- title:
--   Lower semicontinuous envelope $\operatorname{lsc}(f)$
-- statement:
--   Given a set $X\subseteq\mathbb R^d$ and $f:X\to\overline{\mathbb R}$, let $\tilde f$ equal $f$ on $X$ and $+\infty$ outside $X$. The **lower semicontinuous envelope** of $f$ is
--
--   $$
--   \operatorname{lsc}(f)(x):=\liminf_{y\to x}\tilde f(y)=\sup_{r>0}\ \inf\{\tilde f(y):\|y-x\|<r\},
--   $$
--
--   where the lower limit is nonpunctured and $\inf\emptyset=+\infty$. It is the largest lower semicontinuous function below $\tilde f$; in particular $\operatorname{lsc}(f|_{\operatorname{ri}(K)})$ is the envelope of $f$ restricted to the relative interior of $K$.
--
--   **Formalization Note** `lscEnv X f` uses only the values of $f$ on $X$ (the infimum runs over the points of $X$ in the open ball); `lscEnv Set.univ f` is $\operatorname{lsc}(f)$ for $f$ defined on all of $\mathbb R^d$. Infima and suprema are taken in `EReal`, where the empty infimum is $+\infty$.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §3, p.10

import Mathlib

namespace TiltedCvx.Supplement

/-- **Lower semicontinuous envelope.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §3,
p.10: given `f : X → ℝ̄`, let `f̃` equal `f` on `X` and `+∞` outside `X`; its lower semicontinuous
envelope is `lsc(f)(x) := liminf_{y→x} f̃(y) = sup_{r>0} inf{f̃(y) : ‖y − x‖ < r}`, where the lower
limit is nonpunctured and `inf ∅ = +∞`.

**Formalization Note** `lscEnv X f` is `lsc` of `f` regarded as a function on `X`: only the values
of `f` on `X` enter, and the infimum over the points of `X` in the open ball is the infimum of `f̃`
over the ball (`f̃ = +∞` elsewhere). In `EReal` the empty infimum is `⊤`, matching `inf ∅ = +∞`.
`lscEnv Set.univ f` is `lsc(f)` for `f : ℝ^d → ℝ̄`, and `lscEnv (ri K) f` is `lsc(f|ri(K))`. -/
noncomputable def lscEnv {E : Type*} [NormedAddCommGroup E] (X : Set E) (f : E → EReal) :
    E → EReal :=
  fun x => ⨆ (r : ℝ) (_ : 0 < r), ⨅ (y : E) (_ : y ∈ X ∧ ‖y - x‖ < r), f y

end TiltedCvx.Supplement



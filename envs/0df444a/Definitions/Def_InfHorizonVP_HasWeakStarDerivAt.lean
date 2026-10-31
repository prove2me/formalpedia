-- Prove2me | Definitions.Def_InfHorizonVP_HasWeakStarDerivAt
-- name    : InfHorizonVP_HasWeakStarDerivAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:57.191821+00:00
-- url     : https://prove2.me/theorems/75443e16-322b-4278-8f58-7b82c73ae87f
-- title:
--   Weak$^*$ derivative $\dot p(t)$
-- statement:
--   A function $p:\mathbb R_+\to E^*$ is **weakly$^*$ differentiable** at $t>0$ with weak$^*$ derivative $\dot p(t)=x^*$ if
--   $$
--   \lim_{h\to0}\Bigl\langle\frac{p(t+h)-p(t)}{h},x\Bigr\rangle=\langle x^*,x\rangle\qquad\text{for every }x\in E .
--   $$
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §4.1, p.11

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Weak\* derivative of a dual-valued function.**
Frankowska, Sagara, arXiv:1801.00400v3, §4.1, p.11: "A function p(·) is said to be weakly*
differentiable at t > 0 if there exists x* ∈ E* such that lim_{h→0} ⟨(p(t + h) − p(t))/h, x⟩ =
⟨x*, x⟩ for every x ∈ E. Then vector x* is called the weak* derivative of p at t and is denoted by
ṗ(t)".

`HasWeakStarDerivAt p y t` says `y` is the weak\* derivative of `p` at `t`.

**Formalization Note.** `E* = E →L[ℝ] ℝ`; the condition is that every scalar function
`s ↦ ⟨p(s), x⟩` has derivative `⟨y, x⟩` at `t` (two-sided). -/
def HasWeakStarDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ → E →L[ℝ] ℝ) (y : E →L[ℝ] ℝ) (t : ℝ) : Prop :=
  ∀ x : E, HasDerivAt (fun s => p s x) (y x) t

end InfHorizonVP



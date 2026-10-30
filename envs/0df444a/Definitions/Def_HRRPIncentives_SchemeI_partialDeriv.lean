-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_partialDeriv
-- name    : HRRPIncentives_SchemeI_partialDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:12:42.417376+00:00
-- url     : https://prove2.me/theorems/7454f7a5-f46e-4392-9ac7-7a15aba00b35
-- title:
--   Partial derivative within the action box
-- statement:
--   For $f:\mathbb R^2\to\mathbb R$, a set $B\subseteq\mathbb R^2$ and a direction $v$, this is the directional derivative of $f$ along $v$ taken within $B$:
--
--   $$\partial_v^B f(x)=Df|_B(x)\,v,$$
--
--   where $Df|_B(x)$ is the Fréchet derivative of $f$ at $x$ within $B$. With $B$ the action box, $v=(1,0)$ gives the partial derivative $f_r$ in the readmission rate and $v=(0,1)$ the partial derivative $f_c$ in the cost. Iterating gives the second partials used in the standing assumptions: $R_{rc}=\partial_c(\partial_r R)$ and $R_{cr}=\partial_r(\partial_c R)$.
--
--   **Formalization Note** The paper's $R$ is defined only on the closed box, so derivatives are taken within the box rather than on an open neighbourhood. On a convex set with nonempty interior such derivatives are uniquely determined at every point of the set.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, unnumbered, p. 10 ("where Rx denotes partial derivative with respect to variable x")

import Mathlib

namespace HRRPIncentives.SchemeI

/-- Directional (partial) derivative of `f : ℝ × ℝ → ℝ` along `v`, taken within the set `B`:
`partialDeriv f B v x = (D_B f)(x) v`, where `D_B f` is the Fréchet derivative of `f` within `B`.

With `B` the action box, `v = (1, 0)` gives the partial derivative in the readmission rate `r`
and `v = (0, 1)` the partial derivative in the cost `c`. Iterating gives second partials:
`partialDeriv (partialDeriv R B (1,0)) B (0,1)` is `R_rc = ∂_c(∂_r R)` and
`partialDeriv (partialDeriv R B (0,1)) B (1,0)` is `R_cr = ∂_r(∂_c R)`.

Source: Arifoğlu, Ren, Tezcan, Management Science 67(4) (2021), author-accepted manuscript,
unnumbered, p. 10 ("where Rx denotes partial derivative with respect to variable x").

**Formalization Note.** The paper's `R` lives on the closed box, so derivatives are taken within
the box (`fderivWithin`), not on an open neighbourhood. On a convex set with nonempty interior,
derivatives within the set are uniquely determined at every point of the set. -/
noncomputable def partialDeriv (f : ℝ × ℝ → ℝ) (B : Set (ℝ × ℝ)) (v : ℝ × ℝ) :
    ℝ × ℝ → ℝ :=
  fun x => fderivWithin ℝ f B x v

end HRRPIncentives.SchemeI



-- Prove2me | Definitions.Def_TiltedCvx_exTwo
-- name    : TiltedCvx_exTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:13.694702+00:00
-- url     : https://prove2.me/theorems/93b31429-d914-425b-b536-a16a513f29d7
-- title:
--   The function of Example 2
-- statement:
--   For $\gamma\in(0,1)$ and $c:=(1-\gamma)/\gamma$, the function $f:\mathbb R\to\overline{\mathbb R}$ of Example 2 is
--
--   $$
--   f(x):=\frac{x}{1+cx}\quad\text{for } x\in[0,1],\qquad f(x)=+\infty\ \text{ elsewhere}.
--   $$
--
--   It separates $\mathcal F^\gamma_{\mathrm{sec}}$ from $\mathcal F^\gamma_{\mathrm{mono}}$.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Example 2, p.29

import Mathlib

namespace TiltedCvx

/-- **The function of Example 2.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Example 2,
p.29: for `γ ∈ (0, 1)` and `c := (1 − γ)/γ`, `f(x) := x/(1 + cx)` for `x ∈ [0, 1]` and
`f(x) = +∞` elsewhere.

**Formalization Note** A function `ℝ → EReal`; for `γ ∈ (0, 1)` and `x ∈ [0, 1]` the denominator
is at least `1`. -/
noncomputable def exTwo (γ : ℝ) (x : ℝ) : EReal :=
  if 0 ≤ x ∧ x ≤ 1 then ((x / (1 + ((1 - γ) / γ) * x) : ℝ) : EReal) else ⊤

end TiltedCvx



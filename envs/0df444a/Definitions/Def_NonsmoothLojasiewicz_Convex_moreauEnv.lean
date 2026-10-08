-- Prove2me | Definitions.Def_NonsmoothLojasiewicz_Convex_moreauEnv
-- name    : NonsmoothLojasiewicz_Convex_moreauEnv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:50:18.741195+00:00
-- url     : https://prove2.me/theorems/2a2d6689-792e-47ea-9089-2f6b230fa362
-- title:
--   The epigraphical sum of $f$ and $\tfrac12\|\cdot\|^2$ (Moreau envelope)
-- statement:
--   For $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$, the **epigraphical sum** of $f$ and the square function $\tfrac12\|\cdot\|^2$ is
--   $$h(x)=\inf\Big\{f(u)+\tfrac12\|x-u\|^2:\ u\in\mathbb R^n\Big\},\qquad x\in\mathbb R^n,$$
--   a function with values in $[-\infty,+\infty]$. For a lower semicontinuous convex $f$ this is the Moreau envelope of $f$ with parameter $1$.
--
--   In the paper this regularization (denoted $h$ in Proposition 2.9 and $g$ in Section 3.2) is the device that turns a convex subanalytic $f$ into a continuous subanalytic function with the same critical points and the same infimum.
--
--   **Formalization Note** The infimum is taken in `EReal`. Since $f$ never takes the value $-\infty$, every term is a sum of an element of $\mathbb R\cup\{+\infty\}$ and a real number.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1210, Proposition 2.9 (definition of h); p. 1215, Section 3.2 (g)

import Mathlib

namespace NonsmoothLojasiewicz.Convex

/-- The epigraphical sum of `f` and the square function `½‖·‖²` (Proposition 2.9 of
Bolte–Daniilidis–Lewis, p. 1210; the Moreau envelope with parameter 1):
`h(x) = inf {f(u) + ½‖x − u‖² : u ∈ ℝⁿ}`, computed in `EReal = [−∞, +∞]`. For `f` never `−∞`
each term `f(u) + ½‖x − u‖²` is a sum of a value in `ℝ ∪ {+∞}` and a real number, so no
`⊥ + ⊤` case arises; the infimum may a priori be `−∞` or `+∞`. -/
noncomputable def moreauEnv {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (x : X) : EReal :=
  ⨅ u : X, f u + (((‖x - u‖ ^ 2) / 2 : ℝ) : EReal)

end NonsmoothLojasiewicz.Convex



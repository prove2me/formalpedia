-- Prove2me | Definitions.Def_ConstrSOSP_InteriorSospBox
-- name    : ConstrSOSP_InteriorSospBox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:06:31.544098+00:00
-- url     : https://prove2.me/theorems/c96d5c45-0a2e-4d21-932b-4518f27932ae
-- title:
--   Interior-Sosp on $[0,1]^2$ (Definition 4.10)
-- statement:
--   **Interior-Sosp** restricted as in Theorem 5.1: on the valid instances on $[0,1]^2$, find a rational $x^*$ in the open square $(0,1)^2$ with
--   $$
--   \|\nabla f(x^*)\|\le\epsilon_G,\qquad y^\top\nabla^2f(x^*)y\ge-\epsilon_H\ \ \text{for all unit }y .
--   $$
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.10, pp.21–22; Theorem 5.1, p.22

import Mathlib
import Definitions.Def_ConstrSOSP_boxA
import Definitions.Def_ConstrSOSP_boxB
import Definitions.Def_ConstrSOSP_IsSOSP
import Definitions.Def_ConstrSOSP_BoxProblem

namespace ConstrSOSP

/-- **Interior-Sosp on `[0, 1]²` with `L = L₁ = L₂ = 1`** (arXiv:2604.02285, 2 Nov 2026,
Definition 4.10, pp.21–22, restricted as in Theorem 5.1, p.22): "Goal: Find a point x* ∈ X that is
an (ϵG, ϵH)-SOSP; that is, x* ∈ int X and • ‖∇f(x*)‖ ≤ ϵG, (11a) • yᵀ∇²f(x*)y ≥ −ϵH, ∀ y ∈ ℝ^d
s.t. ‖y‖ = 1 (11b)".

The instances are those of `ValidBox K`; an answer is a rational point of the open square
`(0, 1)²` that is an `(ϵG, ϵH)`-SOSP (`IsSOSP`) of the machines' data. -/
def InteriorSospBox (K : ℕ) : TetrisHard.Rows.SearchProblem :=
  BoxProblem K (fun ϵG ϵH x g H => IsSOSP boxA boxB ϵG ϵH x g H)

end ConstrSOSP



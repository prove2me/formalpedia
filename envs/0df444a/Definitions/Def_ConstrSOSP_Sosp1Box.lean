-- Prove2me | Definitions.Def_ConstrSOSP_Sosp1Box
-- name    : ConstrSOSP_Sosp1Box
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:05:46.092134+00:00
-- url     : https://prove2.me/theorems/d7866728-44b5-4219-8600-e6784da35c0a
-- title:
--   Sosp1 on $[0,1]^2$ (Definition 4.6)
-- statement:
--   **Sosp1** restricted as in Theorem 5.1: on the valid instances on $[0,1]^2$, find a rational $x^*\in[0,1]^2$ that is an $(\epsilon_G,\epsilon_H)$-SOSP1 (proximal gradient with $L_1=1$, curvature on the null space of the active rows of $[I;-I]$).
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.6, pp.19–20; Theorem 5.1, p.22

import Mathlib
import Definitions.Def_ConstrSOSP_boxA
import Definitions.Def_ConstrSOSP_boxB
import Definitions.Def_ConstrSOSP_IsSOSP1
import Definitions.Def_ConstrSOSP_BoxProblem

namespace ConstrSOSP

/-- **Sosp1 on `[0, 1]²` with `L = L₁ = L₂ = 1`** (arXiv:2604.02285, 2 Nov 2026, Definition 4.6,
pp.19–20, restricted as in Theorem 5.1, p.22): "Goal: Find a point x* ∈ X such that:
• ‖g_π(x*)‖ ≤ ϵG, (7a) • yᵀ∇²f(x*)y ≥ −ϵH, ∀ y s.t. A′(x*)y = 0 and ‖y‖ = 1 (7b)".

The instances are those of `ValidBox K`; an answer is a rational point of `[0, 1]²` that is an
`(ϵG, ϵH)`-SOSP1 (`IsSOSP1`, proximal gradient with `L₁ = 1`, active rows of `A = [I; −I]`) of
the machines' data. -/
def Sosp1Box (K : ℕ) : TetrisHard.Rows.SearchProblem :=
  BoxProblem K (fun ϵG ϵH x g H => IsSOSP1 boxA boxB 1 ϵG ϵH x g H)

end ConstrSOSP



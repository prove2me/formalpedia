-- Prove2me | Definitions.Def_ConstrSOSP_Sosp2Box
-- name    : ConstrSOSP_Sosp2Box
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:06:16.62931+00:00
-- url     : https://prove2.me/theorems/df1450c8-9921-42d1-926c-f8b1357be55d
-- title:
--   Fixed-Dimensions-Sosp2 on $[0,1]^2$ (Definition 4.8)
-- statement:
--   **Fixed-Dimensions-Sosp2** with $d_0=2$, restricted as in Theorem 5.1: on the valid instances on $[0,1]^2$, find a rational $x^*\in[0,1]^2$ that is an $(\epsilon_G,\epsilon_H)$-SOSP2.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.8, pp.20–21; Theorem 5.1, p.22

import Mathlib
import Definitions.Def_ConstrSOSP_boxA
import Definitions.Def_ConstrSOSP_boxB
import Definitions.Def_ConstrSOSP_IsSOSP2
import Definitions.Def_ConstrSOSP_BoxProblem

namespace ConstrSOSP

/-- **Fixed-Dimensions-Sosp2 on `[0, 1]²` (d₀ = 2) with `L = L₁ = L₂ = 1`** (arXiv:2604.02285,
2 Nov 2026, Definition 4.8, pp.20–21, restricted as in Theorem 5.1, p.22): "Goal: Find a point
x* ∈ X such that, for every displacement s ∈ ℝ^{d₀} satisfying x* + s ∈ X and ‖s‖ ≤ 1,
∇f(x*)ᵀs ≥ −ϵG (first order), (9a) ∇f(x*)ᵀs ≤ 0 ⟹ sᵀ∇²f(x*)s ≥ −ϵH (second order). (9b)"

The instances are those of `ValidBox K`; an answer is a rational point of `[0, 1]²` that is an
`(ϵG, ϵH)`-SOSP2 (`IsSOSP2`) of the machines' data. -/
def Sosp2Box (K : ℕ) : TetrisHard.Rows.SearchProblem :=
  BoxProblem K (fun ϵG ϵH x g H => IsSOSP2 boxA boxB ϵG ϵH x g H)

end ConstrSOSP



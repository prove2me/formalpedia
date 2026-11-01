-- Prove2me | Definitions.Def_LocalDOvS_SUS_susState__311ba0
-- name    : LocalDOvS_SUS_susState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:28:44.636224+00:00
-- url     : https://prove2.me/theorems/311ba053-4430-4c6b-8a7f-0efddc2a3b51
-- title:
--   Iteration state along a run
-- statement:
--   The state $(S_k,d_k,x_{L,k},x_{U,k})$ of the iteration in progress of the corrected SUS algorithm after history $h$. Along a run on tape $\omega$, evaluating it at the history at time $t$ gives the iteration in progress at time $t$, or the final state.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, p.15; p.ec14

import Mathlib
import Definitions.Def_LocalDOvS_SUS_susGo
import Definitions.Def_LocalDOvS_SUS_initState

open scoped NNReal

namespace LocalDOvS.SUS

/-- The state of the iteration in progress of the corrected shrinking uniform sampling
algorithm after history `h` (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, `S_k`, `d_k`, `x_{L,k}`,
`x_{U,k}` of p.ec14): along a run, `susState … (histAt (sus …) ω t)` is the state `(S_k, d_k,
x_{L,k}, x_{U,k})` of the iteration `k` in progress at time `t`, or the final state. -/
noncomputable def susState (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ)
    (pick : SUSState → (ℕ → ℕ → ℝ) → ℕ × ℕ) (tie : SUSState → (ℕ → ℕ → ℝ) → Bool)
    (h : List (ℕ × ℝ)) : SUSState :=
  (susGo N σ ε δ pick tie h N (initState N)).1

end LocalDOvS.SUS



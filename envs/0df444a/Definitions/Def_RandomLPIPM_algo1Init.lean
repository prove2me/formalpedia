-- Prove2me | Definitions.Def_RandomLPIPM_algo1Init
-- name    : RandomLPIPM_algo1Init
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:54.558901+00:00
-- url     : https://prove2.me/theorems/ce6faef6-ff8f-422e-9851-660577549ebc
-- title:
--   Initial state of Algorithm 1
-- statement:
--   Algorithm 1 starts (line 2) from $(x,\mu)=(x^0,\mu_{\mathrm{start}})$, with inner variable $u=0$, control at the outer loop test, and no linear system solved yet.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Algorithm 1, line 2, p.80

import Mathlib
import Definitions.Def_RandomLPIPM_Algo1State

namespace RandomLPIPM

/-- **Initial state of Algorithm 1** (line 2: `(x, μ) ← (x⁰, μ_start)`). Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Algorithm 1,
p.80. The inner variable starts at `0`, no line-7 evaluation has been made. -/
def algo1Init {n : ℕ} (x0 : Fin n → ℝ) (μstart : ℝ) : Algo1State n :=
  ⟨x0, μstart, 0, Algo1Phase.outer, 0⟩

end RandomLPIPM



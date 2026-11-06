-- Prove2me | Definitions.Def_RandomLPIPM_Algo1Phase
-- name    : RandomLPIPM_Algo1Phase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:46.245639+00:00
-- url     : https://prove2.me/theorems/8fc5bca9-ceac-4327-9208-8657538c063f
-- title:
--   Control position of Algorithm 1
-- statement:
--   The control position of Algorithm 1: **outer** (about to test the outer loop condition $\mu>\mu_{\mathrm{end}}$, line 3), **inner** (inside the inner loop, lines 7–8), **done** (returned, line 10).
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Algorithm 1, p.80

import Mathlib

namespace RandomLPIPM

/-- **Control position of Algorithm 1.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Algorithm 1, p.80. `outer`: about to test the
outer loop condition (line 3); `inner`: inside the inner loop (lines 7–8); `done`: returned
(line 10). -/
inductive Algo1Phase
  | outer
  | inner
  | done
  deriving DecidableEq

end RandomLPIPM



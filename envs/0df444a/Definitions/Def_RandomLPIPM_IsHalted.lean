-- Prove2me | Definitions.Def_RandomLPIPM_IsHalted
-- name    : RandomLPIPM_IsHalted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:10.883341+00:00
-- url     : https://prove2.me/theorems/b8225207-92f2-44ef-b5e0-d1016969ec5b
-- title:
--   Algorithm 1 has returned
-- statement:
--   A state of Algorithm 1 is **halted** when control has reached the return statement (line 10); its output is then $(\hat x,\hat\mu)=(x,\mu)$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Algorithm 1, line 10, p.80

import Mathlib
import Definitions.Def_RandomLPIPM_Algo1State

namespace RandomLPIPM

/-- **Algorithm 1 has returned** (line 10). Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Algorithm 1, p.80. -/
def IsHalted {n : ℕ} (s : Algo1State n) : Prop :=
  s.phase = Algo1Phase.done

end RandomLPIPM



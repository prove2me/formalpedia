-- Prove2me | Definitions.Def_RandomLPIPM_traceH
-- name    : RandomLPIPM_traceH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:01.470011+00:00
-- url     : https://prove2.me/theorems/2ecbce82-c4d2-4dad-92bd-b56ceac544f1
-- title:
--   $h_T(t)=\operatorname{Tr}H_T(t)$
-- statement:
--   $$h_T(t)=\operatorname{Tr}H_T(t)=\sum_i\frac{\lambda_it}{(1+\lambda_it)^2}.$$
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (6) p.14; (18)–(19) p.23

import Mathlib
import Definitions.Def_RandomLPIPM_matH

open Matrix

namespace RandomLPIPM

/-- **`h_T(t) = Tr H_T(t)`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (6) p.14 and (18) p.23. -/
noncomputable def traceH {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) : ℝ :=
  trace (matH T t)

end RandomLPIPM



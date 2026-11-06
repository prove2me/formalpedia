-- Prove2me | Definitions.Def_RandomLPIPM_traceF
-- name    : RandomLPIPM_traceF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:06.007546+00:00
-- url     : https://prove2.me/theorems/f51bb1e8-e3d2-4ff9-aadf-abf7efa5edd5
-- title:
--   Resolvent trace $f_T(t)=\operatorname{Tr}F_T(t)$
-- statement:
--   $$f_T(t)=\operatorname{Tr}F_T(t)=\sum_{i}\frac{\lambda_it}{1+\lambda_it}.$$
--   It increases from $0$ to $\operatorname{rank}(T)$ as $t$ goes from $0$ to $\infty$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (6) p.14; (18)–(19) p.23

import Mathlib
import Definitions.Def_RandomLPIPM_matF

open Matrix

namespace RandomLPIPM

/-- **Resolvent trace `f_T(t) = Tr F_T(t)`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (6) p.14 and (18) p.23. -/
noncomputable def traceF {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) : ℝ :=
  trace (matF T t)

end RandomLPIPM



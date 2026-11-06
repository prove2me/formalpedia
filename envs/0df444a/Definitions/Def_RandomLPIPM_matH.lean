-- Prove2me | Definitions.Def_RandomLPIPM_matH
-- name    : RandomLPIPM_matH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:15.474783+00:00
-- url     : https://prove2.me/theorems/a95160f2-43ad-4d29-ab66-3ae6013e5018
-- title:
--   $H_T(t)=F_T(t)(I-F_T(t))$
-- statement:
--   For a positive semidefinite $T$ and $t>0$,
--   $$H_T(t)=F_T(t)\big(I-F_T(t)\big),$$
--   whose eigenvalues are $\lambda_it/(1+\lambda_it)^2$; it measures the sensitivity of $F_T$ to the scale $t$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (5) p.14; (17) p.23

import Mathlib
import Definitions.Def_RandomLPIPM_matF

open Matrix

namespace RandomLPIPM

/-- **`H_T(t) = F_T(t)(I − F_T(t))`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (5) p.14 and (17) p.23. -/
noncomputable def matH {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  matF T t * (1 - matF T t)

end RandomLPIPM



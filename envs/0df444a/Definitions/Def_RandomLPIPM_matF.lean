-- Prove2me | Definitions.Def_RandomLPIPM_matF
-- name    : RandomLPIPM_matF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:13.807397+00:00
-- url     : https://prove2.me/theorems/1cb37faa-e0de-4f6a-8c97-a1c5a8ff8809
-- title:
--   Resolvent at scale $t$: $F_T(t)=tT(tT+I)^{-1}$
-- statement:
--   For a positive semidefinite $T\in\mathbb R^{N\times N}$ and $t>0$,
--   $$F_T(t)=tT\,(tT+I)^{-1}=I-(I+tT)^{-1}.$$
--   Its eigenvalues are $\lambda_it/(1+\lambda_it)$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (5) p.14; (17) p.23

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **Resolvent at scale `t`: `F_T(t) = tT(tT + I)⁻¹`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (5) p.14 and (17) p.23. -/
noncomputable def matF {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (t • T) * (t • T + 1)⁻¹

end RandomLPIPM



-- Prove2me | Definitions.Def_RandomLPIPM_Algo1State
-- name    : RandomLPIPM_Algo1State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:43.574195+00:00
-- url     : https://prove2.me/theorems/a272ecea-2b6e-4769-a76c-5372b5261afc
-- title:
--   State of Algorithm 1
-- statement:
--   A state of Algorithm 1 consists of
--   1. the iterate $x\in\mathbb R^n$,
--   2. the barrier parameter $\mu$,
--   3. the inner variable $u\in\mathbb R^n$,
--   4. the control position (outer / inner / done),
--   5. the number of evaluations of the test of line 7 performed so far.
--
--   Each evaluation of line 7 computes $P_x\nabla\Phi_{x,\mu}(u)$, i.e. one linear system solve in $AX^2A^\top$; the counter is the iteration count of Theorems 1.1 and 9.3.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Algorithm 1, p.80

import Mathlib
import Definitions.Def_RandomLPIPM_Algo1Phase

namespace RandomLPIPM

/-- **State of Algorithm 1.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Algorithm 1, p.80: the iterate `x`, the barrier parameter
`μ`, the inner variable `u`, the control position `phase`, and `solves`, the number of evaluations
of line 7 performed so far (each evaluation applies `P_x` once, i.e. one linear system solve in
`AX²Aᵀ`). -/
structure Algo1State (n : ℕ) where
  /-- the current iterate `x` -/
  x : Fin n → ℝ
  /-- the current barrier parameter `μ` -/
  μ : ℝ
  /-- the inner variable `u` -/
  u : Fin n → ℝ
  /-- the control position -/
  phase : Algo1Phase
  /-- number of evaluations of line 7 so far -/
  solves : ℕ

end RandomLPIPM



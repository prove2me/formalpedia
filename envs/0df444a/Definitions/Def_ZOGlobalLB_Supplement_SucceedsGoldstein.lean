-- Prove2me | Definitions.Def_ZOGlobalLB_Supplement_SucceedsGoldstein
-- name    : ZOGlobalLB_Supplement_SucceedsGoldstein
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:49:07.326522+00:00
-- url     : https://prove2.me/theorems/d20d0d5c-20b7-4665-aa8d-20ea84ad7b9a
-- title:
--   Success at Goldstein $(\delta,\varepsilon)$-stationarity
-- statement:
--   A randomized zeroth-order run succeeds at Goldstein $(\delta,\varepsilon)$-stationarity if it stops after finitely many exact scalar queries and outputs a point $\widehat x$ satisfying
--
--   $$
--   g_\delta(\widehat x)\le\varepsilon.
--   $$
--
--   A run that never stops does not succeed. The algorithm retains arbitrary adaptive queries, label reuse, randomized stopping, and arbitrary outputs.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Eq. (6) and Theorem 2.2, pp.4-5

import Mathlib
import Definitions.Def_ZOGlobalLB_ZOAlg
import Definitions.Def_ZOGlobalLB_Supplement_goldsteinGauge

namespace ZOGlobalLB

namespace Supplement

/-- A run succeeds at Goldstein `(δ, ε)`-stationarity when it stops and outputs `x` with
`g_δ(x) ≤ ε`, as in Xia--Yuan, arXiv:2610.19652, display (6) and Theorem 2.2, pp.4--5.
A run that never stops does not succeed. -/
def SucceedsGoldstein {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (δ ε : ℝ)
    (A : ZOAlg d n Ω) (F : Fin n → E d → ℝ) (ω : Ω) : Prop :=
  ∃ t x, A.outputAt F ω t = some x ∧ goldsteinGauge (popMean F) δ x ≤ ε

end Supplement

end ZOGlobalLB



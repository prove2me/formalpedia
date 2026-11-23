-- Prove2me | Definitions.Def_StochSQP_Vanishing_Supplement_TrueTrial
-- name    : StochSQP_Vanishing_Supplement_TrueTrial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:15:35.210189+00:00
-- url     : https://prove2.me/theorems/cceadccc-4ca1-4631-a7eb-f273be6b4e1b
-- title:
--   True-gradient directions and extended trial merit
-- statement:
--   At each iterate recompute the solution of (9) using the true gradient:
--   $$H_ku_k^{\mathrm{true}}+J_k^Ty_k^{\mathrm{true}}=-(\nabla f(x_k)+H_kv_k),\qquad J_ku_k^{\mathrm{true}}=0,$$
--   and set $d_k^{\mathrm{true}}=v_k+u_k^{\mathrm{true}}$. With $b_k=\nabla f(x_k)^Td_k^{\mathrm{true}}+(u_k^{\mathrm{true}})^TH_ku_k^{\mathrm{true}}$, define
--   $$T_k^{\mathrm{trial,true}}=\begin{cases}+\infty,&b_k\le0,\\ (1-\sigma)(\|c_k\|_2-\|c_k+J_kd_k^{\mathrm{true}}\|_2)/b_k,&b_k>0.\end{cases}$$
--   Assumption 3 makes the system consistent and its tangential component unique, even when the multiplier is not unique. The definition chooses any solution and has a zero fallback only outside that consistent domain. The value is an extended nonnegative real; on valid runs the numerator is nonnegative. Division is confined to the strictly positive denominator branch. These quantities are computed from the problem and run, not arbitrary extra directions.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, pp. 6–7, 12, 14, (9), (11), true trial

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

namespace StochSQP.Vanishing.Supplement

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace ENNReal

variable {n m : ℕ}

/-- System (9) with the true gradient. The tangential component is unique under Assumption 3;
any multiplier solution represents the same trial value. -/
def TrueSystem (P : Problem n m) (R : Run n m) (k : ℕ) (s : E n × E m) : Prop :=
  R.H k s.1 + P.Jt (R.x k) s.2 = -(P.grad (R.x k) + R.H k (R.v k)) ∧
  P.J (R.x k) s.1 = 0

noncomputable def trueSolution (P : Problem n m) (R : Run n m) (k : ℕ) : E n × E m := by
  classical
  exact if h : ∃ s, TrueSystem P R k s then Classical.choose h else (0, 0)

noncomputable def trueU (P : Problem n m) (R : Run n m) (k : ℕ) : E n :=
  (trueSolution P R k).1

noncomputable def trueD (P : Problem n m) (R : Run n m) (k : ℕ) : E n :=
  R.v k + trueU P R k

/-- Honest infinity in (11); no division is evaluated in its nonpositive branch. -/
noncomputable def trueTrial (P : Problem n m) (A : Params) (R : Run n m) (k : ℕ) : ℝ≥0∞ :=
  let b := ⟪P.grad (R.x k), trueD P R k⟫_ℝ + ⟪trueU P R k, R.H k (trueU P R k)⟫_ℝ
  if b ≤ 0 then ⊤ else
    ENNReal.ofReal ((1 - A.σ) *
      (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (trueD P R k)‖) / b)

end StochSQP.Vanishing.Supplement



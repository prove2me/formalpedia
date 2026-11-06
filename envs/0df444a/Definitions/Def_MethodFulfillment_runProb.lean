-- Prove2me | Definitions.Def_MethodFulfillment_runProb
-- name    : MethodFulfillment_runProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:40.947349+00:00
-- url     : https://prove2.me/theorems/3531210b-2a66-47bb-b109-be1894dcb5d2
-- title:
--   Probability of a run of Algorithm 1
-- statement:
--   Given an LP solution $y$ and a method-acceptance strategy $\sigma$, the probability of a run $r$ is
--   $$\Pr(r)=\prod_{t}\Pr(\text{arrival}_t)\cdot\Pr(\text{draw}_t\mid\text{arrival}_t)\cdot\sigma_t(A_t\mid h_t,\text{arrival}_t,\text{draw}_t),$$
--   the product of the arrival probability, the probability of the drawn method (step 1) and the probability the strategy gives to the available set (step 2). For a non-anticipating strategy this is the law of the online process built period by period.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Algorithm 1, p.13

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Run
import Definitions.Def_MethodFulfillment_arrProb
import Definitions.Def_MethodFulfillment_drawProb

namespace MethodFulfillment

/-- The probability of a run of Algorithm 1 (Amil, Makhdoumi & Wei, manuscript, PDF sha256
197c13b9…, Algorithm 1, p.13) with LP solution `y` and method-acceptance strategy `σ`: the
product over periods of the arrival probability, the probability of the drawn method (step 1),
and the probability the strategy assigns to the available set (step 2).

**Formalization Note.** For a non-anticipating strategy (`IsPolicy`) this is the law of the
process built period by period: the factor at `t` depends on the run only through periods `≤ t`
and is a conditional probability given the past. Arrivals are independent across periods, and
the draw at `t` is independent of the past. -/
noncomputable def runProb {I K Q : Type} [DecidableEq I] [DecidableEq K] [Fintype Q] {T : ℕ}
    (P : Instance I K Q T) (y : Q → Finset (I × K) → ℝ)
    (σ : Fin T → Run I K Q T → Option Q → Finset (I × K) → Finset (I × K) → ℝ)
    (r : Run I K Q T) : ℝ :=
  ∏ t, arrProb P t (r t).1 * drawProb P y (r t).1 (r t).2.1 *
    σ t r (r t).1 (r t).2.1 (r t).2.2

end MethodFulfillment



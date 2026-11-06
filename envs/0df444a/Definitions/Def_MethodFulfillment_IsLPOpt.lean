-- Prove2me | Definitions.Def_MethodFulfillment_IsLPOpt
-- name    : MethodFulfillment_IsLPOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:42.641204+00:00
-- url     : https://prove2.me/theorems/084bb33d-d824-4f0f-9085-5f872871e985
-- title:
--   Optimal solution of the expected LP, value $\mathrm{OPT}^E$
-- statement:
--   A vector $y$ is an **optimal solution of the expected LP** (6)–(9) when it is feasible and
--   $$\sum_{q}\sum_{m\in M(q)}c_m y_m\le\sum_{q}\sum_{m\in M(q)}c_m x_m\quad\text{for every feasible }x .$$
--   Its objective value is $\mathrm{OPT}^E$. The offline process of Algorithm 1 solves this LP and uses $y$ to guide the online decisions.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), (6), p.11

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_LPFeasible
import Definitions.Def_MethodFulfillment_lpObj

namespace MethodFulfillment

/-- `y` is an optimal solution of the expected LP (6)–(9) (Amil, Makhdoumi & Wei, manuscript, PDF
sha256 197c13b9…, (6), p.11): it is feasible and its objective is at most that of every feasible
point. Its value is `OPT^E`. -/
def IsLPOpt {I K Q : Type} [DecidableEq I] [DecidableEq K] [Fintype Q] {T : ℕ}
    (P : Instance I K Q T) (y : Q → Finset (I × K) → ℝ) : Prop :=
  LPFeasible P y ∧ ∀ x, LPFeasible P x → lpObj P y ≤ lpObj P x

end MethodFulfillment



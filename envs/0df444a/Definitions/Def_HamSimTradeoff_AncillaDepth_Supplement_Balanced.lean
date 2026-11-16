-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Balanced
-- name    : HamSimTradeoff_AncillaDepth_Supplement_Balanced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:50:24.086511+00:00
-- url     : https://prove2.me/theorems/61fdc4c4-00dc-4dc1-87a6-7ba8932270a1
-- title:
--   The balanced LCU instance hypotheses
-- statement:
--   For $\eta\in[0,1)$, a balanced instance comprises $L,N\ge1$ and a fixed LCU circuit with
--   $$N\ge T(L+1)^2,\qquad\|B(P)-L^{-1}\sum_jP_j\|\le\eta/L\quad\text{for every }P\in U(N)^L.$$
--   This predicate abbreviates only Theorem 1.5's hypotheses. It supplies no positive-query premise, resource bound or algorithmic conclusion.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), pp. 8–9, Theorem 1.5

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_LCU
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

def BalancedInstance (eta : ℝ) (L N : ℕ) (B : LCUCircuit L) : Prop :=
  1 ≤ L ∧ 1 ≤ N ∧ B.T*(L+1)^2 ≤ N ∧
    LCUApprox B N (fun _ => 1/(L:ℝ)) (eta/(L:ℝ))

end
end HamSimTradeoff.AncillaDepth.Supplement



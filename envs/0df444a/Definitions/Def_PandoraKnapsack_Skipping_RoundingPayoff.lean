-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_RoundingPayoff
-- name    : PandoraKnapsack_Skipping_RoundingPayoff
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:12:38.355975+00:00
-- url     : https://prove2.me/theorems/fc152f6d-a563-4af3-a758-48113221c608
-- title:
--   Skipping list and expected net utility of Algorithm 1 rounding
-- statement:
--   The policy associated to an assignment scans the items in order of assigned start time. For a triple with time $t$, its threshold is $T-t$. The assignment-averaged payoff is
--   $$
--   U_I(x)=\sum_a \left(\prod_i p_i(a_i)\right)V_I(\sigma_a),
--   $$
--   where $p_i$ is Algorithm 1's categorical law and $V_I$ already averages over all realized sizes.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora's Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Algorithm 1 and the proof of Theorem 5.1.

import Definitions.Def_PandoraKnapsack_Skipping_Algorithm1
import Definitions.Def_PandoraKnapsack_Skipping_Policies

namespace PandoraKnapsack.Skipping
variable {n m T : ℕ}

/-- The list output from an assignment in Algorithm 1. At an assigned start time
`t`, attempt the item exactly when at least `T - t` units remain. -/
def alg1Policy (a : Assignment n m T) : SkipList n m :=
  (scanOrder a).map fun e => (e.1, e.2.1, T - e.2.2)

/-- Expected net utility over the independent categorical assignments in Algorithm 1.
The inner `skipValue` averages over the sizes revealed when executing that list. -/
noncomputable def alg1Utility (I : Instance n m T) (x : LPArray n m) : ℝ :=
  ∑ a : Assignment n m T, (∏ i, assignWeight x i (a i)) * skipValue I (alg1Policy a)

end PandoraKnapsack.Skipping



-- Prove2me | Definitions.Def_LiquidWelfareFPA_dcomp
-- name    : LiquidWelfareFPA_dcomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:18.378859+00:00
-- url     : https://prove2.me/theorems/231f16c1-c183-46ee-9958-b681cc996d77
-- title:
--   Highest competing bid $d_{it}=\max_{j\ne i}b_{jt}$
-- statement:
--   In an outcome, the **highest competing bid** faced by player $i$ in round $t$ is
--
--   $$d_{it}=\max_{j\ne i}b_{jt}.$$
--
--   It is computed from the bids the other players actually submitted, and it is the threshold against which player $i$'s counterfactual bids are evaluated in the benchmark.
--
--   **Formalization Note** When $n=1$ there is no competitor and $d_{it}=0$; bids are nonnegative, so this is the natural value.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, §3, p.6

import Mathlib
import Definitions.Def_LiquidWelfareFPA_Outcome

namespace LiquidWelfareFPA

/-- **Highest competing bid `d_it = max_{j≠i} b_jt`.**
Fikioris & Tardos, arXiv:2210.07502v4, §3, p.6: "with d_it the highest competing bid faced by
player i, i.e., d_it = max_{j≠i} b_jt".

**Formalization Note** The maximum is taken in `ℝ≥0` (bids are nonnegative, so `toNNReal` does
not change them) and coerced back to `ℝ`. When `n = 1` there is no competitor and `d_it = 0`. -/
noncomputable def dcomp {n T : ℕ} (o : Outcome n T) (i : Fin n) (t : Fin T) : ℝ :=
  (((Finset.univ.erase i).sup fun j => (o.bid j t).toNNReal : NNReal) : ℝ)

end LiquidWelfareFPA



-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_lpMax
-- name    : KallMayerSLP_Bonferroni_lpMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:40.767519+00:00
-- url     : https://prove2.me/theorems/152630dd-7553-49a8-8b05-09644b53e196
-- title:
--   Optimal value $V_{\max}$ of the maximization counterpart of (3.14)
-- statement:
--   The optimal value
--   $$
--   V_{\max}=\max\{v_1+\dots+v_r : v \text{ feasible for (3.14)}\},
--   $$
--   obtained from (3.14) by changing the direction of optimization to maximization.
--
--   **Formalization Note** The maximum is the real supremum of the objective values. That supremum returns $0$ on an empty or unbounded set, but for data arising from events the feasible set is nonempty and bounded and the maximum is attained.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, p.288 (PDF 297)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_lpObjectiveValues

namespace KallMayerSLP.Bonferroni

/-- The optimal value `V_max` of the linear program obtained from (3.14) by changing the direction
of optimization to maximization.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, p.288 (PDF 297).

**Formalization Note.** The book's `max` is a real `sSup`, which is `0` on an empty or unbounded
above set. For data arising from events the feasible set is nonempty and bounded
(`lp_feasible_nonempty_bounded`) and the maximum is attained (`eq_3_15_lp_closed_forms`), so the
junk value never occurs in this mission. -/
noncomputable def lpMax (r : ℕ) (S₁ S₂ : ℝ) : ℝ :=
  sSup (lpObjectiveValues r S₁ S₂)

end KallMayerSLP.Bonferroni



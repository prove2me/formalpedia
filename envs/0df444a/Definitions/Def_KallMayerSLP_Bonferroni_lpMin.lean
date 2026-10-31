-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_lpMin
-- name    : KallMayerSLP_Bonferroni_lpMin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:27.51386+00:00
-- url     : https://prove2.me/theorems/add45a39-cae8-4aab-ab61-2e367573e48f
-- title:
--   Optimal value $V_{\min}$ of the linear program (3.14)
-- statement:
--   The optimal value
--   $$
--   V_{\min}=\min\{v_1+\dots+v_r : v \text{ feasible for (3.14)}\}.
--   $$
--
--   **Formalization Note** The minimum is the real infimum of the objective values. That infimum returns $0$ on an empty set, but for data arising from events the feasible set is nonempty and bounded and the minimum is attained.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.14), p.288 (PDF 297)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_lpObjectiveValues

namespace KallMayerSLP.Bonferroni

/-- The optimal value `V_min` of the linear program (3.14).

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.14), p.288 (PDF 297).

**Formalization Note.** The book's `min` is a real `sInf`, which is `0` on an empty or unbounded
below set. For data arising from events the feasible set is nonempty and bounded
(`lp_feasible_nonempty_bounded`) and the minimum is attained (`eq_3_15_lp_closed_forms`), so the
junk value never occurs in this mission. -/
noncomputable def lpMin (r : ℕ) (S₁ S₂ : ℝ) : ℝ :=
  sInf (lpObjectiveValues r S₁ S₂)

end KallMayerSLP.Bonferroni



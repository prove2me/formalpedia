-- Prove2me | Definitions.Def_MeanBudgetXC_budgetZeroSection
-- name    : MeanBudgetXC_budgetZeroSection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:03.966373+00:00
-- url     : https://prove2.me/theorems/7185e473-f36a-46ab-84c9-b4d15c871bc5
-- title:
--   The budgeted zero section $Z_{Q,B}$
-- statement:
--   The **budgeted zero section** is
--   $$Z_{Q,B}=Z_Q\cap\Big\{\sum_{e\in E}x_e\le B/2\Big\}.$$
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.1, p.18, display (12)

import Mathlib
import Definitions.Def_MeanBudgetXC_zeroSection

namespace MeanBudgetXC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **budgeted zero section** `Z_{Q,B} = Z_Q ∩ {∑_{e ∈ E} x_e ≤ B/2}` of (12)
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.1, p.18). -/
def budgetZeroSection (Q : SimpleGraph V) [DecidableRel Q.Adj] (d : ℕ) (B : ℝ) :
    Set (Q.edgeSet → ℝ) :=
  zeroSection Q d ∩ {x | ∑ e, x e ≤ B / 2}

end MeanBudgetXC



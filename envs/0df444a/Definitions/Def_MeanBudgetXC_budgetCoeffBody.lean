-- Prove2me | Definitions.Def_MeanBudgetXC_budgetCoeffBody
-- name    : MeanBudgetXC_budgetCoeffBody
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:26.398478+00:00
-- url     : https://prove2.me/theorems/d4d3af79-259a-4769-80d9-c62acf17a00e
-- title:
--   The budgeted coefficient body $C_{Q,B}$
-- statement:
--   For $B>0$, the **budgeted coefficient body** is
--   $$C_{Q,B}=\ \downarrow\mathrm{conv}\big(C_Q\cup\{(2/B)\mathbf 1_E\}\big).$$
--   It is the antiblocker of the budgeted zero section $Z_{Q,B}$.
--
--   **Formalization Note** The expression is used only for $B>0$. At $B=0$ Lean's division gives the point $0$, and no statement uses that case.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.1, p.18, display (14)

import Mathlib
import Definitions.Def_MeanBudgetXC_coeffBody

namespace MeanBudgetXC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **budgeted coefficient body** `C_{Q,B} = ↓conv(C_Q ∪ {(2/B) 1_E})` of (14)
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.1, p.18), used for `B > 0`. -/
def budgetCoeffBody (Q : SimpleGraph V) [DecidableRel Q.Adj] (d : ℕ) (B : ℝ) :
    Set (Q.edgeSet → ℝ) :=
  downClosure (convexHull ℝ (coeffBody Q d ∪ {fun _ => 2 / B}))

end MeanBudgetXC



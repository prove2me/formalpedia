-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_binaryQueryLang
-- name    : MeanBudgetXC_Supplement_binaryQueryLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:12:06.747954+00:00
-- url     : https://prove2.me/theorems/db7a9793-9284-4b73-98a0-152fa5cf2e6d
-- title:
--   Codes of binary-cap queries with a prescribed value
-- statement:
--   Given $\theta$, constants $D,E$, a target body $P_N$ for each size $N$ and a property $\mathcal P$ of real numbers, this is the set of binary strings that encode (by the full-cap encoding) an instance $(N,u_F)$ with $F$ in the sparse-support family and $\mathcal P(V_{P_N}(u_F))$. With $\mathcal P(v)\equiv v=1$ it is the YES side of the gap problem of Theorem 7.2, with $\mathcal P(v)\equiv v\ge1+\delta$ its NO side.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 7.2, p.36

import Mathlib
import Definitions.Def_MeanBudgetXC_Supplement_capValue
import Definitions.Def_MeanBudgetXC_Supplement_binaryCap
import Definitions.Def_MeanBudgetXC_Supplement_graphCode
import Definitions.Def_MeanBudgetXC_Supplement_IsSparseFamily

namespace MeanBudgetXC.Supplement

/-- The codes of the **binary-cap queries** of the sparse family whose value satisfies `P`
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 7.2, p.36): the strings `graphCode N F` for graphs `F` on `[N]` in
the family `IsSparseFamily θ D E` with `P (V_{body N}(u_F))`, where `body N ⊆ ℝ^{Pair (Fin N)}` is
the target body at size `N`. With `P v := v = 1` this is the YES side of the gap problem of
Theorem 7.2, with `P v := 1 + δ ≤ v` its NO side. -/
def binaryQueryLang (θ : ℝ) (D E : ℕ) (body : (N : ℕ) → Set (Pair (Fin N) → ℝ)) (P : ℝ → Prop) :
    Set (List Bool) :=
  {w | ∃ (N : ℕ) (F : SimpleGraph (Fin N)) (_ : DecidableRel F.Adj),
    IsSparseFamily θ D E F ∧ w = graphCode N F ∧ P (capValue (body N) (binaryCap F))}

end MeanBudgetXC.Supplement



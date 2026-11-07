-- Prove2me | Definitions.Def_MeanBudgetXC_coeffBody
-- name    : MeanBudgetXC_coeffBody
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:13.919551+00:00
-- url     : https://prove2.me/theorems/6d7b004f-3f09-4e02-b670-d49ea451f2cd
-- title:
--   The coefficient body $C_Q$
-- statement:
--   The **coefficient body** of a graph $Q$ at context size $d$ is
--   $$C_Q=\ \downarrow\mathrm{conv}\{c_S:|S|=d\}\subseteq\mathbb{R}^E.$$
--   It is the antiblocker of the zero section $Z_Q$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.1, p.18

import Mathlib
import Definitions.Def_MeanBudgetXC_downClosure
import Definitions.Def_MeanBudgetXC_coverVec

namespace MeanBudgetXC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **coefficient body** `C_Q = ↓conv{c_S : |S| = d}` (Chao–Gao–Qi–Wang, *A Sharp
Mean-Budget Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256
882d9c71…9e76, Section 4.1, p.18, before (14)). -/
def coeffBody (Q : SimpleGraph V) [DecidableRel Q.Adj] (d : ℕ) : Set (Q.edgeSet → ℝ) :=
  downClosure (convexHull ℝ {y | ∃ S : Finset V, S.card = d ∧ y = coverVec Q S})

end MeanBudgetXC



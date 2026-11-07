-- Prove2me | Definitions.Def_MeanBudgetXC_OPair
-- name    : MeanBudgetXC_OPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:29.777512+00:00
-- url     : https://prove2.me/theorems/66397937-798c-4c7b-812b-4011c6e0bc52
-- title:
--   Ordered pairs of distinct vertices
-- statement:
--   The **ordered pairs** $(i,j)$ of distinct vertices index the variable families $z$ and $v$ of the quadratic formulation: the paper gives them one coordinate per ordered pair $i\ne j$, against one per unordered pair for $q$ and $w$.
--
--   The module also records the map to the underlying unordered pair $\{i,j\}$ and the reversal $(i,j)\mapsto(j,i)$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.5, p.15

import Mathlib
import Definitions.Def_MeanBudgetXC_Pair

namespace MeanBudgetXC

variable {V : Type*} [DecidableEq V]

/-- Ordered pairs `(i, j)` of distinct vertices, the index set of the variable families `z` and
`v` of the quadratic formulation (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local
Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76, Section 3.5, p.15: "zij
and vij have one coordinate per ordered pair (i ≠ j)"). -/
abbrev OPair (V : Type*) : Type _ := {ij : V × V // ij.1 ≠ ij.2}

/-- The unordered pair `{i, j}` underlying an ordered pair `(i, j)`. -/
def OPair.toPair (o : OPair V) : Pair V := ⟨s(o.1.1, o.1.2), Sym2.mk_isDiag_iff.not.mpr o.2⟩

/-- The reversed ordered pair `(j, i)`. -/
def OPair.swap (o : OPair V) : OPair V := ⟨(o.1.2, o.1.1), o.2.symm⟩

end MeanBudgetXC



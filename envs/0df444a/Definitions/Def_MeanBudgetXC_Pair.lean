-- Prove2me | Definitions.Def_MeanBudgetXC_Pair
-- name    : MeanBudgetXC_Pair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:36.873074+00:00
-- url     : https://prove2.me/theorems/8414e387-1890-4a81-a304-cc2a6f5895fe
-- title:
--   Pair coordinates: unordered pairs of distinct vertices
-- statement:
--   The **pair coordinates** of a finite vertex set $V$ are the unordered pairs $\{i,j\}$ with $i\ne j$. There are $M=\binom{N}{2}$ of them when $|V|=N$. A **pair array** is a real vector $q=(q_{ij})$ indexed by these pairs, so $q_{ij}=q_{ji}$ by construction.
--
--   The pair coordinates are the ambient coordinates of every body in this mission.
--
--   **Formalization Note** The paper's vertex set is $[N]$. Here it is a generic finite type, instantiated at `Fin N` in the goal; at `Fin N` this is definitionally the platform's edge type `ExtensionComplexity.TSP.Edge N`. The module also records the `Fintype` instance.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 1.1, p.3

import Mathlib

namespace MeanBudgetXC

variable {V : Type*} [DecidableEq V]

/-- The **pair coordinates** of the vertex set `V`: unordered pairs `{i, j}` with `i ≠ j`
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 1.1, p.3: the `M = (N choose 2)` pair
probabilities `q_ij`). A pair array is a function `Pair V → ℝ`.

**Formalization Note** The paper's vertex set is `[N]`; here it is a generic finite type `V`
(`N = card V`), and the mission's goal instantiates `V = Fin N`, where `Pair (Fin N)` is
definitionally the platform's `ExtensionComplexity.TSP.Edge N`. -/
abbrev Pair (V : Type*) : Type _ := {e : Sym2 V // ¬ e.IsDiag}

/-- `Pair V` is finite when `V` is (stated explicitly: instance search does not always find the
decidability of `¬ e.IsDiag` on structured vertex types). -/
instance Pair.fintype [Fintype V] : Fintype (Pair V) :=
  @Subtype.fintype _ (fun e : Sym2 V => ¬ e.IsDiag)
    (fun e => @instDecidableNot _ (Sym2.IsDiag.decidablePred V e)) _

end MeanBudgetXC



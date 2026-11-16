-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_graphCode
-- name    : MeanBudgetXC_Supplement_graphCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:11:09.913049+00:00
-- url     : https://prove2.me/theorems/397b90ce-5c33-4d90-b911-01c97958a558
-- title:
--   The binary encoding of a binary-cap instance
-- statement:
--   A binary-cap instance $(N,u_F)$ is encoded over $\{0,1\}$ as $N$ in unary ($N$ ones), a separator $0$, and then the $M=\binom N2$ bits $u_{ij}=\mathbf 1[ij\in E(F)]$, one per pair $i<j$, in lexicographic order of $(i,j)$. This is the full-cap encoding the paper mentions ("The full cap has $O(N^2)$ bits").
--
--   **Formalization Note** The paper fixes no encoding; this one is injective in $(N,F)$ and has length $N+1+\binom N2$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 7.2, p.36

import Mathlib

namespace MeanBudgetXC.Supplement

/-- The **binary encoding** of a binary-cap instance `(N, u_F)` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 7.2,
p.36: "The full cap has O(N²) bits"): `N` in unary (`N` copies of `1`), a separator `0`, and
then the `M = (N choose 2)` bits `u_ij = 1[ij ∈ E(F)]` of the cap, one per pair `i < j`, in
lexicographic order of `(i, j)`.

**Formalization Note** The paper fixes no encoding; this is the full-cap encoding it mentions,
written over the alphabet `Bool`. It is injective in `(N, F)`. -/
def graphCode (N : ℕ) (F : SimpleGraph (Fin N)) [DecidableRel F.Adj] : List Bool :=
  List.replicate N true ++ false ::
    (List.finRange N).flatMap fun i =>
      (List.finRange N).filterMap fun j => if i < j then some (decide (F.Adj i j)) else none

end MeanBudgetXC.Supplement



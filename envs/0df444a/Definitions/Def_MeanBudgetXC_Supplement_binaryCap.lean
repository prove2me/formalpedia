-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_binaryCap
-- name    : MeanBudgetXC_Supplement_binaryCap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:10:50.822642+00:00
-- url     : https://prove2.me/theorems/d3144f85-bcf1-43c0-8120-a2b9f4711e65
-- title:
--   The binary cap $u_F=\mathbf 1_{E(F)}$
-- statement:
--   For a graph $F$ on the vertex set, the **binary cap** $u_F=\mathbf 1_{E(F)}$ is the pair array with $u_{ij}=1$ when $ij$ is an edge of $F$ and $u_{ij}=0$ otherwise.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 7.2, p.36; Appendix F.2, p.49

import Mathlib
import Definitions.Def_MeanBudgetXC_Pair

namespace MeanBudgetXC.Supplement

/-- The **binary cap** `u_F = 1_{E(F)}` of a graph `F` on the vertex set `V` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 7.2, p.36, and Appendix F.2, p.49): `1` on the pair coordinates that are edges
of `F` and `0` elsewhere. -/
noncomputable def binaryCap {V : Type*} (F : SimpleGraph V) : Pair V → ℝ :=
  open Classical in fun e => if e.1 ∈ F.edgeSet then 1 else 0

end MeanBudgetXC.Supplement



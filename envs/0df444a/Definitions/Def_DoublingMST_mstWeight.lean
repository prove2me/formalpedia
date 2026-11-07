-- Prove2me | Definitions.Def_DoublingMST_mstWeight
-- name    : DoublingMST_mstWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:35.988642+00:00
-- url     : https://prove2.me/theorems/cf86514c-73da-4a32-8dbe-5e2b54280f3a
-- title:
--   MST weight $\mathrm{MST}(X)$
-- statement:
--   $\mathrm{MST}(X)$ is the minimum of $w(T)$ over the spanning trees $T$ of $X$: the weight of a minimum spanning tree.
--
--   **Formalization Note** Defined as an infimum over the (finite, nonempty for $n\ge1$) set of spanning trees; it is attained exactly by the MSTs.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §1, p.1 (PDF p.3); §4.2, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsSpanningTree
import Definitions.Def_DoublingMST_completeGraph
import Definitions.Def_DoublingMST_treeWeight

namespace DoublingMST

/-- **The MST weight MST(X).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §1, p.1 (PDF p.3) and §4.2, p.20 (PDF p.22): MST(X) = w(T*), the weight of a minimum
spanning tree of X.

`mstWeight d` is the infimum of `treeWeight d T` over the spanning trees `T` of the complete graph
on `Fin n`.

**Formalization Note.** For `n ≥ 1` the set of spanning trees is finite and nonempty, so the
infimum is a minimum, attained exactly by the MSTs (`(completeGraph n).IsMST (edgeCost d) T`).
Statements assume the standing `2 ≤ n`. -/
noncomputable def mstWeight {n : ℕ} (d : Fin n → Fin n → ℝ) : ℝ :=
  sInf {w : ℝ | ∃ T : Finset (Sym2 (Fin n)), (completeGraph n).IsSpanningTree T ∧ treeWeight d T = w}

end DoublingMST



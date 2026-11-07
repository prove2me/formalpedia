-- Prove2me | Definitions.Def_DoublingMST_IsApproxMST
-- name    : DoublingMST_IsApproxMST
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:51.402359+00:00
-- url     : https://prove2.me/theorems/3f7ec81c-2115-42d8-afd1-a3067154def0
-- title:
--   $(1+\epsilon)$-approximate MST, output as label pairs
-- statement:
--   A list `out` of integer pairs is a **$(1+\epsilon)$-approximate MST** of $(X,d)$ under the labelling $\iota$ if
--
--   1. it has exactly $n-1$ entries, each a pair of labels;
--   2. the edges it names form a spanning tree $T$ of $X$;
--   3. $w(T)\le(1+\epsilon)\,\mathrm{MST}(X)$.
--
--   **Formalization Note** A spanning tree has $n-1$ edges, so the $n-1$ entries name distinct edges and the sum of $d$ over the list is $w(T)$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §1, p.1 (PDF p.3); Definition 2.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsSpanningTree
import Definitions.Def_DoublingMST_completeGraph
import Definitions.Def_DoublingMST_treeWeight
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_DoublingMST_decodeEdges

namespace DoublingMST

/-- **A (1 + ϵ)-approximate MST, output as label pairs.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §1, p.1 (PDF p.3): "the objective is to compute a spanning tree on X whose total weight is
at most (1 + ϵ) times the weight of the exact MST", output as in Definition 2.1, p.11: "a list of
n − 1 pairs of point labels".

`IsApproxMST d ι ϵ out`: `out` has `n − 1` entries, each a pair of labels; the edges they name form
a spanning tree of `X`; and its weight is at most `(1 + ϵ) · MST(X)`.

**Formalization Note.** A spanning tree on `n` points has `n − 1` edges, so the `n − 1` entries
name `n − 1` distinct edges, and the weight of the list (the sum of `d` over its entries) equals
`treeWeight d (decodeEdges ι out)`. The orientation of each pair is irrelevant. -/
def IsApproxMST {n : ℕ} (d : Fin n → Fin n → ℝ) (ι : Fin n → ℤ) (ϵ : ℝ)
    (out : List (ℤ × ℤ)) : Prop :=
  out.length = n - 1 ∧ (∀ p ∈ out, (∃ a, ι a = p.1) ∧ (∃ b, ι b = p.2)) ∧
    (completeGraph n).IsSpanningTree (decodeEdges ι out) ∧
    treeWeight d (decodeEdges ι out) ≤ (1 + ϵ) * mstWeight d

end DoublingMST



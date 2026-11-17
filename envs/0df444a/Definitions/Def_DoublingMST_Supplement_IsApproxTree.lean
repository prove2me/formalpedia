-- Prove2me | Definitions.Def_DoublingMST_Supplement_IsApproxTree
-- name    : DoublingMST_Supplement_IsApproxTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:16:49.331199+00:00
-- url     : https://prove2.me/theorems/554f91ee-12cc-456c-8c48-753fea6ef4c6
-- title:
--   An $\alpha$-approximate spanning tree, as an explicit edge set
-- statement:
--   Let $d$ be a distance function on the points $\{0,\dots,n-1\}$ and $\alpha\ge 1$. An edge set $T$ of unordered pairs is an **$\alpha$-approximate spanning tree** if $T$ is a spanning tree of the complete graph $K_n$ and
--
--   $$w_d(T)=\sum_{\{u,v\}\in T} d(u,v)\le \alpha\cdot \mathrm{MST}(d).$$
--
--   This is the success condition of the decision-tree lower bounds of Section 6 (with $\alpha=1+\epsilon$ in Theorem 6.7), whose leaves carry explicit edge sets.
--
--   **Formalization Note** The edge-set counterpart of the published `DoublingMST.IsApproxMST`, which reads the tree from $n-1$ label pairs of a real-RAM output; it uses the published `completeGraph`, `treeWeight` and `mstWeight`.
-- source:
--   Höckendorff–Hommelsheim–Sohler–Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 6.3, p.31 (PDF p.33); Theorem 6.7, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsSpanningTree
import Definitions.Def_DoublingMST_completeGraph
import Definitions.Def_DoublingMST_treeWeight
import Definitions.Def_DoublingMST_mstWeight

namespace DoublingMST.Supplement

/-- **An α-approximate spanning tree, as an edge set.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning
Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 6.3,
p.31 (PDF p.33) ("an explicit α-approximate MST") and Theorem 6.7, p.34 (PDF p.36) ("a
(1 + ϵ)-approximate spanning tree").

`IsApproxTree d α T`: `T` is a spanning tree of the complete graph on `Fin n` and
`w(T) ≤ α · MST(X)`.

**Formalization Note.** The edge-set form of the published `DoublingMST.IsApproxMST` (which reads
the tree from `n − 1` label pairs of a real-RAM output), for the decision-tree models of §6.1,
whose leaves are explicit edge sets. `α = 1 + ϵ` in Theorem 6.7. -/
def IsApproxTree {n : ℕ} (d : Fin n → Fin n → ℝ) (α : ℝ) (T : Finset (Sym2 (Fin n))) : Prop :=
  (DoublingMST.completeGraph n).IsSpanningTree T ∧ DoublingMST.treeWeight d T ≤ α * DoublingMST.mstWeight d

end DoublingMST.Supplement



-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_IsEulerian
-- name    : EulerSparsify_DiGraph_IsEulerian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:14.758195+00:00
-- url     : https://prove2.me/theorems/8494f4a9-8959-4d2f-aa16-ac45dbe63e0f
-- title:
--   Eulerian graph: $B^\top w=0$
-- statement:
--   A weighted directed graph $\vec G=(V,E,w)$ is **Eulerian** if $w$ is a circulation,
--
--   $$B^\top w = 0,$$
--
--   that is, at every vertex the total weight of the edges leaving it equals the total weight of the edges entering it. For Eulerian graphs $\vec L\mathbf 1=0$ as well as $\vec L^\top\mathbf 1=0$.
--
--   **Formalization Note** A self-loop contributes nothing to $B^\top w$.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §1, p.1 (PDF p.3); §3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_incMat

namespace EulerSparsify

/-- **Eulerian graph** (§1, p.1, PDF p.3; §3, p.10, PDF p.12).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), p.1: "Eulerian graphs, in
which every vertex has equal weighted in-degree and out-degree"; p.10: "If ⃗G is Eulerian, then …
w is a circulation in ⃗G, i.e., Bᵀw = 0_V."

`G.IsEulerian` says `Bᵀw = 0`: at every vertex the total weight of the edges leaving it equals the
total weight of the edges entering it.

**Formalization Note.** A self-loop contributes nothing to `Bᵀw`. -/
def DiGraph.IsEulerian {V E : Type} [Fintype E] [DecidableEq V] (G : DiGraph V E) : Prop :=
  G.incMat.transpose.mulVec G.w = 0

end EulerSparsify



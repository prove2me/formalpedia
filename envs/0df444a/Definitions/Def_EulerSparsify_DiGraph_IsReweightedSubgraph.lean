-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_IsReweightedSubgraph
-- name    : EulerSparsify_DiGraph_IsReweightedSubgraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:26.182197+00:00
-- url     : https://prove2.me/theorems/9211fc03-cdff-402c-a409-60b11709a85d
-- title:
--   Reweighted subgraph
-- statement:
--   New weights $w'\in\mathbb R^E$ describe a **reweighted subgraph** of $\vec G=(V,E,w)$ if
--
--   1. $w'_e\ge 0$ for every edge $e$, and
--   2. $w'_e=0$ whenever $w_e=0$.
--
--   The reweighted graph is $\vec H=(V,\mathrm{supp}(w'),w')$: its edges are among the edges of $\vec G$ of positive weight and carry new weights. The paper notes that in all its constructions the sparsifier is a reweighted subgraph, and Algorithm 5.2 returns $(V,\mathrm{supp}(w_t),w_t)$.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §1, p.1 (PDF p.3); Algorithm 5.2, line 9, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph

namespace EulerSparsify

/-- **Reweighted subgraph** (§1, p.1, PDF p.3; Algorithm 5.2, p.23, PDF p.25).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), p.1: "An ε-approximate Eulerian sparsifier of ⃗G is a sparse graph ⃗H that is an ε-Eulerian
spectral approximation of ⃗G; in all our constructions, ⃗H is a reweighted subgraph of ⃗G";
Algorithm 5.2, line 9: "return ⃗H ← (V, supp(w_t), w_t)".

`G.IsReweightedSubgraph w'` says that the new weights `w'` are nonnegative and vanish on every
edge of weight zero in `G`, so that `(V, supp(w'), w')` is a subgraph of `(V, supp(w), w)` with new
weights.

**Formalization Note.** The reweighted graph is `G.withWeights w'`, with the same edge labels;
its edges are those with `w' e ≠ 0`, counted by `nnz w'`. -/
def DiGraph.IsReweightedSubgraph {V E : Type} (G : DiGraph V E) (w' : E → ℝ) : Prop :=
  (∀ e, 0 ≤ w' e) ∧ ∀ e, G.w e = 0 → w' e = 0

end EulerSparsify



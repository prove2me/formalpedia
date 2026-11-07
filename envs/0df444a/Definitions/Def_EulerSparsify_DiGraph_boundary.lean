-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_boundary
-- name    : EulerSparsify_DiGraph_boundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:15.660596+00:00
-- url     : https://prove2.me/theorems/dfef2661-d8f7-4a31-bee3-ad8dd4a9ae3a
-- title:
--   Boundary $\partial_W S$ and level sets $S_\varphi[\theta]$
-- statement:
--   For $W\subseteq V$ and $S\subseteq W$, the **boundary** $\partial_W S$ is the set of edges of the induced subgraph $G[W]$ with exactly one endpoint in $S$, and $w(\partial_W S)$ is their total weight. For a potential vector $\varphi$ and a threshold $\theta$, the **level set** is
--
--   $$S_\varphi[\theta]=\{v\in W:\ \varphi(v)\ge\theta\}.$$
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §7, p.34 (PDF p.36); Algorithm 7.1, p.36

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph

namespace EulerSparsify

/-- **Boundary of `S` inside `G[W]`** `∂_W S` (§7, p.34, PDF p.36).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §7, p.34: "for W ⊆ V and S ⊆ W, ∂_W S is the set of boundary edges of S in the induced
subgraph G[W], and w(∂_W S) is their total weight."

The edges with both endpoints in `W` and exactly one endpoint in `S`. -/
def DiGraph.boundary {V E : Type} [Fintype E] [DecidableEq V] (G : DiGraph V E)
    (W S : Finset V) : Finset E :=
  Finset.univ.filter fun e =>
    G.head e ∈ W ∧ G.tail e ∈ W ∧ (G.head e ∈ S ↔ G.tail e ∉ S)

/-- **Level set** `S_φ[θ] = {v ∈ W : φ(v) ≥ θ}` of potentials `φ` (Algorithm 7.1, §7, p.36). -/
noncomputable def levelSet {V : Type} (W : Finset V) (φ : V → ℝ) (θ : ℝ) : Finset V :=
  W.filter fun v => θ ≤ φ v

end EulerSparsify



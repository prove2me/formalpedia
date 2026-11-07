-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_DiamERLe
-- name    : EulerSparsify_DiGraph_DiamERLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:00.29174+00:00
-- url     : https://prove2.me/theorems/6bd4d758-27db-47c8-8815-22c7a3d52d51
-- title:
--   ER diameter bound $\mathrm{diam}_{\mathrm{ER}}(K)\le\rho$
-- statement:
--   For a subgraph $K$ with vertex set $U$ (and edges inside $U$), the ER diameter is $\mathrm{diam}_{\mathrm{ER}}(K)=\max_{u,v\in U}\mathrm{ER}_K(u,v)$. The bound $\mathrm{diam}_{\mathrm{ER}}(K)\le\rho$ means:
--
--   1. $K$ is connected on $U$ through positive-weight edges, and
--   2. $\mathrm{ER}_K(u,v)\le\rho$ for all $u,v\in U$.
--
--   **Formalization Note** Connectivity is part of the bound because effective resistance between components is $+\infty$; the paper itself uses "$\widehat K_{i'}$ is connected as $\mathrm{diam}_{\mathrm{ER}}(\widehat K_{i'})\le\rho$" (p.13). For $U=\emptyset$ the bound holds for every $\rho$, and for a single vertex iff $\rho\ge 0$.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, p.10 (PDF p.12); Definition 2.1 item 2, p.4; proof of Proposition 4.3, p.13

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_effRes
import Definitions.Def_EulerSparsify_DiGraph_Reach

namespace EulerSparsify

/-- **ER diameter bound** `diam_ER(K) ≤ ρ` (§3, p.10, PDF p.12; Definition 2.1 item 2, p.4).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), p.10: "Given a graph G, we let diam_ER(G) = max_{u,v∈V(G)} ER_G(u, v)"; p.13, PDF p.15:
"bK_{i′} is connected as diam_ER(bK_{i′}) ≤ ρ".

`G.DiamERLe U ρ` says that the graph `G` (a subgraph with vertex set `U`, encoded by zero weights
outside its edges) is connected on `U` through positive-weight edges and that
`ER_G(u, v) ≤ ρ` for all `u, v ∈ U`.

**Formalization Note.** Connectivity is part of the bound: the true effective resistance between
two components is `+∞`, whereas the pseudoinverse formula returns a finite number; the paper uses
"connected as diam_ER ≤ ρ". For `U = ∅` the bound holds for every `ρ`; for a single vertex it
holds iff `ρ ≥ 0`. -/
def DiGraph.DiamERLe {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (U : Finset V) (ρ : ℝ) : Prop :=
  G.ConnectedOn U ∧ ∀ u ∈ U, ∀ v ∈ U, G.effRes u v ≤ ρ

end EulerSparsify



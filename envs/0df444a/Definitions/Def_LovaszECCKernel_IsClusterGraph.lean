-- Prove2me | Definitions.Def_LovaszECCKernel_IsClusterGraph
-- name    : LovaszECCKernel_IsClusterGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:46.450852+00:00
-- url     : https://prove2.me/theorems/138bfa3e-bc94-419a-af4b-0d8777db97af
-- title:
--   Cluster graphs
-- statement:
--   A graph $H$ is a **cluster graph** if each connected component of $H$ is a complete graph. Equivalently, $H$ has no two vertices at distance exactly two: whenever $uv$ and $vw$ are edges and $u\ne w$, also $uw$ is an edge.
--
--   A graph $H$ is complete multipartite exactly when its complement $\overline H$ is a cluster graph; Cluster Editing asks for the fewest modifications that turn a graph into a cluster graph.
--
--   **Formalization Note** Stated as the transitivity condition above (adjacency restricted to distinct vertices is transitive).
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15, and §3.2, p.21 (= PDF pp.15, 21)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

/-- A **cluster graph** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets
Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027
submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15)): "A graph G is said to be a
cluster graph if each connected component of G is a complete graph, i.e., its vertex set forms a
clique." Equivalently (p.21), "it contains no pairs of vertices at distance exactly two".

**Formalization Note** Stated as transitivity of adjacency on distinct vertices: if `uv` and `vw`
are edges and `u ≠ w` then `uw` is an edge. This says that "equal or adjacent" is an equivalence
relation, whose classes are the components, each a clique. -/
def IsClusterGraph {V : Type*} (H : SimpleGraph V) : Prop :=
  ∀ u v w : V, H.Adj u v → H.Adj v w → u ≠ w → H.Adj u w

end LovaszECCKernel



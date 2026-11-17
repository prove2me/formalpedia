-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_treePath
-- name    : MonoidProdQ_Supplement_treePath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:12:00.126965+00:00
-- url     : https://prove2.me/theorems/353104c1-037e-4b82-b6de-bf348101a5a8
-- title:
--   Root-to-vertex path $P(v)$ in a rooted tree
-- statement:
--   For a finite rooted tree $T$ with root $\rho$ and a vertex $v$, $P(v)$ is the set of vertices on the path from $\rho$ to $v$, **including both endpoints**. In Theorem 42 a vertex is marked by a predicate of the answers $(g_w(x))_{w\in P(v)}$ along its root path.
--
--   **Formalization Note** The tree is the published rooted-tree model (a root and a parent map with the parent of the root equal to the root, under which every vertex reaches the root). $P(v)$ is the set of iterated parents of $v$ up to its depth; it contains $v$ and the root.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 42, p.58

import Definitions.Def_HarelTarjan_Compressed_RootedTree

namespace MonoidProdQ.Supplement

open HarelTarjan.Compressed

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 42, p.58: for a finite rooted tree
`T` with root `ρ`, "P(v) [is] the root-to-v path, including both endpoints".

**Formalization Note.** The tree is the published `HarelTarjan.Compressed.RootedTree` (a root and
a parent map, `parent root = root`, under which every vertex reaches the root). `P(v)` is the set
of iterated parents `parentᵏ(v)`, `0 ≤ k ≤ depth(v)`: it contains `v` (`k = 0`) and the root
(`k = depth(v)`). -/
def treePath {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V) (v : V) : Finset V :=
  (Finset.range (depth T v + 1)).image fun k => T.parent^[k] v

end MonoidProdQ.Supplement



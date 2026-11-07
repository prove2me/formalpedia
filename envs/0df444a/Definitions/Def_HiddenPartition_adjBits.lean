-- Prove2me | Definitions.Def_HiddenPartition_adjBits
-- name    : HiddenPartition_adjBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:26.57469+00:00
-- url     : https://prove2.me/theorems/d3099458-a1ee-4fc5-8544-1a12401b18a3
-- title:
--   Row-major adjacency bits of a graph on $\{0,\dots,n-1\}$
-- statement:
--   For a simple graph $G$ on the vertex set $\{0,\dots,n-1\}$, $\mathrm{adjBits}(G)$ is the list of the $n^2$ bits of its adjacency matrix in row-major order: the bit in position $u\cdot n+v$ is $1$ exactly when $u$ and $v$ are adjacent.
--
--   It is the matrix part of the input and output codes of the algorithm of Theorem 1.1.
--
--   **Formalization Note** The bit is decided classically, so the list depends only on the graph.
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), Theorem 1.1, p.2 (pdf p.4) (encoding of the algorithm's graphs)

import Mathlib

set_option autoImplicit false

open Classical

namespace HiddenPartition

/-- **Adjacency bits of a graph on `Fin n`** (encoding used for the inputs and outputs of the
algorithm of Theorem 1.1, Agrawal et al., STOC 2027 submission, manuscript sha256 17239d0b…,
p.2 (pdf p.4)).

The list of the `n²` bits `[u ~ v]` of the adjacency matrix in row-major order: the bit at
position `u * n + v` is `true` exactly when `u` and `v` are adjacent in `G`.

**Formalization Note.** The bit is decided classically, so the list depends on the graph alone
and not on any decidability instance. `finProdFinEquiv.symm p = (p / n, p % n)`, so position
`p` holds the bit of the pair `(p / n, p % n)`. -/
noncomputable def adjBits {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool :=
  List.ofFn (fun p : Fin (n * n) =>
    decide (G.Adj (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2))

end HiddenPartition



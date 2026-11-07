-- Prove2me | Definitions.Def_GenTuranHard_leafAdd
-- name    : GenTuranHard_leafAdd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:15.046292+00:00
-- url     : https://prove2.me/theorems/88a6ba8a-a527-42a0-86ea-e5e23f107dd0
-- title:
--   Leaf additions $L_x(G)$ and $L_{\mathbf x}(G) = L_{x_1}(L_{x_2}(\cdots L_{x_s}(G)\cdots))$
-- statement:
--   Given a graph $G$ and a positive integer $x$, $L_x(G)$ is obtained from $G$ by attaching $x$ leaves to every vertex of $G$, where all added vertices are distinct and lie outside $V(G)$ (§4.1, p.12). For $\mathbf x = (x_1, \dots, x_s)$ (p.14),
--
--   $$
--   L_{\mathbf x}(G) = L_{x_1}(L_{x_2}(\cdots L_{x_s}(G) \cdots)).
--   $$
--
--   At every level leaves are attached to every vertex of the previous graph, including earlier leaves, so $v(L_{\mathbf x}(G)) = v(G) \prod_{i=1}^{s}(x_i + 1)$.
--
--   These graphs carry the expansion of $\hom(T, L_{\mathbf x}(G))$ (Lemmas 4.1 and 4.3) on which the reduction rests.
--
--   **Formalization Note** For $G$ on $\{0,\dots,n-1\}$, $L_x(G)$ has vertex set $\{0, \dots, n + nx - 1\}$: the vertices $0,\dots,n-1$ carry $G$ and the $j$-th leaf ($j < x$) of the anchor $v$ is $n + vx + j$. Hence at every level of $L_{\mathbf x}(G)$ the original graph $G$ occupies the first $n$ vertices.
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), §4.1, p.12 (L_x(G)); p.14 (L_x(G) for a vector x)

import Mathlib
import Definitions.Def_GenTuranHard_FinGraph

set_option autoImplicit false

namespace GenTuranHard

/-- The **leaf addition** `L_x(G)` (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, §4.1,
p.12): the graph obtained from `G` by attaching `x` leaves to every vertex of `G`, all added vertices
distinct and outside `V(G)`. The vertex set is `Fin (n + n·x)` with `n = v(G)`: the vertices `0, …, n−1`
carry `G`, and the `j`-th leaf (`j < x`) of the anchor `v` is `n + v·x + j`, so a leaf `b ≥ n` has
anchor `(b − n) / x`. The edges are those of `G` together with the anchor–leaf edges. -/
noncomputable def leafAdd (x : ℕ) (G : FinGraph) : FinGraph :=
  ⟨G.1 + G.1 * x, SimpleGraph.fromRel fun a b : Fin (G.1 + G.1 * x) =>
    (∃ (ha : a.val < G.1) (hb : b.val < G.1), G.2.Adj ⟨a.val, ha⟩ ⟨b.val, hb⟩) ∨
      (a.val < G.1 ∧ G.1 ≤ b.val ∧ (b.val - G.1) / x = a.val)⟩

/-- The **iterated leaf addition** `L_x(G) = L_{x₁}(L_{x₂}(⋯ L_{x_s}(G)⋯))` (p.14) for the list
`x = [x₁, …, x_s]`. Leaves are attached at every level to every vertex of the previous graph, including
earlier leaves. At every level the original graph `G` sits on the first `v(G)` vertices. -/
noncomputable def iterLeaf (x : List ℕ) (G : FinGraph) : FinGraph :=
  x.foldr leafAdd G

end GenTuranHard



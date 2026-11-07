-- Prove2me | Definitions.Def_EulerSparsify_NestedFamily
-- name    : EulerSparsify_NestedFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:38.313976+00:00
-- url     : https://prove2.me/theorems/54f98195-11a0-4a7b-b655-1eb00fe9d846
-- title:
--   Data of a nested family $\{K_i,F_i,b_i\}_{i\in[I]}$ and $w_{\min}$
-- statement:
--   A finite family $\{K_i,F_i,b_i\}_{i\in[I]}$ as in Definition 2.1: for each index $i$, a vertex set $U_i$ and an edge set $E_i$ (the subgraph $K_i=(U_i,E_i)$), a set $F_i$ of owned edges, and an integer exponent $j_i$ that fixes the weight scale
--
--   $$b_i=2^{j_i}\,w_{\min},\qquad w_{\min}=\min_{e\in E}w_e .$$
--
--   The conditions of a nested ER partitioning are imposed separately (`IsNestedER`).
--
--   **Formalization Note** $w_{\min}$ is taken to be $0$ when there are no edges (then every condition involving it is vacuous).
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Definition 2.1, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph

namespace EulerSparsify

/-- **A finite family `{K_i, F_i, b_i}_{i∈[I]}`** (data of Definition 2.1, p.4, PDF p.6).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Definition 2.1: "We call {K_i, F_i, b_i}_{i∈[I]} a ρ-nested effective resistance (ER)
partitioning if K_i are subgraphs of G with F_i ⊆ E_i = E(K_i) …"

Index `i : Fin I`; `K_i` has vertex set `U i` and edge set `Ed i`; `F i` is the set of edges it
owns; `b_i = 2^{j i} · w_min` is recorded by the integer exponent `j i`.

**Formalization Note.** The conditions are in `IsNestedER`; this structure only carries the data. -/
structure NestedFamily (V E : Type) where
  /-- the number of members -/
  I : ℕ
  /-- the vertex set of `K_i` -/
  U : Fin I → Finset V
  /-- the edge set `E_i = E(K_i)` -/
  Ed : Fin I → Finset E
  /-- the owned edges `F_i ⊆ E_i` -/
  F : Fin I → Finset E
  /-- the exponent `j` with `b_i = 2^j · w_min` -/
  j : Fin I → ℤ

/-- The minimum edge weight `w_min` (Definition 2.1, p.4); `0` if there are no edges. -/
noncomputable def DiGraph.wmin {V E : Type} [Fintype E] (G : DiGraph V E) : ℝ :=
  if h : (Finset.univ : Finset E).Nonempty then Finset.univ.inf' h G.w else 0

/-- The weight-scale lower bound `b_i = 2^{j_i} · w_min` of the `i`-th member. -/
noncomputable def NestedFamily.b {V E : Type} [Fintype E] (G : DiGraph V E)
    (P : NestedFamily V E) (i : Fin P.I) : ℝ :=
  (2 : ℝ) ^ (P.j i) * G.wmin

end EulerSparsify



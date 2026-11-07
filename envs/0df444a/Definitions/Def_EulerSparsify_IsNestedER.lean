-- Prove2me | Definitions.Def_EulerSparsify_IsNestedER
-- name    : EulerSparsify_IsNestedER
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:19.469839+00:00
-- url     : https://prove2.me/theorems/28f83bdb-a061-464a-892f-10c05d041f4e
-- title:
--   Definition 2.1 — $\rho$-nested effective resistance partitioning
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph with positive weights, $m=|E|$ and minimum weight $w_{\min}$. A family $\{K_i,F_i,b_i\}_{i\in[I]}$, where $K_i=(U_i,E_i)$ is a subgraph of $G$ (every edge of $E_i$ has both endpoints in $U_i$) and $F_i\subseteq E_i$, is a **$\rho$-nested ER partitioning** if:
--
--   1. the $F_i$ are pairwise disjoint and $\bigl|\bigcup_i F_i\bigr|\ge \tfrac12 m$;
--   2. the unweighted copy $\widehat K_i$ (weight $1$ on $E_i$) satisfies $\mathrm{diam}_{\mathrm{ER}}(\widehat K_i)\le\rho$ on $U_i$;
--   3. each $b_i=2^{j}w_{\min}$ for some integer $j$;
--   4. for each $j$, the $K_i$ with $b_i=2^jw_{\min}$ are vertex-disjoint;
--   5. every $e\in E_i$ has $w_e\ge b_i$, and every $e\in F_i$ has $w_e<2b_i$;
--   6. if $b_i<b_{i'}$, then $E_i\cap E_{i'}=\emptyset$ or $E_{i'}\subseteq E_i$.
--
--   Each $K_i$ lives in one dyadic weight bucket: it owns the edges $F_i$ of weight in $[b_i,2b_i)$ and may use every heavier edge for routing; heavier edges are reused by a chain of nested subgraphs.
--
--   **Formalization Note** The exponent $j$ ranges over $\mathbb Z$ ("for some $j$"). Item 4's "disjoint" is read as vertex-disjoint, as the proof of Proposition 4.3 states ("the subgraphs $K_i$'s are vertex disjoint"). Item 2's ER diameter includes connectivity of $\widehat K_i$ on $U_i$. Positivity of the weights is assumed by every statement using the definition.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Definition 2.1, p.4 (PDF p.6), restated p.12 (PDF p.14)

import Mathlib
import Definitions.Def_EulerSparsify_NestedFamily
import Definitions.Def_EulerSparsify_DiGraph_restrict
import Definitions.Def_EulerSparsify_DiGraph_DiamERLe

namespace EulerSparsify

/-- **Definition 2.1 (Nested ER partitioning)**, p.4, PDF p.6 (restated p.12, PDF p.14).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Definition 2.1: "for a weighted graph G = (V, E, w) with m = |E| and minimum edge weight
w_min. We call {K_i, F_i, b_i}_{i∈[I]} a ρ-nested effective resistance (ER) partitioning if K_i are
subgraphs of G with F_i ⊆ E_i = E(K_i) and satisfy the following:
1. F_i's are disjoint and |⋃_{i∈[I]} F_i| ≥ ½m
2. Let bK_i be K_i without weight, diam_ER(bK_i) ≤ ρ.
3. Each b_i = 2^j · w_min for some j
4. Let I_j = {i ∈ I : b_i = 2^j · w_min}, {K_i}_{I_j} is disjoint.
5. for each e ∈ E_i, w_e ≥ b_i and if e ∈ F_i, w_e < 2b_i.
6. for b_i < b_j, either E_i ∩ E_j = ∅ or E_j ⊆ E_i."

`IsNestedER G ρ P` states: each `K_i = (U_i, E_i)` is a subgraph (`E_i` inside `U_i`), `F_i ⊆ E_i`;
items 1–6, with item 3 built in (`b_i = 2^{j_i} w_min`, `j_i ∈ ℤ`).

**Formalization Note.**
* The graph `G` is meant to have positive weights (Definition 2.1 uses `w_min` and `b_i = 2^j w_min`;
  every use in §§4–5 is on a graph with positive weights, e.g. `(V, supp(w), w_supp(w))` in
  Algorithm 5.1); each statement assumes it.
* "for some j": `j ∈ ℤ`.
* Item 4 "disjoint" means vertex-disjoint (p.13: "for i ∈ I_j, the subgraphs K_i's are vertex
  disjoint").
* Item 2: `bK_i` is `G.unitOn E_i` (weight 1 on `E_i`) with vertex set `U_i`, and
  `diam_ER(bK_i) ≤ ρ` includes that `bK_i` is connected on `U_i` (`DiGraph.DiamERLe`).
* Item 1's `m` is the number of edges of `G`. -/
def IsNestedER {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (ρ : ℝ) (P : NestedFamily V E) : Prop :=
  (∀ i, P.Ed i ⊆ G.inducedEdges (P.U i)) ∧
  (∀ i, P.F i ⊆ P.Ed i) ∧
  -- item 1
  (∀ i i', i ≠ i' → Disjoint (P.F i) (P.F i')) ∧
  ((Fintype.card E : ℝ) / 2 ≤ ((Finset.univ.biUnion P.F).card : ℝ)) ∧
  -- item 2
  (∀ i, (G.unitOn (P.Ed i)).DiamERLe (P.U i) ρ) ∧
  -- item 4
  (∀ i i', i ≠ i' → P.j i = P.j i' → Disjoint (P.U i) (P.U i')) ∧
  -- item 5
  (∀ i, ∀ e ∈ P.Ed i, P.b G i ≤ G.w e) ∧
  (∀ i, ∀ e ∈ P.F i, G.w e < 2 * P.b G i) ∧
  -- item 6
  (∀ i i', P.b G i < P.b G i' → Disjoint (P.Ed i) (P.Ed i') ∨ P.Ed i' ⊆ P.Ed i)

end EulerSparsify



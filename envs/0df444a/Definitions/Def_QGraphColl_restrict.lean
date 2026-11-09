-- Prove2me | Definitions.Def_QGraphColl_restrict
-- name    : QGraphColl_restrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:19.120805+00:00
-- url     : https://prove2.me/theorems/078a20fa-28ce-4031-b780-ca0aebe747b2
-- title:
--   $G[P]$ on the same labels, vertex covers, bipartition sides and the bipartite double cover
-- statement:
--   Let $G$ be a graph on the vertex set $V$. Edge deletions retain the vertex labels and their input bits.
--
--   1. **Induced graph on the same labels.** For $P\subseteq V$, $G[P]$ keeps the edges of $G$ with both endpoints in $P$; every label outside $P$ stays, isolated. The edges of $G$ outside $G[P]$ form the graph $G\setminus G[P]$.
--   2. **Vertex cover.** $U\subseteq V$ covers $G$ if every edge of $G$ has an endpoint in $U$.
--   3. **Sides.** $G$ is bipartite with sides $A,B$ if $A\cap B=\emptyset$ and every edge joins a vertex of $A$ to a vertex of $B$.
--   4. **Bipartite double cover.** On $V\times\{0,1\}$, the vertices $(u,i)$ and $(v,j)$ are adjacent iff $i\ne j$ and $uv\in E(G)$: each vertex $v$ is replaced by $v_0,v_1$ and each edge $uv$ by $u_0v_1$ and $v_0u_1$.
--
--   These are the graph operations of the algorithm: thresholding keeps $G[P]$ and tests the rest through the cover $V\setminus P$, and the double cover reduces graph collision to the bipartite case.
--
--   **Formalization Note.** `restrict G P` is a graph on the same type `V` (Mathlib's `induce` would change the vertex type). `IsSides G A B` allows labels outside $A\cup B$; they are then isolated.
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), §2 p.12 ('Edge deletions retain the vertex labels'); Lemma 2.3 and proof, p.13; Lemmas 2.7–2.9, p.14; Lemma 3.2, p.15 (G[P])

import Mathlib

namespace QGraphColl

/-!
# Induced subgraphs on the same labels, vertex covers, bipartition sides, the bipartite double cover

A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…),
§2, p.12 ("Edge deletions retain the vertex labels and their input bits"); Lemma 2.3 and its
proof, p.13 (bipartite reduction); Lemmas 2.7–2.9, p.14 (vertex covers, sides `A`, `B`);
Lemma 3.2, p.15 (`G[P]`).

**Formalization Note.**
* `restrict G P` is the paper's `G[P]` **on the same vertex type**: it keeps the edges of `G` with
  both endpoints in `P`, and every label outside `P` becomes isolated. Mathlib's `G.induce` would
  change the vertex type and lose the labels and input bits. The edges of `G` outside `G[P]` are
  `G \ restrict G P`, an edge deletion `≤ G` on the same labels.
* `IsCover G U`: every edge of `G` has an endpoint in `U`.
* `IsSides G A B`: `A` and `B` are disjoint and every edge of `G` joins `A` to `B`, i.e. `G` is
  bipartite with sides `A`, `B`. Labels outside `A ∪ B` are allowed and are then isolated.
* `doubleCover G` is the graph of the proof of Lemma 2.3 on `V × Bool`: each `v` becomes `(v, 0)`
  and `(v, 1)`, and each edge `uv` becomes `(u, 0)(v, 1)` and `(v, 0)(u, 1)`.
-/

variable {V : Type*}

/-- Lemma 3.2, p.15: `G[P]` on the same labels: `u ~ v` iff `u ~_G v` and `u, v ∈ P`. -/
def restrict (G : SimpleGraph V) (P : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ P ∧ v ∈ P
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

/-- Lemmas 2.7, 2.9, p.14: `U` is a vertex cover of `G`: every edge has an endpoint in `U`. -/
def IsCover (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ U ∨ v ∈ U

/-- Lemma 2.8, p.14: `G` is bipartite with sides `A` and `B`: the sides are disjoint and every
edge joins a vertex of `A` to a vertex of `B`. -/
def IsSides (G : SimpleGraph V) (A B : Finset V) : Prop :=
  Disjoint A B ∧ ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

/-- Lemma 2.3 and its proof, p.13: the bipartite double cover on `V × Bool`, with `(u, i) ~ (v, j)`
iff `i ≠ j` and `u ~_G v`. -/
def doubleCover (G : SimpleGraph V) : SimpleGraph (V × Bool) where
  Adj p q := p.2 ≠ q.2 ∧ G.Adj p.1 q.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end QGraphColl



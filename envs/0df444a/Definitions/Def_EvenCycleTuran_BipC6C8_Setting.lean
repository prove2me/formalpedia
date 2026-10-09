-- Prove2me | Definitions.Def_EvenCycleTuran_BipC6C8_Setting
-- name    : EvenCycleTuran_BipC6C8_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:38.312353+00:00
-- url     : https://prove2.me/theorems/d0a880d1-557e-4d55-a23c-481a0d0014dc
-- title:
--   pp. 6, 14–17 — ex_bip, bipartitions, fat pairs and fat 6-cycles, N(u, v), g, the hypergraph 𝓗, Berge-C₄, h, marked pairs, nice sets
-- statement:
--   All graphs are finite simple graphs. For a set $\mathcal A$ of integers, a graph is **$\mathcal C_{\mathcal A}$-free** if it contains no cycle $C_a$ with $a\in\mathcal A$ as a (not necessarily induced) subgraph.
--
--   1. **The bipartite generalized Turán number.** $\mathrm{ex}_{bip}(n,H,\mathcal C_{\mathcal A})$ is the maximum number of copies of $H$ (subgraphs isomorphic to $H$) in a bipartite $\mathcal C_{\mathcal A}$-free graph on $n$ vertices. In particular $\mathrm{ex}_{bip}(n,C_6,C_8)$ is the maximum number of $6$-cycles in a bipartite $C_8$-free graph on $n$ vertices.
--   2. **$K_{k,n-k}$.** The complete bipartite graph on the vertices $0,\dots,n-1$ whose classes are $\{i<k\}$ and $\{i\ge k\}$.
--   3. **Bipartitions.** A pair $(A,B)$ of vertex sets is a bipartition of $G$ if $A$ and $B$ are disjoint, $A\cup B=V(G)$, and every edge of $G$ has one end in $A$ and one in $B$.
--   4. **Common neighbourhoods.** For vertices $u,v$, $N(u,v)=\{w : uw,vw\in E(G)\}$.
--   5. **Fat pairs.** A pair $\{u,v\}$ of distinct vertices is *fat* if $|N(u,v)|\ge 4$. In a bipartite graph $u$ and $v$ then lie in the same class, and the four common neighbours in the other class.
--   6. **Fat $6$-cycles.** A labelled $6$-cycle is a sequence of six distinct vertices $v_1,\dots,v_6$ with $v_iv_{i+1}\in E(G)$ (indices mod $6$). It is *fat* if it contains a fat pair from each class: one of $\{v_1,v_3\},\{v_3,v_5\},\{v_5,v_1\}$ is fat and one of $\{v_2,v_4\},\{v_4,v_6\},\{v_6,v_2\}$ is fat. A vertex set *lies on a fat $6$-cycle* if all its vertices are vertices of one fat $6$-cycle.
--   7. **The sum $g$.** For a pair $\{v_1,v_3\}$,
--   $$g(v_1,v_3)=\sum_{\substack{\{v_4,v_6\}\subseteq B \text{ fat}\\ v_1,v_3,v_4,v_6 \text{ on a fat } C_6}}|N(v_4,v_6)|,$$
--   the sum running over unordered pairs.
--   8. **The hypergraph $\mathcal H$.** Its hyperedges are the sets $N(v_1,v_3)$, for the fat pairs $\{v_1,v_3\}\subseteq A$ lying on at least one fat $6$-cycle (equal sets give one hyperedge).
--   9. **Berge-$C_4$.** A hypergraph (a finite family of distinct hyperedges) is *Berge-$C_4$-free* if there are no distinct vertices $x,y,z,w$ and distinct hyperedges $h_1,h_2,h_3,h_4$ with $x,y\in h_1$, $y,z\in h_2$, $z,w\in h_3$, $w,x\in h_4$.
--   10. **The count $h$.** For a vertex set $T$, $h(T)$ is the number of $6$-cycles of $G$ (subgraphs isomorphic to $C_6$) containing every vertex of $T$; $h(x,y,z)=h(\{x,y,z\})$.
--   11. **Marked pairs and nice sets.** A pair is *marked* if it has exactly three common neighbours. A $4$-set $F\subseteq A$ is *nice* if there is a $3$-set $S\subseteq B$ with every vertex of $F$ adjacent to every vertex of $S$ (a copy of $K_{4,3}$).
--
--   These are the objects of the proof of Theorem 12 in §4.2.
--
--   **Formalization Note** Vertices form a finite type (`Fin n` in the uniform statements); $\mathrm{ex}_{bip}$ is a supremum of natural numbers over a nonempty finite set (the empty graph is admissible), hence a true maximum. Copies are unlabelled (`SimpleGraph.copyCount`). "Bipartite" in $\mathrm{ex}_{bip}$ is `Colorable 2`; in the proof's statements a bipartition $(A,B)$ is fixed explicitly. Fatness is defined without reference to the classes, which is equivalent for a bipartite graph.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 6, §2.1 (ex_bip); p. 9 (K_{k−1,n−k+1}); pp. 14–17, §4.2 (fat pairs, fat 6-cycles, N(u, v), g, 𝓗, Berge-C4, h, marked, nice)

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting

open Finset SimpleGraph

namespace EvenCycleTuran.BipC6C8

/-- ex_bip(n, H, 𝒞_A): the maximum number of copies of `H` in a bipartite `n`-vertex
𝒞_A-free graph (p. 6). `ex_bip(n, C₆, C₈)` is `exBip n (cycleGraph 6) {8}`. -/
noncomputable def exBip {W : Type*} (n : ℕ) (H : SimpleGraph W) (A : Set ℕ) : ℕ :=
  sSup {N | ∃ G : SimpleGraph (Fin n), G.Colorable 2 ∧ EvenCycleTuran.C4Count.CycleFree A G ∧ G.copyCount H = N}

/-- The complete bipartite graph `K_{k, n-k}` on `Fin n`: the classes are `{i | i < k}` and
`{i | k ≤ i}`, and every vertex of the first class is adjacent to every vertex of the second. -/
def bipGraph (n k : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => i.val < k ∧ k ≤ j.val

/-- `(A, B)` is a bipartition of `G`: the classes are disjoint, cover every vertex, and every
edge of `G` joins a vertex of `A` to a vertex of `B`. -/
def IsBipartition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A B : Finset V) : Prop :=
  Disjoint A B ∧ A ∪ B = Finset.univ ∧
    ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

open Classical in
/-- `N(s)`: the vertices adjacent to every vertex of `s`. For a pair, `commonNbrs G {u, v}` is the
paper's `N(u, v) = {w : uw, vw ∈ E(G)}` (p. 14). -/
noncomputable def commonNbrs {V : Type*} [Fintype V] (G : SimpleGraph V) (s : Finset V) :
    Finset V :=
  Finset.univ.filter fun w => ∀ u ∈ s, G.Adj u w

/-- A fat pair (p. 14): a 2-set `{u, v}` of vertices with at least four common neighbours. In a
bipartite graph the two vertices then lie in the same class and the common neighbours in the
other class, as in the paper's definition. -/
def IsFatPair {V : Type*} [Fintype V] (G : SimpleGraph V) (p : Finset V) : Prop :=
  p.card = 2 ∧ 4 ≤ (commonNbrs G p).card

/-- A labelled 6-cycle `v 0, v 1, …, v 5, v 0` of `G`: six distinct vertices with consecutive
vertices adjacent (indices mod 6). -/
def IsHexagon {V : Type*} (G : SimpleGraph V) (v : Fin 6 → V) : Prop :=
  Function.Injective v ∧ ∀ i : Fin 6, G.Adj (v i) (v (i + 1))

/-- A fat 6-cycle (p. 14): a 6-cycle containing a fat pair from each class, i.e. one of the
pairs `{v 0, v 2}, {v 2, v 4}, {v 4, v 0}` is fat and one of `{v 1, v 3}, {v 3, v 5}, {v 5, v 1}`
is fat. -/
def IsFatHexagon {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : Fin 6 → V) :
    Prop :=
  IsHexagon G v ∧
    (IsFatPair G {v 0, v 2} ∨ IsFatPair G {v 2, v 4} ∨ IsFatPair G {v 4, v 0}) ∧
    (IsFatPair G {v 1, v 3} ∨ IsFatPair G {v 3, v 5} ∨ IsFatPair G {v 5, v 1})

/-- The vertices of `s` all lie on one fat 6-cycle of `G`. -/
def InFatHexagon {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : Finset V) :
    Prop :=
  ∃ v : Fin 6 → V, IsFatHexagon G v ∧ (s : Set V) ⊆ Set.range v

open Classical in
/-- `g(v₁, v₃)` (p. 15) for the pair `p = {v₁, v₃}`: the sum of `|N(v₄, v₆)|` over the fat pairs
`q = {v₄, v₆} ⊆ B` such that `v₁, v₃, v₄, v₆` lie on a common fat 6-cycle. -/
noncomputable def gSum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (B p : Finset V) : ℕ :=
  ∑ q ∈ (B.powersetCard 2).filter (fun q => IsFatPair G q ∧ InFatHexagon G (p ∪ q)),
    (commonNbrs G q).card

open Classical in
/-- The hypergraph `𝓗` of p. 15 (vertex set `B`): its hyperedges are the sets `N(v₁, v₃)` for the
fat pairs `{v₁, v₃} ⊆ A` lying on at least one fat 6-cycle. Equal neighbourhoods give one
hyperedge. -/
noncomputable def fatHypergraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) : Finset (Finset V) :=
  ((A.powersetCard 2).filter (fun p => IsFatPair G p ∧ InFatHexagon G p)).image (commonNbrs G)

/-- A hypergraph `H` (a finite set of hyperedges) is Berge-`C₄`-free (p. 16): there are no
distinct vertices `x, y, z, w` and distinct hyperedges `h₁, h₂, h₃, h₄ ∈ H` with
`x, y ∈ h₁`, `y, z ∈ h₂`, `z, w ∈ h₃`, `w, x ∈ h₄`. -/
def BergeC4Free {V : Type*} (H : Finset (Finset V)) : Prop :=
  ¬ ∃ x y z w : V, ∃ h₁ ∈ H, ∃ h₂ ∈ H, ∃ h₃ ∈ H, ∃ h₄ ∈ H,
    [x, y, z, w].Nodup ∧ [h₁, h₂, h₃, h₄].Nodup ∧
    x ∈ h₁ ∧ y ∈ h₁ ∧ y ∈ h₂ ∧ z ∈ h₂ ∧ z ∈ h₃ ∧ w ∈ h₃ ∧ w ∈ h₄ ∧ x ∈ h₄

/-- `h(T)` (p. 17): the number of (unlabelled) 6-cycles of `G` whose vertex set contains `T`,
i.e. the subgraphs of `G` isomorphic to `C₆` containing every vertex of `T`. For `T = {x, y, z}`
this is the paper's `h(x, y, z)`. -/
noncomputable def hexCount {V : Type*} [Fintype V] (G : SimpleGraph V) (T : Finset V) : ℕ := by
  classical exact #{G' : G.Subgraph | Nonempty (cycleGraph 6 ≃g G'.coe) ∧ (T : Set V) ⊆ G'.verts}

/-- A marked pair (p. 17): a 2-set with exactly three common neighbours. -/
def IsMarked {V : Type*} [Fintype V] (G : SimpleGraph V) (p : Finset V) : Prop :=
  p.card = 2 ∧ (commonNbrs G p).card = 3

/-- A nice set (p. 17): a 4-set `F ⊆ A` whose four vertices have three common neighbours in `B`,
forming a copy of `K_{4,3}`. -/
def IsNice {V : Type*} (G : SimpleGraph V) (A B F : Finset V) : Prop :=
  F ⊆ A ∧ F.card = 4 ∧ ∃ S ⊆ B, S.card = 3 ∧ ∀ x ∈ F, ∀ b ∈ S, G.Adj x b

end EvenCycleTuran.BipC6C8



-- Prove2me | Definitions.Def_DecrNbhdCover_Graph
-- name    : DecrNbhdCover_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:44.550111+00:00
-- url     : https://prove2.me/theorems/05f558c6-7046-4c41-a66d-c9e2c94ddae2
-- title:
--   Graphs with parallel edges and positive integer lengths, walks, distances, balls, well-structured graphs, $H_C$
-- statement:
--   A **graph** $G=(V(G),E(G),\ell_G)$ is undirected, may have parallel edges, has no self-loops, and has lengths $\ell_G(e)\in\mathbb Z_{>0}$. A **walk** (a possibly non-simple path) is a sequence of vertices and edges, the **length** $\ell_G(P)$ being the sum of its edge lengths; a **simple path** repeats no vertex. The distance
--   $$\mathrm{dist}_G(u,v)=\min_P \ell_G(P)$$
--   is the smallest length of a walk from $u$ to $v$, with the value $\infty$ if there is none. Also $\mathrm{dist}_G(S,v)=\min_{s\in S}\mathrm{dist}_G(s,v)$, $B_G(v,D)=\{u:\mathrm{dist}_G(u,v)\le D\}$, and $B_G(S,D)=\{u:\mathrm{dist}_G(S,u)\le D\}$. $G[C]$ is the subgraph induced by $C$.
--
--   A **well-structured graph** $H=(V,U,E(H),\ell_H)$ has regular vertices $V$ and supernodes $U$, and each edge joins $V$ to $U$. $\ell_H(v,u)$ is the length of the shortest edge between $v$ and $u$. A path $(v_1,u_1,\dots,u_k,v_{k+1})$ has **no consecutively repeated regular vertices** if $v_i\ne v_{i+1}$ for all $i$. The subgraph **associated with a cluster** $C$ is $H_C=H[C\cup N_H(C)]$: the vertices of $C$, their incident edges and the supernodes at the other ends.
--
--   These are the graph objects of every statement of the mission.
--
--   **Formalization Note** A snapshot is a raw structure with a separate well-formedness predicate, since the mission's graphs are defined by comprehension. Distances take values in $\mathbb N_\infty$, and comparisons with real numbers are made in $[0,\infty]$, so no junk value of a real infimum can enter.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), §2.1–2.2, pp.13–14 (PDF 17–18); Definition 3.1, pp.15–16 (PDF 19–20); Definition 3.10, p.20 (PDF 24); p.18 (PDF 22) for $\ell_H(v,u)$

import Mathlib

set_option autoImplicit false

namespace DecrNbhdCover

open scoped ENNReal

/-! # Graphs with parallel edges and positive integer lengths, distances, balls

Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems*
(STOC 2027 submission, sha256 4278ef58…), §2.1–2.2, pp.13–14; Definition 3.1, pp.15–16; Definition 3.10,
p.20. "All graphs in this paper are undirected. By default graphs may contain parallel edges but no self
loops"; "ℓG : E(G) → Z+"; "distG(u, v) … the smallest length ℓG(P) of any path P connecting u to v";
"BG(v, D) = {u ∈ V(G) | distG(u, v) ≤ D}".

**Formalization Note.** A `Graph α ε` is a raw snapshot: vertex and edge sets inside label types, with
endpoints and lengths given by total functions, and `Graph.WF` says it is a graph of the paper. A
`WSGraph α β ε` is a well-structured graph: the bipartition `(V, U)` is built in, regular vertices in `α` and
supernodes in `β`, so all its edges join `V` to `U`. Paths may be non-simple (p.72: "Recall that paths may be
non-simple unless mentioned otherwise"), so a walk is the general object, and `IsPath` is the simple case.
A walk is given by its vertex sequence and its edge sequence, because parallel edges are allowed. `dist` takes
values in `ℕ∞`, with `⊤` across components and on a vertex outside the graph; every comparison with a real
number is made in `ℝ≥0∞`, where `∞` stays `∞`, so no junk value of a real-valued infimum can enter. -/

/-- A snapshot of a graph: vertices, edges, endpoints and lengths. -/
structure Graph (α ε : Type) where
  V : Set α
  E : Set ε
  ends : ε → α × α
  len : ε → ℕ

namespace Graph

variable {α ε : Type}

/-- A graph of the paper: finite, every edge has two distinct endpoints in `V` and a positive length. -/
structure WF (G : Graph α ε) : Prop where
  finV : G.V.Finite
  finE : G.E.Finite
  ends_mem : ∀ e ∈ G.E, (G.ends e).1 ∈ G.V ∧ (G.ends e).2 ∈ G.V
  no_loop : ∀ e ∈ G.E, (G.ends e).1 ≠ (G.ends e).2
  pos : ∀ e ∈ G.E, 0 < G.len e

/-- `e` has endpoints `u` and `w`. -/
def Joins (G : Graph α ε) (e : ε) (u w : α) : Prop :=
  G.ends e = (u, w) ∨ G.ends e = (w, u)

/-- `IsWalk vs es`: `vs = v₀ … v_k` and `es = e₁ … e_k` form a (possibly non-simple) path of `G`. -/
inductive IsWalk (G : Graph α ε) : List α → List ε → Prop
  | nil (v : α) (hv : v ∈ G.V) : IsWalk G [v] []
  | cons (u w : α) (vs : List α) (e : ε) (es : List ε) (hu : u ∈ G.V) (he : e ∈ G.E)
      (hj : G.Joins e u w) (ih : IsWalk G (w :: vs) es) : IsWalk G (u :: w :: vs) (e :: es)

/-- A simple path: a walk that repeats no vertex. -/
def IsPath (G : Graph α ε) (vs : List α) (es : List ε) : Prop :=
  G.IsWalk vs es ∧ vs.Nodup

/-- The length `ℓG(P)` of a sequence of edges. -/
def walkLen (G : Graph α ε) (es : List ε) : ℕ :=
  (es.map G.len).sum

/-- The length of the part of the edge sequence between positions `i` and `j`, in either order: for a
simple path with vertices `v₀ … v_k`, this is `ℓG(P[v_i, v_j])`. -/
def segLen (G : Graph α ε) (es : List ε) (i j : ℕ) : ℕ :=
  G.walkLen ((es.drop (min i j)).take (max i j - min i j))

/-- `es` are the edges of a walk from `u` to `v`. -/
def WalkFromTo (G : Graph α ε) (u : α) (es : List ε) (v : α) : Prop :=
  ∃ vs, G.IsWalk vs es ∧ vs.head? = some u ∧ vs.getLast? = some v

/-- `distG(u, v)`, with value `⊤` if no path connects them. -/
noncomputable def dist (G : Graph α ε) (u v : α) : ℕ∞ :=
  ⨅ (es : List ε) (_ : G.WalkFromTo u es v), (G.walkLen es : ℕ∞)

/-- `distG(S, v) = min_{s ∈ S} distG(s, v)`, with value `⊤` for an empty `S`. -/
noncomputable def distSet (G : Graph α ε) (S : Set α) (v : α) : ℕ∞ :=
  ⨅ s ∈ S, G.dist s v

/-- The ball `BG(v, D)`. -/
noncomputable def ball (G : Graph α ε) (v : α) (D : ℝ) : Set α :=
  {u | u ∈ G.V ∧ ((G.dist u v : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal D}

/-- The ball `BG(S, D)`. -/
noncomputable def ballSet (G : Graph α ε) (S : Set α) (D : ℝ) : Set α :=
  {u | u ∈ G.V ∧ ((G.distSet S u : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal D}

/-- The subgraph `G[C]` induced by `C`. -/
def induced (G : Graph α ε) (C : Set α) : Graph α ε where
  V := C
  E := {e | e ∈ G.E ∧ (G.ends e).1 ∈ C ∧ (G.ends e).2 ∈ C}
  ends := G.ends
  len := G.len

/-- The edges incident to `v`. -/
def incident (G : Graph α ε) (v : α) : Set ε :=
  {e | e ∈ G.E ∧ ((G.ends e).1 = v ∨ (G.ends e).2 = v)}

/-- The maximum vertex degree of `G` is at most `μ`. -/
def DegLe (G : Graph α ε) (μ : ℕ) : Prop :=
  ∀ v ∈ G.V, (G.incident v).encard ≤ μ

/-- `v` is not isolated. -/
def NonIsolated (G : Graph α ε) (v : α) : Prop :=
  (G.incident v).Nonempty

end Graph

/-- A snapshot of a well-structured graph `H = (V, U, E(H), ℓH(·))` (Definition 3.1): each edge joins
the regular vertex `reg e` to the supernode `sup e`. -/
structure WSGraph (α β ε : Type) where
  V : Set α
  U : Set β
  E : Set ε
  reg : ε → α
  sup : ε → β
  len : ε → ℕ

namespace WSGraph

variable {α β ε : Type}

/-- A well-structured graph of the paper: finite, each edge has its endpoints in `V` and `U` and a positive
length. -/
structure WF (H : WSGraph α β ε) : Prop where
  finV : H.V.Finite
  finU : H.U.Finite
  finE : H.E.Finite
  reg_mem : ∀ e ∈ H.E, H.reg e ∈ H.V
  sup_mem : ∀ e ∈ H.E, H.sup e ∈ H.U
  pos : ∀ e ∈ H.E, 0 < H.len e

/-- `H` as a graph on `V ⊔ U`. -/
def toGraph (H : WSGraph α β ε) : Graph (α ⊕ β) ε where
  V := Sum.inl '' H.V ∪ Sum.inr '' H.U
  E := H.E
  ends := fun e => (Sum.inl (H.reg e), Sum.inr (H.sup e))
  len := H.len

/-- `distH(v, v′)` for regular vertices. -/
noncomputable def dist (H : WSGraph α β ε) (v v' : α) : ℕ∞ :=
  H.toGraph.dist (Sum.inl v) (Sum.inl v')

/-- `distH(S, v)` for a set `S` of regular vertices. -/
noncomputable def distSet (H : WSGraph α β ε) (S : Set α) (v : α) : ℕ∞ :=
  ⨅ s ∈ S, H.dist s v

/-- `(v, u) ∈ E(H)`. -/
def Adj (H : WSGraph α β ε) (v : α) (u : β) : Prop :=
  ∃ e ∈ H.E, H.reg e = v ∧ H.sup e = u

/-- `ℓH(v, u)`: the length of the shortest edge `(v, u)` (`⊤` if there is none). p.18: "there may be a number
of parallel edges (v, u(S)) in E(H). … we denote by ℓH(v, u(S)) the length of the shortest such edge." -/
noncomputable def ell (H : WSGraph α β ε) (v : α) (u : β) : ℕ∞ :=
  ⨅ (e : ε) (_ : e ∈ H.E ∧ H.reg e = v ∧ H.sup e = u), (H.len e : ℕ∞)

/-- The vertex sequence `(v₁, u₁, …, u_k, v_{k+1})` has no consecutively repeated regular vertices
(Definition 3.1): no regular vertex recurs two places later. -/
def NoConsecRepeat (vs : List (α ⊕ β)) : Prop :=
  ∀ (i : ℕ) (x : α), vs[i]? = some (Sum.inl x) → vs[i + 2]? ≠ some (Sum.inl x)

/-- `es` are the edges of a path of `H` from the regular vertex `v` to the regular vertex `v'` that has no
consecutively repeated regular vertices. -/
def NoRepeatPath (H : WSGraph α β ε) (v : α) (es : List ε) (v' : α) : Prop :=
  ∃ vs, H.toGraph.IsWalk vs es ∧ vs.head? = some (Sum.inl v) ∧ vs.getLast? = some (Sum.inl v') ∧
    NoConsecRepeat vs

/-- `es` are the edges of a simple path of `H` from the regular vertex `v` to some vertex of `S`. -/
def SimplePathToSet (H : WSGraph α β ε) (v : α) (es : List ε) (S : Set α) : Prop :=
  ∃ vs s, H.toGraph.IsPath vs es ∧ vs.head? = some (Sum.inl v) ∧ vs.getLast? = some (Sum.inl s) ∧ s ∈ S

/-- `ℓH(P)`. -/
def walkLen (H : WSGraph α β ε) (es : List ε) : ℕ :=
  (es.map H.len).sum

/-- The subgraph `H_C = H[C ∪ N_H(C)]` associated with a cluster `C` (Definition 3.10): the vertices of `C`, their
incident edges in `H`, and the supernodes at the other ends. -/
def assocSub (H : WSGraph α β ε) (C : Set α) : WSGraph α β ε where
  V := C
  U := {u | ∃ v ∈ C, H.Adj v u}
  E := {e | e ∈ H.E ∧ H.reg e ∈ C}
  reg := H.reg
  sup := H.sup
  len := H.len

end WSGraph

end DecrNbhdCover



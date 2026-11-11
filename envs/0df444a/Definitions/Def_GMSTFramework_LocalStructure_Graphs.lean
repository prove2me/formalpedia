-- Prove2me | Definitions.Def_GMSTFramework_LocalStructure_Graphs
-- name    : GMSTFramework_LocalStructure_Graphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:00:18.0749+00:00
-- url     : https://prove2.me/theorems/29c349e0-a835-4bf3-b905-df54a29597d8
-- title:
--   Colorful graphs, paths and linkages, separations, tangles, truncation, control of minor-models, $T_\mu$, meshes and $T_M$ (§2.1–2.3.1)
-- statement:
--   A **$q$-colorful graph** is $(G,\chi)$ with $\chi:V(G)\to 2^{[q]}$, $[q]=\{1,\dots,q\}$. A **linkage** is a set of pairwise vertex-disjoint paths; an **$A$-path** has both ends in $A$ and is internally disjoint from $A$; an **$A$-$B$-path** has one end in $A$, the other in $B$, and is internally disjoint from $A\cup B$. A **separation** is $(A,B)$ with $A\cup B=V(G)$ and no edge between $A\setminus B$ and $B\setminus A$; its order is $|A\cap B|$; $S_k(G)$ is the set of separations of order $<k$. A **tangle** of order $k$ is an orientation $\mathcal T$ of $S_k(G)$ (exactly one of $(A,B),(B,A)$ for each member) such that $G[A_1]\cup G[A_2]\cup G[A_3]\ne G$ for all $(A_i,B_i)\in\mathcal T$. $\mathcal D$ is a **truncation** of $\mathcal T$ if $\mathcal D\subseteq\mathcal T$. A minor-model $\mu$ of $H$ is **controlled** by $\mathcal T$ if no $(A,B)\in\mathcal T$ of order $<|V(H)|$ has $\mu(x)\subseteq A\setminus B$. For a $K_t$-model, $\mathcal T_\mu$ consists of the $(A,B)\in S_t$ with $\mu(u)\subseteq B\setminus A$ for some $u$.
--
--   An **$(n\times m)$-mesh** ($n,m\ge2$) is a union of horizontal paths $P_1,\dots,P_n$ (pairwise disjoint) and vertical paths $Q_1,\dots,Q_m$ (pairwise disjoint), each $P_i\cap Q_j$ a nonempty path, each $P_i$ a $V(Q_1)$-$V(Q_m)$-path meeting $Q_1,\dots,Q_m$ in order and each $Q_j$ a $V(P_1)$-$V(P_n)$-path meeting $P_1,\dots,P_n$ in order. Its **perimeter** is $P_1\cup P_n\cup Q_1\cup Q_m$; $M'$ is a **submesh** of $M$ if every horizontal (vertical) path of $M'$ is a subpath of a horizontal (vertical) path of $M$. For an $r$-mesh, $\mathcal T_M$ consists of the $(A,B)\in S_r$ such that $B\setminus A$ contains the vertex set of a horizontal and of a vertical path. A model is **controlled by $M$** if it is controlled by $\mathcal T_M$.
--
--   **Formalization Note.** Graphs are `SimpleGraph V` on a finite type; paths are walks without repeated vertices (`GPath`, a single vertex allowed); indices are 0-based (`Fin n`). Minor-models are the published `SimpleGraph.Minor` (TenChallenges_Minor). `IsTangle` is defined but no statement assumes that a set of separations is a tangle; `Mesh.tangle` and `tangleOfModel` are the sets of separations as printed.
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), p. 11–14 (PDF 14–17), §2.1, §2.2 "Colorful graphs", §2.3.1

import Mathlib
import Definitions.Def_TenChallenges_Minor

open scoped Classical

noncomputable section

namespace GMSTFramework.LocalStructure

/-!
# Colorful graphs, paths and linkages, separations, tangles, minor-models and control, meshes

Gorsky, Protopapas, Wiederrecht, *A unifying framework for Graph Minor Structure Theorems with
polynomial bounds*, STOC 2027 submission (manuscript sha256 b2ee466d…), §2.1 p. 11 (PDF 14),
§2.2 p. 12 (PDF 15), §2.3.1 p. 12–14 (PDF 15–17).

Graphs are finite simple graphs `G : SimpleGraph V` on a finite type `V`. Subgraphs are
`G.Subgraph`; a renderable graph such as `G - A` is the subgraph `(⊤ : G.Subgraph).deleteVerts A`.

* `IsColorful q χ`: `(G, χ)` is a `q`-colorful graph, `χ : V → 2^[q]` with `[q] = {1, …, q}`
  (`q = 0` allowed: then `χ ≡ ∅`).
* `GPath G`: a path of `G`, i.e. a walk from `s` to `t` without repeated vertices (a single vertex
  is a path). `IsPathSub S`, `IsCycleSub S`: the subgraph `S` is a path, resp. a cycle.
* `IsAPath`, `IsABPath`: an `A`-path, an `A`-`B`-path (one end in `A`, the other in `B`, internally
  disjoint from `A ∪ B`), p. 11.
* `Linkage G n`: `n` pairwise vertex-disjoint paths (a linkage of order `n`).
* Separations `(A, B)` (`A ∪ B = V(G)`, no edge between `A \ B` and `B \ A`), their order
  `|A ∩ B|`, `S_k(G)`, orientations, tangles of order `k`, truncation (`D ⊆ T`), control of a
  minor-model by a tangle, and the tangle `T_μ` induced by a `K_t`-minor-model (p. 12–13).
  Minor-models are the published `SimpleGraph.Minor` (pairwise disjoint connected branch sets with
  an edge between `μ(u)` and `μ(v)` for every edge `uv` of `H`).
* `Mesh G n m`: an `(n × m)`-mesh in `G` (`n, m ≥ 2`), with its horizontal paths `P` and vertical
  paths `Q` (p. 13); its perimeter, submeshes, and the orientation `T_M` of `S_r` induced by an
  `r`-mesh (p. 14). "A model controlled by `M`" means controlled by `T_M`.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `(G, χ)` is `q`-colorful: every vertex gets a (possibly empty) subset of `[q] = {1, …, q}`. -/
def IsColorful (q : ℕ) (χ : V → Finset ℕ) : Prop := ∀ v, χ v ⊆ Finset.Icc 1 q

/-- A path of `G`: a walk from `s` to `t` without repeated vertices. -/
structure GPath (G : SimpleGraph V) where
  /-- first end -/
  s : V
  /-- last end -/
  t : V
  /-- the walk -/
  walk : G.Walk s t
  /-- no repeated vertex -/
  isPath : walk.IsPath

namespace GPath

variable {G : SimpleGraph V}

/-- The vertex set of the path. -/
def verts (P : GPath G) : Finset V := P.walk.support.toFinset

/-- The path as a subgraph. -/
def sub (P : GPath G) : G.Subgraph := P.walk.toSubgraph

/-- The internal vertices: the vertices other than the two ends. -/
def inner (P : GPath G) : Finset V := P.verts.filter fun x => x ≠ P.s ∧ x ≠ P.t

/-- `P` is internally disjoint from `X`: no vertex of `P` other than an end lies in `X`. -/
def InternallyDisjoint (P : GPath G) (X : Set V) : Prop := ∀ x ∈ P.inner, x ∉ X

/-- Position of a vertex along the path (from `s`). -/
def pos (P : GPath G) (x : V) : ℕ := P.walk.support.idxOf x

end GPath

/-- The subgraph `S` is a path. -/
def IsPathSub {G : SimpleGraph V} (S : G.Subgraph) : Prop :=
  ∃ (u v : V) (w : G.Walk u v), w.IsPath ∧ w.toSubgraph = S

/-- The subgraph `S` is a cycle. -/
def IsCycleSub {G : SimpleGraph V} (S : G.Subgraph) : Prop :=
  ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ w.toSubgraph = S

/-- The subgraph `S` is the disjoint union of exactly two paths. -/
def IsTwoPaths {G : SimpleGraph V} (S : G.Subgraph) : Prop :=
  ∃ P₁ P₂ : G.Subgraph, IsPathSub P₁ ∧ IsPathSub P₂ ∧ Disjoint P₁.verts P₂.verts ∧ S = P₁ ⊔ P₂

/-- An `A`-path: both ends in `A`, internally disjoint from `A`. -/
def IsAPath {G : SimpleGraph V} (A : Set V) (P : GPath G) : Prop :=
  P.s ∈ A ∧ P.t ∈ A ∧ P.InternallyDisjoint A

/-- An `A`-`B`-path: one end in `A`, the other in `B`, internally disjoint from `A ∪ B`. -/
def IsABPath {G : SimpleGraph V} (A B : Set V) (P : GPath G) : Prop :=
  ((P.s ∈ A ∧ P.t ∈ B) ∨ (P.s ∈ B ∧ P.t ∈ A)) ∧ P.InternallyDisjoint (A ∪ B)

/-- A linkage of order `n`: `n` pairwise vertex-disjoint paths. -/
structure Linkage (G : SimpleGraph V) (n : ℕ) where
  /-- the paths -/
  path : Fin n → GPath G
  /-- pairwise vertex-disjoint -/
  disj : Pairwise fun i j => Disjoint (path i).verts (path j).verts

namespace Linkage

variable {G : SimpleGraph V} {n : ℕ}

/-- The union `⋃ P` of the paths, as a subgraph. -/
def sub (L : Linkage G n) : G.Subgraph := ⨆ i, (L.path i).sub

/-- The vertices of the linkage. -/
def verts (L : Linkage G n) : Finset V := Finset.univ.biUnion fun i => (L.path i).verts

/-- Two linkages of the same order are end-identical: every path of `Q` has the same ends (as an
unordered pair) as some path of `P`. -/
def EndIdentical (P Q : Linkage G n) : Prop :=
  ∀ j, ∃ i, s((Q.path j).s, (Q.path j).t) = s((P.path i).s, (P.path i).t)

end Linkage

/-! ### Separations and tangles -/

/-- `(A, B)` is a separation of `G`: `A ∪ B = V(G)` and every edge has both ends in `A` or both
ends in `B`. -/
def IsSeparation (G : SimpleGraph V) (A B : Finset V) : Prop :=
  A ∪ B = Finset.univ ∧ ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)

/-- The order `|A ∩ B|` of a separation. -/
def sepOrder (A B : Finset V) : ℕ := (A ∩ B).card

/-- `S_k(G)`: the separations of order less than `k`. -/
def SepLt (G : SimpleGraph V) (k : ℕ) : Set (Finset V × Finset V) :=
  {S | IsSeparation G S.1 S.2 ∧ sepOrder S.1 S.2 < k}

/-- `O` is an orientation of `S_k(G)`: `O ⊆ S_k(G)` and for every `(A, B) ∈ S_k(G)` exactly one of
`(A, B)` and `(B, A)` lies in `O`. -/
def IsOrientation (G : SimpleGraph V) (k : ℕ) (O : Set (Finset V × Finset V)) : Prop :=
  O ⊆ SepLt G k ∧ ∀ S ∈ SepLt G k, (S ∈ O ↔ (S.2, S.1) ∉ O)

/-- `G[A₁] ∪ G[A₂] ∪ G[A₃] = G`. -/
def ThreeSmallSidesCover (G : SimpleGraph V) (A₁ A₂ A₃ : Finset V) : Prop :=
  A₁ ∪ A₂ ∪ A₃ = Finset.univ ∧
    ∀ u v, G.Adj u v → (u ∈ A₁ ∧ v ∈ A₁) ∨ (u ∈ A₂ ∧ v ∈ A₂) ∨ (u ∈ A₃ ∧ v ∈ A₃)

/-- A tangle of order `k`: an orientation of `S_k(G)` no three of whose small sides cover `G`. -/
def IsTangle (G : SimpleGraph V) (k : ℕ) (T : Set (Finset V × Finset V)) : Prop :=
  IsOrientation G k T ∧
    ∀ S₁ ∈ T, ∀ S₂ ∈ T, ∀ S₃ ∈ T, ¬ ThreeSmallSidesCover G S₁.1 S₂.1 S₃.1

/-- `D` is a truncation of `T`: `D ⊆ T`. -/
def IsTruncation (D T : Set (Finset V × Finset V)) : Prop := D ⊆ T

/-- A minor-model `μ` of `H` in `G` is controlled by the set of separations `T`: no `(A, B) ∈ T` of
order less than `|V(H)|` has a branch set `μ(x) ⊆ A \ B`. -/
def ControlledBy {W : Type} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    (μ : H.Minor G) (T : Set (Finset V × Finset V)) : Prop :=
  ¬ ∃ S ∈ T, sepOrder S.1 S.2 < Fintype.card W ∧
      ∃ x : W, μ.branchSet x ⊆ ((S.1 \ S.2 : Finset V) : Set V)

/-- The tangle `T_μ` induced by a `K_t`-minor-model: the separations `(A, B) ∈ S_t(G)` whose
`μ`-majority side is `B`, i.e. `μ(u) ⊆ B \ A` for some `u`. -/
def tangleOfModel {t : ℕ} {G : SimpleGraph V} (μ : (SimpleGraph.completeGraph (Fin t)).Minor G) :
    Set (Finset V × Finset V) :=
  {S | S ∈ SepLt G t ∧ ∃ u : Fin t, μ.branchSet u ⊆ ((S.2 \ S.1 : Finset V) : Set V)}

/-! ### Meshes -/

/-- An `(n × m)`-mesh in `G` (`n, m ≥ 2`): horizontal paths `P₁, …, Pₙ` (pairwise disjoint),
vertical paths `Q₁, …, Q_m` (pairwise disjoint), every `Pᵢ ∩ Qⱼ` a (nonempty) path, every `Pᵢ` a
`V(Q₁)`-`V(Q_m)`-path meeting `Q₁, …, Q_m` in this order, and every `Qⱼ` a `V(P₁)`-`V(Pₙ)`-path
meeting `P₁, …, Pₙ` in this order. Indices are `0`-based. -/
structure Mesh (G : SimpleGraph V) (n m : ℕ) where
  /-- horizontal paths -/
  P : Fin n → GPath G
  /-- vertical paths -/
  Q : Fin m → GPath G
  two_le_n : 2 ≤ n
  two_le_m : 2 ≤ m
  P_disj : Pairwise fun i j => Disjoint (P i).verts (P j).verts
  Q_disj : Pairwise fun i j => Disjoint (Q i).verts (Q j).verts
  inter : ∀ i j, IsPathSub ((P i).sub ⊓ (Q j).sub)
  P_ends : ∀ i, (P i).s ∈ (Q ⟨0, by omega⟩).verts ∧ (P i).t ∈ (Q ⟨m - 1, by omega⟩).verts ∧
    (P i).InternallyDisjoint ((Q ⟨0, by omega⟩).verts ∪ (Q ⟨m - 1, by omega⟩).verts : Finset V)
  Q_ends : ∀ j, (Q j).s ∈ (P ⟨0, by omega⟩).verts ∧ (Q j).t ∈ (P ⟨n - 1, by omega⟩).verts ∧
    (Q j).InternallyDisjoint ((P ⟨0, by omega⟩).verts ∪ (P ⟨n - 1, by omega⟩).verts : Finset V)
  P_order : ∀ i (j j' : Fin m), j < j' → ∀ x ∈ (P i).verts ∩ (Q j).verts,
    ∀ y ∈ (P i).verts ∩ (Q j').verts, (P i).pos x < (P i).pos y
  Q_order : ∀ j (i i' : Fin n), i < i' → ∀ x ∈ (Q j).verts ∩ (P i).verts,
    ∀ y ∈ (Q j).verts ∩ (P i').verts, (Q j).pos x < (Q j).pos y

namespace Mesh

variable {G : SimpleGraph V} {n m : ℕ}

/-- The mesh as a subgraph of `G`. -/
def sub (M : Mesh G n m) : G.Subgraph := (⨆ i, (M.P i).sub) ⊔ ⨆ j, (M.Q j).sub

/-- The vertex set of the mesh. -/
def verts (M : Mesh G n m) : Finset V :=
  (Finset.univ.biUnion fun i => (M.P i).verts) ∪ Finset.univ.biUnion fun j => (M.Q j).verts

/-- The perimeter `P₁ ∪ Pₙ ∪ Q₁ ∪ Q_m` (a cycle). -/
def perimeter (M : Mesh G n m) : G.Subgraph :=
  (M.P ⟨0, by have := M.two_le_n; omega⟩).sub ⊔ (M.P ⟨n - 1, by have := M.two_le_n; omega⟩).sub ⊔
    (M.Q ⟨0, by have := M.two_le_m; omega⟩).sub ⊔ (M.Q ⟨m - 1, by have := M.two_le_m; omega⟩).sub

/-- `M'` is a submesh of `M`: every horizontal (vertical) path of `M'` is a subpath of a horizontal
(vertical) path of `M`. -/
def IsSubmeshOf {n' m' : ℕ} (M' : Mesh G n' m') (M : Mesh G n m) : Prop :=
  (∀ i, ∃ i', (M'.P i).sub ≤ (M.P i').sub) ∧ ∀ j, ∃ j', (M'.Q j).sub ≤ (M.Q j').sub

/-- The tangle `T_M` induced by an `r`-mesh: the separations `(A, B)` of order `< r` such that
`B \ A` contains the vertex set of a horizontal and of a vertical path of `M`. -/
def tangle {r : ℕ} (M : Mesh G r r) : Set (Finset V × Finset V) :=
  {S | S ∈ SepLt G r ∧ (∃ i, (M.P i).verts ⊆ S.2 \ S.1) ∧ ∃ j, (M.Q j).verts ⊆ S.2 \ S.1}

end Mesh

end GMSTFramework.LocalStructure



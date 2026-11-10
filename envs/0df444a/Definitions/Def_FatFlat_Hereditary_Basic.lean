-- Prove2me | Definitions.Def_FatFlat_Hereditary_Basic
-- name    : FatFlat_Hereditary_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:41:57.227578+00:00
-- url     : https://prove2.me/theorems/44d4dae3-b38a-40fc-a454-ef400e6a2014
-- title:
--   Graph classes, hereditary classes, balls, scattered and $(\alpha,Z)$-scattered sets, radius of an induced subgraph
-- statement:
--   Throughout, a **graph** is a finite simple undirected graph $G$ on a finite vertex type $V$, and $\mathrm{dist}_G$ is the graph distance with values in $\mathbb{N}\cup\{\infty\}$ (Lean's `G.edist`; $\infty$ between different components).
--
--   - A **graph class** $\mathcal C$ is a property of graphs: `C V G` says $G\in\mathcal C$.
--   - $\mathcal C$ is **hereditary** if $G\in\mathcal C$ and $H$ an induced subgraph of $G$ (an injective map $V(H)\to V(G)$ preserving and reflecting adjacency) imply $H\in\mathcal C$. In particular a hereditary class is closed under isomorphism.
--   - For $Z\subseteq V(G)$ and $\beta\in\mathbb N$, the **ball** is $\mathrm{Ball}_G(Z,\beta)=\{x : \mathrm{dist}_G(x,Z)\le\beta\}$, i.e. the vertices at distance at most $\beta$ from some $z\in Z$; $\mathrm{Ball}_G(\emptyset,\beta)=\emptyset$.
--   - $B\subseteq V(G)$ is **$\alpha$-scattered** if $\mathrm{dist}_G(a,b)>\alpha$ for all distinct $a,b\in B$.
--   - $B$ is **$(\alpha,Z)$-scattered** if $B- Z$ is $\alpha$-scattered in $G - Z=G[V\setminus Z]$: for all distinct $a,b\in B\setminus Z$, $\mathrm{dist}_{G-Z}(a,b)>\alpha$. Vertices of $B$ inside $Z$ are unconstrained.
--   - $G[S]$ has **radius at most $r$** if some $c\in S$ has $\mathrm{dist}_{G[S]}(c,v)\le r$ for every $v\in S$ (distance in the induced subgraph $G[S]$). This forces $S\neq\emptyset$ and $G[S]$ connected.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, §2.1 p. 7 (PDF 9), §2.2 p. 8 (PDF 10), p. 3 (PDF 5), Part I p. 11 (PDF 13). PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- A **graph class**: a property of finite simple graphs. A graph is a simple graph `G` on a
finite vertex type `V : Type`; `C V G` says that `G` belongs to the class.

Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, *Fatness and Flatness*,
arXiv:2607.21474, §2.1, p. 7, and Part I, p. 11 ("formally we treat all graphs as unweighted
graphs").

**Formalization Note.** Membership may a priori depend on the vertex type; isomorphism
invariance is part of `IsHereditary` below. -/
abbrev GraphClass : Type 1 := ∀ (V : Type) [Fintype V], SimpleGraph V → Prop

/-- A graph class is **hereditary** if it is closed under taking induced subgraphs: whenever
`G ∈ C` and `H` embeds into `G` as an induced subgraph (a Mathlib graph embedding `H ↪g G`,
an injective map that preserves and reflects adjacency), then `H ∈ C`. Since an isomorphism is
such an embedding, a hereditary class is closed under isomorphism. -/
def IsHereditary (C : GraphClass) : Prop :=
  ∀ (V W : Type) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
    C V G → Nonempty (H ↪g G) → C W H

/-- The **ball** `Ball_G(Z, β) = {x | dist_G(x, Z) ≤ β}` around a vertex set `Z`, with the
graph distance `G.edist` (which is `⊤` between different components). Since `ℕ∞` infima over
a nonempty set are attained, `dist_G(x, Z) ≤ β` iff some `z ∈ Z` has `dist_G(x, z) ≤ β`;
`Ball_G(∅, β) = ∅` (arXiv:2607.21474, §2.2, p. 8). -/
def ball {V : Type} (G : SimpleGraph V) (Z : Set V) (β : ℕ) : Set V :=
  {x | ∃ z ∈ Z, G.edist x z ≤ β}

/-- A vertex set `B` is **`α`-scattered** in `G` if `dist_G(a, b) > α` for all distinct
`a, b ∈ B` (arXiv:2607.21474, p. 3 and p. 8). Vertices in different components are at
distance `⊤ > α`. -/
def IsScattered {V : Type} (G : SimpleGraph V) (α : ℕ) (B : Set V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a ≠ b → (α : ℕ∞) < G.edist a b

/-- `B` is **`(α, Z)`-scattered** in `G` if `B − Z` is `α`-scattered in `G − Z`: for all
distinct `a, b ∈ B` outside `Z`, their distance in the graph `G − Z = G[V ∖ Z]` exceeds `α`.
Vertices of `B` inside `Z` are unconstrained (arXiv:2607.21474, p. 3 and p. 8). -/
def IsScatteredOff {V : Type} (G : SimpleGraph V) (α : ℕ) (Z B : Set V) : Prop :=
  ∀ a b : ↥Zᶜ, (a : V) ∈ B → (b : V) ∈ B → a ≠ b → (α : ℕ∞) < (G.induce Zᶜ).edist a b

/-- The vertex set `S` induces a subgraph `G[S]` of **radius at most `r`**: some `c ∈ S` is at
distance at most `r` in `G[S]` from every vertex of `S`. This forces `S` to be nonempty and
`G[S]` to be connected (arXiv:2607.21474, §2.1, p. 7: "`G[φ(v)]` has radius at most `r`"). -/
def RadiusLE {V : Type} (G : SimpleGraph V) (S : Set V) (r : ℕ) : Prop :=
  ∃ c : ↥S, ∀ v : ↥S, (G.induce S).edist c v ≤ r

end FatFlat.Hereditary



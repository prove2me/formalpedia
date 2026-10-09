-- Prove2me | Definitions.Def_OneTwoThree_Weighting_AuxNetwork
-- name    : OneTwoThree_Weighting_AuxNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:21.024707+00:00
-- url     : https://prove2.me/theorems/82bc2d97-770b-4f82-a2d6-e49e0f28d1f6
-- title:
--   p. 4 — maximum cuts, orientations of $F\subseteq E(S)\cup E(T)$, and the auxiliary network $G_{C,F,\sigma}$ of Lemma 4
-- statement:
--   Let $G=(V,E)$ be a finite simple graph.
--
--   1. **Cuts.** For $S\subseteq V$ write $T=V\setminus S$; the cut $C=(S,T)$ has the cut edges $E(S,T)$, the edges with one end in $S$ and one in $T$. Its size is $|E(S,T)|$.
--   2. **Maximum cuts.** $C=(S,T)$ is a *maximum cut* of $G$ if $|E(S,T)|\ge|E(S',V\setminus S')|$ for every $S'\subseteq V$.
--   3. **Orientations of edges inside the sides.** Let $F\subseteq E(S)\cup E(T)$ be a set of edges each having both ends in $S$ or both ends in $T$. An *orientation* $\sigma$ of $F$ chooses for each edge $\{u,v\}\in F$ exactly one of the ordered pairs $(u,v)$, $(v,u)$. Equivalently, $\sigma$ is a set of ordered pairs $(u,v)$ such that each $\{u,v\}$ is an edge of $G$ with both ends on the same side of the cut, and no edge appears in $\sigma$ in both orientations; then $F=\{\{u,v\}:(u,v)\in\sigma\}$ and $|F|=|\sigma|$.
--   4. **The network $G_{C,F,\sigma}$.** Its nodes are the vertices of $G$ together with a source $s$ and a sink $t$. Its arcs are: for each cut edge $\{u,v\}\in E(S,T)$ the two arcs $(u,v)$ and $(v,u)$; and for each $(u,v)\in\sigma$ one arc $(s,u)$ and one arc $(v,t)$. Several oriented edges with the same tail (or head) give parallel arcs $(s,u)$ (or $(v,t)$). No arc $(u,v)$ is inserted for $(u,v)\in\sigma$. All arcs have capacity $1$.
--
--   These are the objects of Lemma 4 (p. 4), which the proof of Lemma 3 uses to reroute weights along edge-disjoint paths.
--
--   **Formalization Note** A cut is given by the set $S$ (a `Finset V`); its size counts ordered pairs $(u,v)$ with $G$-adjacent $u\in S$, $v\notin S$, which counts each cut edge exactly once. The orientation $\sigma$ is a `Finset (V × V)` with the map $(u,v)\mapsto\{u,v\}$ injective on it; $F$ may be empty and may contain edges of both sides. The arc type is the disjoint union of the ordered cut pairs, one copy of $\sigma$ (the arcs $(s,u)$) and another copy of $\sigma$ (the arcs $(v,t)$), with explicit tail and head maps into the node type `Node V`.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 4, Lemma 4 (maximum cut C = (S,T), F ⊆ E(S) ∪ E(T), orientation σ, the network G_{C,F,σ}, items (i)–(iii)); p. 2, §2 notation (E(W), E(S,T))

import Mathlib

namespace OneTwoThree.Weighting

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges of the cut `(S, V ∖ S)` of `G`, i.e. `|E(S, V ∖ S)|`; each cut edge is
counted once, as the ordered pair `(u, v)` with `u ∈ S` and `v ∉ S`. -/
def cutSize (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  #(univ.filter fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S)

/-- `C = (S, V ∖ S)` is a maximum cut of `G`: no cut of `G` has more cut edges. -/
def IsMaxCut (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ S' : Finset V, cutSize G S' ≤ cutSize G S

/-- `σ` is an orientation of an edge set `F ⊆ E(S) ∪ E(V ∖ S)`: every pair `(u, v) ∈ σ` is an edge
of `G` with both ends on the same side of the cut, and no edge is oriented twice (the map
`(u, v) ↦ {u, v}` is injective on `σ`). The oriented edge set is `F = {{u, v} : (u, v) ∈ σ}`, so
`|F| = |σ|`. -/
def IsSideOrientation (G : SimpleGraph V) (S : Finset V) (σ : Finset (V × V)) : Prop :=
  (∀ p ∈ σ, G.Adj p.1 p.2 ∧ (p.1 ∈ S ↔ p.2 ∈ S)) ∧
    Set.InjOn (fun p : V × V => s(p.1, p.2)) (σ : Set (V × V))

/-- Nodes of the network `G_{C,F,σ}`: the vertices of `G`, a source `s` and a sink `t`. -/
inductive Node (V : Type*) where
  | src : Node V
  | snk : Node V
  | vert : V → Node V
  deriving DecidableEq

/-- Arcs of `G_{C,F,σ}` (Lemma 4, p. 4): (ii) for each cut edge `{u, v} ∈ E(S, V ∖ S)` the two arcs
`(u, v)` and `(v, u)`, indexed by the ordered adjacent pairs with ends on different sides; (iii) for
each `(u, v) ∈ σ` one arc `(s, u)` and one arc `(v, t)`, indexed by `σ` itself (so parallel arcs
occur when several oriented edges share a tail or a head). -/
def AuxArc (G : SimpleGraph V) (S : Finset V) (σ : Finset (V × V)) : Type _ :=
  {d : V × V // G.Adj d.1 d.2 ∧ (d.1 ∈ S ↔ d.2 ∉ S)} ⊕ σ ⊕ σ

instance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (σ : Finset (V × V)) :
    Fintype (AuxArc G S σ) := by
  unfold AuxArc; infer_instance

/-- Tail of an arc of `G_{C,F,σ}`. -/
def auxTail (G : SimpleGraph V) (S : Finset V) (σ : Finset (V × V)) : AuxArc G S σ → Node V
  | Sum.inl d => Node.vert d.1.1
  | Sum.inr (Sum.inl _) => Node.src
  | Sum.inr (Sum.inr p) => Node.vert p.1.2

/-- Head of an arc of `G_{C,F,σ}`. -/
def auxHead (G : SimpleGraph V) (S : Finset V) (σ : Finset (V × V)) : AuxArc G S σ → Node V
  | Sum.inl d => Node.vert d.1.2
  | Sum.inr (Sum.inl p) => Node.vert p.1.1
  | Sum.inr (Sum.inr _) => Node.snk

end OneTwoThree.Weighting



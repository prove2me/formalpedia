-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_Supplement_ForestOfCopies
-- name    : RamseyDisambig_Spherical_Supplement_ForestOfCopies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:23:50.664416+00:00
-- url     : https://prove2.me/theorems/0d646208-0ae6-4735-aed0-d8c8639c4fb2
-- title:
--   Copies, forests of copies and the graph Γ(𝓕)
-- statement:
--   Let $F$ and $H$ be graphs. A **copy** of $F$ in $H$ is a subgraph $Q$ of $H$ isomorphic to $F$, with vertex set $V(Q)$ and its own edge set; copies need not be induced. A finite family $\mathcal F$ of copies of $F$ in $H$ is a **forest of copies** if its members can be ordered as $F_1,\dots,F_m$ so that for every $j$ the set
--   $$V(F_j)\cap\bigcup_{i<j}V(F_i)$$
--   is empty, a single vertex, or the two ends $\{u,v\}$ of an edge $uv$ of $H$ that belongs both to $F_j$ and to some earlier $F_i$.
--
--   For a nonempty forest $\mathcal F$, the graph $\Gamma(\mathcal F)$ has vertex set $\bigcup_{Q\in\mathcal F}V(Q)$, and two distinct vertices are adjacent if and only if they belong to a common member of $\mathcal F$.
--
--   These are the objects of the localization lemma (Lemma 17) used in the proofs of Theorems 3 and 5.
--
--   **Formalization Note** Families are `Finset`s of Mathlib subgraphs `H.Subgraph`; an ordering is a bijection `Fin m ≃ 𝓕`. $\Gamma(\mathcal F)$ is defined as a graph on the whole vertex type of $H$ in which vertices outside $\bigcup V(Q)$ are isolated; statements about its cliques restrict to subsets of the union.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), §3.1, p. 15; §3.2, p. 16 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Mathlib

set_option autoImplicit false

noncomputable section

namespace RamseyDisambig.Spherical.Supplement

/-- A copy of `F` in `H` (p. 15): a subgraph `Q` of `H` isomorphic to `F`. Its vertex set is
`Q.verts` and its edges are its own adjacencies `Q.Adj`. Copies need not be induced. -/
def IsGraphCopy {V W : Type*} {H : SimpleGraph V} (F : SimpleGraph W) (Q : H.Subgraph) : Prop :=
  Nonempty (F ≃g Q.coe)

/-- The vertices of the members of an ordered family that come before position `j`:
`⋃_{i<j} V(F_i)`. -/
def earlierVerts {V : Type*} {H : SimpleGraph V} {m : ℕ} (Fs : Fin m → H.Subgraph)
    (j : Fin m) : Set V :=
  ⋃ (i : Fin m) (_ : i < j), (Fs i).verts

/-- A forest of copies of `F` in `H` (p. 15): a finite family `𝓕` of copies of `F` in `H`
whose members can be ordered `F_1, …, F_m` (a bijection `Fin m ≃ 𝓕`) so that for every `j`
the set `V(F_j) ∩ ⋃_{i<j} V(F_i)` is empty, a single vertex, or the two ends `{u, v}` of an
edge of `H` that belongs both to `F_j` and to some earlier `F_i`. -/
def IsForestOfCopies {V W : Type*} (F : SimpleGraph W) (H : SimpleGraph V)
    (𝓕 : Finset H.Subgraph) : Prop :=
  (∀ Q ∈ 𝓕, IsGraphCopy F Q) ∧
  ∃ (m : ℕ) (σ : Fin m ≃ 𝓕), ∀ j : Fin m,
    (σ j).1.verts ∩ earlierVerts (fun i => (σ i).1) j = ∅ ∨
    (∃ v : V, (σ j).1.verts ∩ earlierVerts (fun i => (σ i).1) j = {v}) ∨
    (∃ u v : V, (σ j).1.verts ∩ earlierVerts (fun i => (σ i).1) j = {u, v} ∧
      (σ j).1.Adj u v ∧ ∃ i : Fin m, i < j ∧ (σ i).1.Adj u v)

/-- `⋃_{Q ∈ 𝓕} V(Q)`, the vertex set of `Γ(𝓕)` (p. 16). -/
def copyUnion {V : Type*} {H : SimpleGraph V} (𝓕 : Finset H.Subgraph) : Set V :=
  ⋃ Q ∈ 𝓕, Q.verts

/-- `Γ(𝓕)` (p. 16): two distinct vertices are adjacent iff they belong to a common member of
`𝓕`. Stated on all of `V`; vertices outside `copyUnion 𝓕` are isolated and are not vertices of
the paper's `Γ(𝓕)`, so statements about its cliques restrict to `copyUnion 𝓕`. -/
def copyGraph {V : Type*} {H : SimpleGraph V} (𝓕 : Finset H.Subgraph) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ Q ∈ 𝓕, u ∈ Q.verts ∧ v ∈ Q.verts
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ hQ => ⟨hQ.1, hQ.2.2, hQ.2.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end RamseyDisambig.Spherical.Supplement



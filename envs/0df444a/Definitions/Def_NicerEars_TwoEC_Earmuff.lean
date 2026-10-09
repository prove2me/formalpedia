-- Prove2me | Definitions.Def_NicerEars_TwoEC_Earmuff
-- name    : NicerEars_TwoEC_Earmuff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:58.807449+00:00
-- url     : https://prove2.me/theorems/69de103f-7a15-4b8e-9f32-eccd89ef20dc
-- title:
--   Definitions 9 and 12, Theorems 19–20 — eardrums, 𝒫_f, earmuffs, µ(G,M), L_µ(G,M), L_ϕ(G), decompositions containing a maximum earmuff
-- statement:
--   An **eardrum** $M$ in $G$ (Definition 9) is the set of components of an induced subgraph in which every vertex has degree at most 1: a family of pairwise disjoint vertex sets of size 1 or 2, each 2-element set an adjacent pair, with no edge between vertices of different members.
--
--   For $f\in M$, $\mathcal P_f$ is the set of paths $P$ in $G$ with $\mathrm{in}(P)=f$ (Definition 12). An **earmuff** for $M$ is a choice of $F\subseteq M$ and paths $P_f\in\mathcal P_f$ ($f\in F$) such that $\bigl(V(G),\bigcup_{f\in F}E(P_f)\bigr)$ is a forest; its size is $|F|$, and $\mu(G,M)$ is the maximum size of an earmuff. With these,
--
--   $$L_\mu(G,M)=|V(G)|-1+|M|-\mu(G,M),\qquad L_\varphi(G)=|V(G)|+\varphi(G)-1 .$$
--
--   A nice ear-decomposition **contains a maximum earmuff** for the eardrum $M$ associated with it and $T$ if, for some $F\subseteq M$ with $|F|=\mu(G,M)$, the clean ears with internal vertex set in $F$ form an earmuff.
--
--   These are the quantities of the lower bounds (Theorem 19, Corollary 21) and of the construction of Theorem 24.
--
--   **Formalization Note** A forest is an edge set in which every edge is a bridge, so two parallel edges form a circuit. $\mu(G,M)$ is a supremum of natural numbers over a set that contains $0$ (the empty earmuff) and is bounded by $|M|$, hence a maximum. $L_\mu$ and $L_\varphi$ are integers.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 8 (Definition 9, eardrum), p. 11 (Definition 12), p. 16 (Theorems 19 and 20, L_ϕ and L_µ), p. 18 (Lemma 23, Theorem 24)

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Ears

namespace NicerEars.TwoEC

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Definition 9 (p. 8): M is an eardrum in G: the set of components of an induced subgraph in
which every vertex has degree at most 1. Its members are pairwise disjoint sets of one or two
vertices; a two-element member is an adjacent pair; vertices of different members are
non-adjacent. Adjacency is that of the underlying simple graph (multiplicities ignored). -/
def IsEardrum (G : Graph V E) (M : Finset (Finset V)) : Prop :=
  (∀ f ∈ M, #f = 1 ∨ #f = 2) ∧
  (∀ f ∈ M, ∀ g ∈ M, f ≠ g → Disjoint f g) ∧
  (∀ f ∈ M, ∀ u ∈ f, ∀ w ∈ f, u ≠ w → (G.spanGraph univ).Adj u w) ∧
  (∀ f ∈ M, ∀ g ∈ M, f ≠ g → ∀ u ∈ f, ∀ w ∈ g, ¬ (G.spanGraph univ).Adj u w)

/-- Definition 12 (p. 11): 𝒫_f, the paths P in G with in(P) = f. -/
def PathsThrough (G : Graph V E) (f : Finset V) : Set (Ear G) :=
  {P | P.IsOpen ∧ P.inner = f}

/-- An edge set S ⊆ E(G) is a forest: every edge of S is a bridge of (V(G), S), i.e. its ends are
not connected in (V(G), S minus that edge). Parallel edges in S form a circuit. -/
def IsForest (G : Graph V E) (S : Finset E) : Prop :=
  ∀ e ∈ S, ∀ u v, G.ends e = s(u, v) → ¬ (G.spanGraph (S.erase e)).Reachable u v

/-- Definition 12 (p. 11): an earmuff for M in G: a subset F ⊆ M and paths P_f ∈ 𝒫_f (f ∈ F)
such that (V(G), ⋃_{f ∈ F} E(P_f)) is a forest. Its size is |F|. -/
def IsEarmuff (G : Graph V E) (M : Finset (Finset V)) (F : Finset (Finset V)) (P : F → Ear G) :
    Prop :=
  F ⊆ M ∧ (∀ f : F, P f ∈ PathsThrough G f) ∧
  IsForest G ((univ : Finset F).biUnion (fun f => (P f).edges))

/-- Definition 12 (p. 11): µ(G, M), the maximum size of an earmuff for M in G. The set of sizes
contains 0 (F = ∅) and is bounded by |M|, so this supremum is attained. -/
noncomputable def mu (G : Graph V E) (M : Finset (Finset V)) : ℕ :=
  sSup {n | ∃ (F : Finset (Finset V)) (P : F → Ear G), IsEarmuff G M F P ∧ #F = n}

/-- Theorem 20 (p. 16): L_µ(G, M) := |V(G)| − 1 + |M| − µ(G, M). -/
noncomputable def Lmu (G : Graph V E) (M : Finset (Finset V)) : ℤ :=
  (Fintype.card V : ℤ) - 1 + #M - mu G M

/-- Theorem 19 (p. 16): L_ϕ(G) := |V(G)| + ϕ(G) − 1. -/
noncomputable def Lphi (G : Graph V E) : ℤ :=
  (Fintype.card V : ℤ) + G.phi - 1

/-- Lemma 23 / Theorem 24 (p. 18): the nice ear-decomposition D contains a maximum earmuff for
the eardrum M associated with it and T: for some F ⊆ M with |F| = µ(G, M), the clean ears whose
internal vertex sets lie in F form an earmuff. -/
def EarDecomposition.ContainsMaxEarmuff {G : Graph V E} (D : EarDecomposition G)
    (T : Finset V) : Prop :=
  ∃ (F : Finset (Finset V)) (P : F → Ear G),
    IsEarmuff G (D.eardrumOf T) F P ∧ #F = mu G (D.eardrumOf T) ∧
    ∀ f : F, ∃ i, D.IsClean T i ∧ (D.ear i).inner = f ∧ P f = D.ear i

end NicerEars.TwoEC



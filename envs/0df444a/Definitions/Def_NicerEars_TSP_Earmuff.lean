-- Prove2me | Definitions.Def_NicerEars_TSP_Earmuff
-- name    : NicerEars_TSP_Earmuff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:38.088919+00:00
-- url     : https://prove2.me/theorems/c3fcf8ac-b352-4de7-8d41-02322a567787
-- title:
--   Definitions 9, 12 and pp. 16, 21 — eardrums, 𝒫_f, earmuffs, µ(G, M), L_µ, L_ϕ, Λ, and a maximum earmuff contained in an ear-decomposition
-- statement:
--   This file fixes the earmuff objects of §3–§5 of Sebő and Vygen's paper.
--
--   1. **Eardrums (Definition 9).** An *eardrum* in $G$ is the set $M$ of components of an induced subgraph in which every vertex has degree at most 1: the sets of $M$ are pairwise disjoint, each has one or two elements, the two elements of a two-element set are adjacent, and vertices of different sets are non-adjacent.
--   2. **$\mathcal P_f$ (Definition 12).** For $f\in M$, $\mathcal P_f$ is the set of paths $P$ in $G$ with $\mathrm{in}(P)=f$.
--   3. **Earmuffs (Definition 12).** An *earmuff* for $M$ in $G$ is a set of paths $\{P_f: f\in F\}$ with $F\subseteq M$ and $P_f\in\mathcal P_f$ such that $\big(V(G),\bigcup_{f\in F}E(P_f)\big)$ is a forest; its size is $|F|$, and $\mu(G,M)$ is the maximum size of an earmuff.
--   4. **Lower-bound quantities.**
--   $$L_\mu(G,M):=|V(G)|-1+|M|-\mu(G,M)\quad\text{(Theorem 20, p. 16)},\qquad L_\varphi(G):=|V(G)|+\varphi(G)-1\quad\text{(Theorem 19, p. 16)},$$
--   $$\Lambda(G,M):=\tfrac23 L_\mu(G,M)+\tfrac13 L_\varphi(G)\quad\text{(proof of Theorem 29, p. 21)}.$$
--   5. **Containing a maximum earmuff (Lemma 23).** A nice ear-decomposition *contains a maximum earmuff* for the eardrum $M$ associated with it and $T$ if, for some $F\subseteq M$ with $|F|=\mu(G,M)$, the clean ears whose internal vertex sets lie in $F$ form an earmuff.
--
--   $\Lambda(G,M)$ is the lower bound on $\mathrm{LP}(G)$ that the 7/5 analysis balances against the number of pendant ears.
--
--   **Formalization Note.** Degree in Definition 9 is read in the underlying simple graph (adjacency): with parallel edges a literal degree count would exclude a 3-ear whose middle edge has a parallel 1-ear, which the paper clearly regards as part of an eardrum. A forest is an edge set in which every edge is a bridge, so two parallel edges form a circuit. $\mu(G,M)$ is the supremum of a set of natural numbers that contains $0$ (the empty earmuff) and is bounded by $|M|$, so it is a true maximum. $L_\mu$ and $L_\varphi$ are integers and $\Lambda$ is a real number.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 8 (Definition 9, eardrum), p. 11 (Definition 12), p. 16 (Theorems 19, 20: L_ϕ, L_µ), p. 18 (Lemma 23), p. 21 (proof of Theorem 29: Λ)

import Mathlib
import Definitions.Def_NicerEars_TSP_Ears

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Definition 9, p. 8: M is an eardrum in G, i.e. the set of components of an induced subgraph
in which every vertex has degree at most 1: the sets of M have one or two elements, the two
elements of a 2-element set are adjacent, the sets are pairwise disjoint, and vertices of different
sets are non-adjacent. (Degree is read in the underlying simple graph, i.e. as adjacency.) -/
def Graph.IsEardrum (G : Graph V E) (M : Finset (Finset V)) : Prop :=
  (∀ f ∈ M, #f = 1 ∨ #f = 2) ∧
  (∀ f ∈ M, ∀ u ∈ f, ∀ w ∈ f, u ≠ w → (G.spanGraph univ).Adj u w) ∧
  (∀ f ∈ M, ∀ g ∈ M, f ≠ g → Disjoint f g) ∧
  (∀ f ∈ M, ∀ g ∈ M, f ≠ g → ∀ u ∈ f, ∀ w ∈ g, ¬ (G.spanGraph univ).Adj u w)

/-- Definition 12, p. 11: 𝒫_f, the set of paths P in G with in(P) = f. -/
def Graph.PathsThrough (G : Graph V E) (f : Finset V) : Set (Ear G) :=
  {P | P.IsOpen ∧ P.inner = f}

/-- (V(G), S) is a forest: every edge of S is a bridge of (V(G), S). Two parallel edges in S
form a circuit, so they are excluded. -/
def Graph.IsForest (G : Graph V E) (S : Finset E) : Prop :=
  ∀ e ∈ S, ∀ u v, G.ends e = s(u, v) → ¬ (G.spanGraph (S.erase e)).Reachable u v

/-- Definition 12, p. 11: an earmuff for M in G: a set of paths {P_f : f ∈ F}, F ⊆ M,
P_f ∈ 𝒫_f, such that (V(G), ⋃_{f ∈ F} E(P_f)) is a forest. Its size is |F|. -/
def Graph.IsEarmuff (G : Graph V E) (M F : Finset (Finset V)) (P : F → Ear G) : Prop :=
  F ⊆ M ∧ (∀ f : F, P f ∈ G.PathsThrough f) ∧
    G.IsForest ((univ : Finset F).biUnion (fun f => (P f).edges))

/-- Definition 12, p. 11: µ(G, M), the maximum size of an earmuff for M in G. The set is nonempty
(the empty earmuff) and bounded by |M|. -/
noncomputable def Graph.mu (G : Graph V E) (M : Finset (Finset V)) : ℕ :=
  sSup {n | ∃ F : Finset (Finset V), ∃ P : F → Ear G, G.IsEarmuff M F P ∧ #F = n}

/-- Theorem 20, p. 16: L_µ(G, M) := |V(G)| − 1 + |M| − µ(G, M). -/
noncomputable def Graph.Lmu (G : Graph V E) (M : Finset (Finset V)) : ℤ :=
  (Fintype.card V : ℤ) - 1 + #M - G.mu M

/-- Theorem 19, p. 16: L_ϕ(G) := |V(G)| + ϕ(G) − 1. -/
noncomputable def Graph.Lphi (G : Graph V E) : ℤ :=
  (Fintype.card V : ℤ) + G.phi - 1

/-- Proof of Theorem 29, p. 21: Λ(G, M) := ⅔ L_µ(G, M) + ⅓ L_ϕ(G). -/
noncomputable def Graph.Lambda (G : Graph V E) (M : Finset (Finset V)) : ℝ :=
  2 / 3 * (G.Lmu M : ℝ) + 1 / 3 * (G.Lphi : ℝ)

/-- Lemma 23, Theorem 24: the ear-decomposition contains a maximum earmuff for the eardrum M
associated with it and T: for some F ⊆ M with |F| = µ(G, M), the clean ears whose internal vertex
sets lie in F form an earmuff for M. -/
def EarDecomposition.ContainsMaxEarmuff {G : Graph V E} (D : EarDecomposition G)
    (T : Finset V) : Prop :=
  ∃ F ⊆ D.eardrumOf T, ∃ P : F → Ear G,
    G.IsEarmuff (D.eardrumOf T) F P ∧ #F = G.mu (D.eardrumOf T) ∧
    ∀ f : F, ∃ i, D.IsClean T i ∧ P f = D.ear i

end NicerEars.TSP



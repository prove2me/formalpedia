-- Prove2me | Definitions.Def_BipDijoin_IsDicut
-- name    : BipDijoin_IsDicut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:29.572181+00:00
-- url     : https://prove2.me/theorems/5661d526-8546-4fd6-ae51-f567e4d4b2f3
-- title:
--   Dicuts, dijoins, $\gamma(G)$ and dicut packings
-- statement:
--   Let $D$ be the digraph of a bipartite multigraph, every arc pointing from $L$ to $R$. For $X\subseteq V$ write $\delta^+(X)$ and $\delta^-(X)$ for the arcs leaving and entering $X$.
--
--   1. A **dicut** is a nonempty arc set $C$ such that for some $X\subseteq V$ either $C=\delta^+(X)$ and $\delta^-(X)=\emptyset$, or $C=\delta^-(X)$ and $\delta^+(X)=\emptyset$.
--   2. A **dijoin** is a set of arcs meeting every dicut; a **minimum dijoin** is one of smallest cardinality, and $\gamma(G)$ is that cardinality (the whole arc set is a dijoin, so $\gamma(G)$ is attained).
--   3. A **dicut packing** is a family of pairwise edge-disjoint dicuts; a **maximum dicut packing** is one with the largest number of members.
--
--   By the Lucchesi–Younger theorem the minimum size of a dijoin equals the maximum size of a dicut packing; Theorem 1.1 computes both optima.
--
--   **Formalization Note** Dijoins are defined by "meets every dicut", the paper's definition; the equivalent description by contraction to a strongly connected digraph applies to weakly connected digraphs. A packing is a list of arc sets; pairwise disjointness of nonempty sets makes its members distinct.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), §2.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph

set_option autoImplicit false

namespace BipDijoin

/-!
# Dicuts, dijoins and dicut packings

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), §2.1, p.2 (PDF p.4):
"For X ⊆ V(D), let δ⁺_D(X) and δ⁻_D(X) denote the arcs leaving and entering X, respectively. …
A nonempty set C ⊆ A is a dicut if, for some X ⊆ V(D), either C = δ⁺_D(X) and δ⁻_D(X) = ∅
(or) C = δ⁻_D(X) and δ⁺_D(X) = ∅. A set B ⊆ A is a dijoin if it meets every dicut."
§1, p.1 (PDF p.3): "the minimum dijoin size equals the maximum number of pairwise edge-disjoint
dicuts; such a maximum family is a maximum dicut packing."

**Formalization Note.**
* Arcs are edge identities; `e` is the arc `tl e → hd e`. A dicut is a set of identities, so a
  dicut contains all or none of a class of parallel arcs.
* A dijoin is defined as "meets every dicut" (the paper's definition), not through contraction;
  the two agree on weakly connected digraphs.
* `gamma G` is the minimum dijoin size `γ(G)` (Claim 3.1, p.4); `E` itself is always a dijoin, so
  the infimum is attained.
* A dicut packing is a list of dicuts that are pairwise disjoint; since dicuts are nonempty, its
  members are distinct, and its length is the number of dicuts.
-/

namespace BipGraph

variable (G : BipGraph)

/-- `δ⁺(X)`: the arcs leaving `X`. -/
def outArcs (X : Finset ℕ) : Finset ℕ := G.E.filter (fun e => G.tl e ∈ X ∧ G.hd e ∉ X)

/-- `δ⁻(X)`: the arcs entering `X`. -/
def inArcs (X : Finset ℕ) : Finset ℕ := G.E.filter (fun e => G.tl e ∉ X ∧ G.hd e ∈ X)

/-- A **dicut**: a nonempty arc set `C` with `C = δ⁺(X)`, `δ⁻(X) = ∅` or `C = δ⁻(X)`, `δ⁺(X) = ∅`
for some `X ⊆ V` (§2.1, p.2). -/
def IsDicut (C : Finset ℕ) : Prop :=
  C.Nonempty ∧ ∃ X ⊆ G.V,
    (C = G.outArcs X ∧ G.inArcs X = ∅) ∨ (C = G.inArcs X ∧ G.outArcs X = ∅)

/-- A **dijoin**: a set of arcs meeting every dicut (§2.1, p.2). -/
def IsDijoin (B : Finset ℕ) : Prop := B ⊆ G.E ∧ ∀ C, G.IsDicut C → (B ∩ C).Nonempty

/-- A **minimum dijoin**: a dijoin of smallest cardinality. -/
def IsMinDijoin (B : Finset ℕ) : Prop := G.IsDijoin B ∧ ∀ B', G.IsDijoin B' → B.card ≤ B'.card

/-- `γ(G)`, the minimum size of a dijoin. -/
noncomputable def gamma : ℕ := sInf {k | ∃ B, G.IsDijoin B ∧ B.card = k}

/-- A **dicut packing**: a family of pairwise edge-disjoint dicuts. -/
def IsDicutPacking (F : List (Finset ℕ)) : Prop :=
  (∀ C ∈ F, G.IsDicut C) ∧ F.Pairwise Disjoint

/-- A **maximum dicut packing**: a dicut packing with the largest number of members. -/
def IsMaxDicutPacking (F : List (Finset ℕ)) : Prop :=
  G.IsDicutPacking F ∧ ∀ F', G.IsDicutPacking F' → F'.length ≤ F.length

end BipGraph

end BipDijoin



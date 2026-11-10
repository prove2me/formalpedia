-- Prove2me | Definitions.Def_BipDijoin_IsPartialDecomp
-- name    : BipDijoin_IsPartialDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:48:07.155897+00:00
-- url     : https://prove2.me/theorems/cd0c3c86-2832-4514-a70f-4c551a7a7b59
-- title:
--   Bipartite end decompositions: maximum, relaxed and partial (Definitions 2.2, 3.2)
-- statement:
--   An **end decomposition** of $H^0=G$ (Definition 2.2) is a sequence $\big((H^0,M^0,U^0),\dots,(H^k,M^k,U^k)\big)$ such that for every $i<k$:
--
--   1. $M^i$ is a maximum matching of $H^i$;
--   2. $U^i$ is a nontrivial source or sink SCC of the alternating digraph $H^i_{M^i}$;
--   3. $H^{i+1}=H^i/U^i$;
--
--   and the terminal graph $H^k$ has exactly one vertex. A **relaxed** end decomposition (Definition 3.2) only asks that each $M^i$ be a matching of $H^i$. A **partial** (relaxed) end decomposition is the same sequence ending at a graph $H$ that need not have one vertex. In each step $P^i=M^i\cap E(H^i[U^i])$ is a perfect matching of $U^i$.
--
--   The decomposition is recorded as the list of triples $(s_i,U^i,P^i)$, where $s_i$ says whether $U^i$ is a source end (its contracted vertex placed on $L$) or a sink end (placed on $R$). The graphs $H^i$ are recovered by contracting $U^0,U^1,\dots$ in turn, the $i$-th contracted vertex receiving the fresh name $N_0+i$, and the matchings $M^i$ are required to exist. The module also defines $B=\bigcup_i P^i$, the dijoin of Algorithm 5.
--
--   **Formalization Note** Contraction keeps edge identities, so each $P^i$ is a set of edges of $G$. Representatives must be fresh ($N_0+i\notin V(H^i)$).
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Definition 2.2, p.3 (PDF p.5); Definition 3.2, p.4 (PDF p.6); Algorithm 5, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsStrongEnd

set_option autoImplicit false

namespace BipDijoin

/-!
# Bipartite end decompositions, relaxed and partial

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6).
Definition 2.2, p.3 (PDF p.5): "An end-decomposition of H⁰ = G is a sequence
ℰ = ((H⁰, M⁰, U⁰), (H¹, M¹, U¹), …, (Hᵏ, Mᵏ, Uᵏ)) such that, for every i < k,
(i) Mⁱ is a maximum matching of Hⁱ; (ii) Uⁱ is a nontrivial source or sink SCC of Hⁱ_{Mⁱ}; and
(iii) Hⁱ⁺¹ = Hⁱ/Uⁱ. The terminal graph Hᵏ consists of one vertex, and Mᵏ = Uᵏ = ∅. In particular,
Pⁱ = Mⁱ ∩ E(Hⁱ[Uⁱ]) is a perfect matching of each recorded strong end Uⁱ."
Definition 3.2, p.4 (PDF p.6): "A relaxed bipartite end-decomposition is defined as in
Definition 2.2, except that condition (i) requires only that Mⁱ is a matching of Hⁱ, not
necessarily maximum."
A *partial* (relaxed) end decomposition (Lemmas 4.3, 4.4, Theorems 3.5, 6.4) is the same sequence
ending at a graph `H` that need not have one vertex.

**Formalization Note.**
* A decomposition is recorded as a list of records `(s, Uⁱ, Pⁱ)`; the graphs `Hⁱ` are recovered
  by replaying the contractions from `G`, and the matching `Mⁱ` is asserted to exist. Recording
  `Pⁱ` loses nothing: the dijoin and the dicut packing of Algorithm 5 (p.45) use only `Uⁱ`,
  `Pⁱ` and `Hⁱ`.
* The `i`-th representative (counting from `0`) is the vertex `N₀ + i`, which must be fresh
  (`N₀ + i ∉ V(Hⁱ)`). A source end's representative is left (`s = true`), a sink end's is
  right (`s = false`) ("Contracting a source (sink) strong end produces a source (sink)
  vertex", p.3).
* `maximum = true` is Definition 2.2 (each `Mⁱ` maximum), `maximum = false` Definition 3.2.
* Contraction keeps edge identities, so each `Pⁱ` is a set of edges of the input `G`.
-/

/-- A record of one contraction: the side `left` of the representative (`true` for a source end,
`false` for a sink end), the strong end `U` and its internal matching `P`. -/
structure Rec where
  /-- `true`: `U` is a source end (representative on the left); `false`: a sink end. -/
  left : Bool
  /-- The contracted strong end `Uⁱ` (vertices of `Hⁱ`). -/
  U : Finset ℕ
  /-- `Pⁱ = Mⁱ ∩ E(Hⁱ[Uⁱ])`. -/
  P : Finset ℕ

/-- One valid step of an end decomposition at the graph `G` with fresh representative `x`: some
matching `M` of `G` (maximum if `maximum`) has `r.U` as a nontrivial source SCC (`r.left`) or sink
SCC (`¬ r.left`) of `G_M`, and `r.P = M ∩ E(G[r.U])`. -/
def StepOK (maximum : Bool) (G : BipGraph) (x : ℕ) (r : Rec) : Prop :=
  x ∉ G.V ∧ 2 ≤ r.U.card ∧ ∃ M, G.IsMatching M ∧ (maximum = true → G.IsMaxMatching M) ∧
    (r.left = true → IsSourceSCC (G.altArc M) G.V r.U) ∧
    (r.left = false → IsSinkSCC (G.altArc M) G.V r.U) ∧
    r.P = M ∩ (G.induced r.U).E

/-- Replaying records from `G`, the `i`-th record contracting to `N₀ + i`, is a valid partial
decomposition ending at `H`. -/
def IsPartialDecompFrom (maximum : Bool) (N₀ : ℕ) : ℕ → BipGraph → List Rec → BipGraph → Prop
  | _, G, [], H => H = G
  | i, G, r :: rs, H =>
      StepOK maximum G (N₀ + i) r ∧
        IsPartialDecompFrom maximum N₀ (i + 1) (G.contract r.U (N₀ + i) r.left) rs H

/-- A **partial** (relaxed, if `maximum = false`) **bipartite end decomposition** of `G` ending at
`H`, with representatives `N₀, N₀ + 1, …`. -/
def IsPartialDecomp (maximum : Bool) (G : BipGraph) (N₀ : ℕ) (recs : List Rec) (H : BipGraph) :
    Prop :=
  IsPartialDecompFrom maximum N₀ 0 G recs H

/-- A (relaxed, if `maximum = false`) **bipartite end decomposition** of `G`: a partial one whose
terminal graph has exactly one vertex (Definitions 2.2 and 3.2). -/
def IsDecomp (maximum : Bool) (G : BipGraph) (N₀ : ℕ) (recs : List Rec) : Prop :=
  ∃ H, IsPartialDecomp maximum G N₀ recs H ∧ H.V.card = 1

/-- The union `B = ⋃ᵢ Pⁱ` of the recorded internal matchings (Algorithm 5, p.45, with every lifting
map the identity on edge identities). -/
def dijoinOf (recs : List Rec) : Finset ℕ := recs.foldr (fun r B => r.P ∪ B) ∅

/-- The edges of `G` with both ends in one of the sets `Us`. -/
def BipGraph.internalEdges (G : BipGraph) (Us : List (Finset ℕ)) : Finset ℕ :=
  Us.foldr (fun U acc => (G.induced U).E ∪ acc) ∅

end BipDijoin



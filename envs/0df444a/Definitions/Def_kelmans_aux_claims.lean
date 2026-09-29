-- Prove2me | Definitions.Def_kelmans_aux_claims
-- name    : kelmans_aux_claims
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-07T23:22:35.648642+00:00
-- url     : https://prove2.me/theorems/ed64318b-96ed-4a06-a638-7f8f830e16c8
-- title:
--   Deletion gadgets and intermediate claims for the Kelmans $(z1)$-$(z8)$ chain
-- statement:
--   Auxiliary deletion gadgets and intermediate claims for the $(z1) \Rightarrow (z8)$ chain of Kelmans Theorem 3.1 (arXiv:0910.2766v2, Theorem 3.1 as proved in 3.8, 3.11, 3.16, 3.15). For a finite simple graph $G$, `erasePair` deletes two vertices and takes the induced subgraph, while `erase2Edges` deletes two edges given by ordered endpoint pairs. On cubic 3-connected graphs, `ClaimZ4` says every vertex is the center of a 3-vertex path whose deletion leaves a $P_3$-factorable graph; `ClaimT2` says deleting the endpoints of any edge leaves a $P_3$-factorable graph when the order is $2 \bmod 6$; and `ClaimZ7` says deleting any two distinct edges leaves a $P_3$-factorable graph. All bounds are stated for ordinary small types, matching the mission's existing `ClaimZ1`/`ClaimZ8`.
-- source:
--   A. Kelmans, Packing 3-vertex Paths In Cubic 3-connected Graphs, https://arxiv.org/abs/0910.2766v2, Theorem 3.1, claims (z4), (t2), (z7); deletion gadgets follow Sections 3.15-3.16.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

/-- Delete two vertices and take the induced graph. -/
def erasePair {W : Type u} (G : SimpleGraph W) (x y : W) :
    SimpleGraph {v : W // v ≠ x ∧ v ≠ y} :=
  G.induce {v : W | v ≠ x ∧ v ≠ y}

/-- Delete two edges, given by ordered endpoint pairs (both orientations removed). -/
def erase2Edges {W : Type u} (G : SimpleGraph W) (a1 b1 a2 b2 : W) : SimpleGraph W where
  Adj u v := G.Adj u v ∧ ¬ ((u = a1 ∧ v = b1) ∨ (u = b1 ∧ v = a1) ∨ (u = a2 ∧ v = b2) ∨ (u = b2 ∧ v = a2))
  symm := ⟨by
    intro u v h
    refine ⟨G.adj_symm h.1, ?_⟩
    intro hc
    apply h.2
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inr (Or.inr ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))⟩
  loopless := ⟨by
    intro v h
    exact (G.ne_of_adj h.1) rfl⟩

/-- Claim (z4) in Kelmans's Theorem 3.1, restricted to ordinary small types:
every vertex is the center of a 3-vertex path whose deletion leaves a
P3-factorable graph. -/
def ClaimZ4 : Prop :=
  ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W,
    Cubic G → ThreeVertexConnected G → Fintype.card W % 6 = 0 →
      ∀ x : W, ∃ L : P3Path G, L.center = x ∧ Nonempty (P3Factor (eraseP3 G L))

/-- Claim (t2) in Kelmans's Theorem 3.1, restricted to ordinary small types:
deleting the endpoints of any edge leaves a P3-factorable graph. -/
def ClaimT2 : Prop :=
  ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W,
    Cubic G → ThreeVertexConnected G → Fintype.card W % 6 = 2 →
      ∀ x y : W, G.Adj x y → Nonempty (P3Factor (erasePair G x y))

/-- Claim (z7) in Kelmans's Theorem 3.1, restricted to ordinary small types:
deleting any two edges leaves a P3-factorable graph. -/
def ClaimZ7 : Prop :=
  ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W,
    Cubic G → ThreeVertexConnected G → Fintype.card W % 6 = 0 →
      ∀ a1 b1 a2 b2 : W, G.Adj a1 b1 → G.Adj a2 b2 →
        ({a1, b1} : Set W) ≠ {a2, b2} →
        Nonempty (P3Factor (erase2Edges G a1 b1 a2 b2))

end CubicP3Partition



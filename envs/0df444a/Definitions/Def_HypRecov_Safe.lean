-- Prove2me | Definitions.Def_HypRecov_Safe
-- name    : HypRecov_Safe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:33.059203+00:00
-- url     : https://prove2.me/theorems/baf1f456-c7fc-42b1-ae38-5a7bfd775882
-- title:
--   Safe partitions, coarsenings and block mergers
-- statement:
--   Fix a hypergraph $H$ and $k$. A partition of $V$, given by a block label $P:V\to V$, is **safe** if every **small cut**, a set $S$ with $\mathrm{cut}_H(S)<k$, is a union of blocks: two vertices with the same label lie on the same side of every small cut.
--
--   A partition $P'$ **coarsens** $P$ if every block of $P$ lies in a block of $P'$. $P'$ arises from $P$ by **merging the blocks meeting** a set $X$ if two vertices share a block of $P'$ exactly when they share a block of $P$ or both their $P$-blocks meet $X$. A set **spans** $P$ if it meets two blocks.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §4, p.8 (PDF p.9); §5.2, p.11; Theorem 6.2, p.14

import Mathlib
import Definitions.Def_HypRecov_crisp

namespace HypRecov

/-- **Safe partitions.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous Projection Streams*,
STOC 2027 submission (manuscript sha256 719dcfff…), §4, p.8 (PDF p.9): "Throughout the recovery
argument, a small cut means a cut S of the original hypergraph H with cut_H(S) < k. We call a
partition safe if every such S is a union of its blocks."

A partition of `Fin n` is given by a block label `P : Fin n → Fin n` (the blocks are its fibres).
`Safe E k P`: no small cut separates two vertices of one block. -/
def Safe {n : ℕ} (E : Finset (Finset (Fin n))) (k : ℕ) (P : Fin n → Fin n) : Prop :=
  ∀ S : Finset (Fin n), cut E S < k → ∀ u v : Fin n, P u = P v → (u ∈ S ↔ v ∈ S)

/-- `Coarsens P P'`: the partition `P'` is a coarsening of `P` (every block of `P` lies in a block of
`P'`); §4, p.9: "The current partition P starts at P0 and is coarsened". -/
def Coarsens {n : ℕ} (P P' : Fin n → Fin n) : Prop := ∀ u v : Fin n, P u = P v → P' u = P' v

/-- `IsMergeOf P X P'`: `P'` arises from `P` by merging all blocks of `P` that meet `X` into one block
and leaving the other blocks unchanged (§5.2, p.11: "merge their current blocks"; Theorem 6.2, p.14:
"Its current blocks may be merged"). -/
def IsMergeOf {n : ℕ} (P : Fin n → Fin n) (X : Finset (Fin n)) (P' : Fin n → Fin n) : Prop :=
  ∀ u v : Fin n, P' u = P' v ↔ (P u = P v ∨ ((∃ a ∈ X, P a = P u) ∧ ∃ b ∈ X, P b = P v))

/-- `Spans P X`: `X` meets at least two blocks of `P` ("spanning current blocks", §5.2, p.11). -/
def Spans {n : ℕ} (P : Fin n → Fin n) (X : Finset (Fin n)) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, P u ≠ P v

/-- The number of blocks of `P`. -/
def numBlocks {n : ℕ} (P : Fin n → Fin n) : ℕ := (Finset.univ.image P).card

end HypRecov



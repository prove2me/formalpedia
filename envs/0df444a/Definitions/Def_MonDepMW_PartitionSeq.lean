-- Prove2me | Definitions.Def_MonDepMW_PartitionSeq
-- name    : MonDepMW_PartitionSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:35.374616+00:00
-- url     : https://prove2.me/theorems/3ba86291-b85d-483f-b875-c6a0a1d3b54f
-- title:
--   Partition sequences and partition merge-width
-- statement:
--   A **partition sequence** for $G$ is a sequence $\mathcal P_1\sqsubseteq\dots\sqsubseteq\mathcal P_m$ of ever coarser partitions of $V(G)$ with $\mathcal P_1$ the partition into singletons and $\mathcal P_m$ having the one part $V(G)$. Its **radius-$r$ width** is the smallest $k$ such that for every $i\in[m-1]$ and $u\in V(G)$, $\mathrm{Ball}^r_{\mathcal P_{i+1}}[u]$ intersects at most $k$ parts of $\mathcal P_i$. The **radius-$r$ partition merge-width** of $G$ is the least $k$ such that $G$ admits a partition sequence of radius-$r$ width at most $k$.
--
--   Partition merge-width avoids the sets $R_i$ by working with balls of the flip-metric; Theorem 3.5 converts it to merge-width.
--
--   **Formalization Note** The width and the partition merge-width are `sInf` of sets that always contain $n$, so they are true minima. `PartitionSeq.ofSets` packages the sequence $\mathcal T_1(G,B_0),\dots,\mathcal T_1(G,B_m)$ of Theorem 4.3.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.14

import Mathlib
import Definitions.Def_MonDepMW_IsFlip

set_option autoImplicit false

namespace MonDepMW

/-- A sequence of partitions `𝒫₁, …, 𝒫_m` of `Fin n`, indexed `1, …, m` as on the page. -/
structure PartitionSeq (n : ℕ) where
  m : ℕ
  P : ℕ → Setoid (Fin n)

/-- **Partition sequences.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.14: "A partition sequence for a graph G is a sequence 𝒫1 ⊑ 𝒫2 ⊑ . . . ⊑ 𝒫m of
ever coarser partitions of the vertex set of G such that 𝒫1 is the partition into singletons and 𝒫m has one part
V (G)." The condition does not involve the edges of `G`. -/
structure PartitionSeq.IsValid {n : ℕ} (S : PartitionSeq n) : Prop where
  one_le : 1 ≤ S.m
  first : S.P 1 = ⊥
  last : S.P S.m = ⊤
  mono : ∀ i, 1 ≤ i → i + 1 ≤ S.m → S.P i ≤ S.P (i + 1)

/-- **Radius-`r` width at most `k` of a partition sequence.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.14: "For every i ∈ [m − 1] and u ∈ V (G),
Ball^r_{𝒫_{i+1}}[u] intersects at most k parts of 𝒫i." -/
def PartitionSeq.WidthLE {n : ℕ} (S : PartitionSeq n) (G : SimpleGraph (Fin n)) (r k : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i + 1 ≤ S.m → ∀ u, partsHit (S.P i) (flipBall G (S.P (i + 1)) r u) ≤ k

/-- **The radius-`r` width of a partition sequence**, "the smallest integer k satisfying" `WidthLE` (p.14).

**Formalization Note.** The set is nonempty (`k = n` always works), so `sInf` is its minimum, not the junk value. -/
noncomputable def PartitionSeq.width {n : ℕ} (S : PartitionSeq n) (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | S.WidthLE G r k}

/-- **The radius-`r` partition merge-width.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.14: "the radius-r partition merge-width of G is the least k
such that G admits a partition sequence of radius-r width at most k."

**Formalization Note.** The set is nonempty (`k = n`, with the sequence `⊥, ⊤`), so `sInf` is its minimum. -/
noncomputable def partitionMergeWidth {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | ∃ S : PartitionSeq n, S.IsValid ∧ S.WidthLE G r k}

/-- The sequence `𝒫₀ ⊑ … ⊑ 𝒫_m`, `𝒫_i := 𝒯₁(G, B_i)`, of Theorem 4.3 (p.16), as a `PartitionSeq` of length `m + 1`:
its entry number `i` (from `1`) is `𝒯₁(G, B_{i−1})`. -/
def PartitionSeq.ofSets {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) (B : ℕ → Finset (Fin n)) : PartitionSeq n where
  m := m + 1
  P := fun i => oneType G (B (i - 1))

end MonDepMW



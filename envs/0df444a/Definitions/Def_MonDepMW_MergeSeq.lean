-- Prove2me | Definitions.Def_MonDepMW_MergeSeq
-- name    : MonDepMW_MergeSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:32.508447+00:00
-- url     : https://prove2.me/theorems/25e774b9-646b-4f0d-a9ca-88cd110e7e8d
-- title:
--   Merge sequences, their radius-$r$ width and merge-width
-- statement:
--   A **merge sequence** for $G$ is a sequence $(\mathcal P_1,R_1),\dots,(\mathcal P_m,R_m)$ such that:
--
--   1. $\mathcal P_1\sqsubseteq\dots\sqsubseteq\mathcal P_m$ are ever coarser partitions of $V$, $\mathcal P_1$ is the partition into singletons and $\mathcal P_m$ has the one part $V$;
--   2. $R_1\subseteq\dots\subseteq R_m\subseteq\binom V2$;
--   3. for every $i\in[m]$ and parts $P,P'\in\mathcal P_i$ (possibly equal), either all pairs $uu'\in\binom V2$ with $u\in P,u'\in P'$, $uu'\notin R_i$ are edges of $G$, or they are all non-edges of $G$.
--
--   Its **radius-$r$ width** is the smallest $k$ such that for every $i\in[m-1]$ and $u\in V$, $\mathrm{Ball}^r_{(V,R_{i+1})}[u]$ intersects at most $k$ parts of $\mathcal P_i$. The **radius-$r$ merge-width** of $G$ is the smallest $k$ such that $G$ admits a merge sequence of radius-$r$ width at most $k$.
--
--   This is the parameter bounded by the goal theorem.
--
--   **Formalization Note** Indices run over $1,\dots,m$ as on the page; values of the Lean sequences outside this range are not used. Each $R_i$ is a simple graph. The statements use the predicates "width at most $k$", which are equivalent to the smallest-$k$ phrasing.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.14

import Mathlib
import Definitions.Def_MonDepMW_IsFlip

set_option autoImplicit false

namespace MonDepMW

/-- A sequence `(𝒫₁, R₁), …, (𝒫_m, R_m)` on the vertex set `Fin n`, indexed `1, …, m` as on the page; the values of
`P`, `R` outside `1, …, m` are not used. `R i` is a set of pairs of distinct vertices, i.e. a simple graph. -/
structure MergeSeq (n : ℕ) where
  m : ℕ
  P : ℕ → Setoid (Fin n)
  R : ℕ → SimpleGraph (Fin n)

/-- **Merge sequences.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.14: "A merge sequence for G is a sequence (𝒫1, R1), …, (𝒫m, Rm) such that
𝒫1 ⊑ 𝒫2 ⊑ . . . ⊑ 𝒫m is a sequence of ever coarser partitions of the vertex set of G, where 𝒫1 is the partition into
singletons and 𝒫m has one part V ; R1 ⊆ R2 ⊆ . . . ⊆ Rm ⊆ (V choose 2) is an inclusion chain of sets of pairs of
vertices of G; for every i ∈ [m] and pair of parts P, P′ ∈ 𝒫i (possibly P = P′), either all pairs uu′ ∈ (V choose 2)
with u ∈ P, u′ ∈ P′, uu′ ∉ Ri, are edges in G, or they are all non-edges in G." -/
structure MergeSeq.IsFor {n : ℕ} (M : MergeSeq n) (G : SimpleGraph (Fin n)) : Prop where
  one_le : 1 ≤ M.m
  first : M.P 1 = ⊥
  last : M.P M.m = ⊤
  mono_P : ∀ i, 1 ≤ i → i + 1 ≤ M.m → M.P i ≤ M.P (i + 1)
  mono_R : ∀ i, 1 ≤ i → i + 1 ≤ M.m → M.R i ≤ M.R (i + 1)
  homog : ∀ i, 1 ≤ i → i ≤ M.m → ∀ a b : Fin n,
    (∀ u u', (M.P i).r a u → (M.P i).r b u' → u ≠ u' → ¬ (M.R i).Adj u u' → G.Adj u u') ∨
    (∀ u u', (M.P i).r a u → (M.P i).r b u' → u ≠ u' → ¬ (M.R i).Adj u u' → ¬ G.Adj u u')

/-- **Radius-`r` width at most `k`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.14: "For every i ∈ [m − 1] and u ∈ V , Ball^r_{(V,R_{i+1})}[u]
intersects at most k parts of 𝒫i." Note the `+1`: balls in `R_{i+1}`, parts of `𝒫_i`. -/
def MergeSeq.WidthLE {n : ℕ} (M : MergeSeq n) (r k : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i + 1 ≤ M.m → ∀ u, partsHit (M.P i) (ball (M.R (i + 1)) r u) ≤ k

/-- **Radius-`r` merge-width at most `k`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.14: "The radius-r merge-width of G is the smallest k such that G
admits a merge sequence of radius-r width at most k." -/
def MergeWidthLE {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ) : Prop :=
  ∃ M : MergeSeq n, M.IsFor G ∧ M.WidthLE r k

end MonDepMW



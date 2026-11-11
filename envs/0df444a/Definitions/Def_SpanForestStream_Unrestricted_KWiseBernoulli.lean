-- Prove2me | Definitions.Def_SpanForestStream_Unrestricted_KWiseBernoulli
-- name    : SpanForestStream_Unrestricted_KWiseBernoulli
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:30:55.147689+00:00
-- url     : https://prove2.me/theorems/79a55c9b-e293-495e-b72e-3a38f76769af
-- title:
--   r-wise independent Bernoulli sampling indicators and the sampled size
-- statement:
--   A law $P$ of an indicator family $(\omega_i)_{i\in\iota}$ is **$r$-wise independent with rate $p$** when every set $T$ of at most $r$ indices has the product law: $P(\omega_i=a_i\ \forall i\in T)=\prod_{i\in T}p^{a_i}(1-p)^{1-a_i}$. For a fixed finite set $S$ of names, the **sampled size** is $X=|\{i\in S:\omega_i=1\}|$. Level $j$ of a $(2b+2)$-wise independent hash keeps the names whose first $j$ hash bits are zero, which gives such a family with $r=2b+2$ and $p=2^{-j}$.
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 46 (PDF 49), Lemma B.1

import Mathlib

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-!
# `r`-wise independent Bernoulli indicators

Chao, Cen, Ma, Wang, arXiv:2611.04365, Lemma B.1, p. 46: the level-`j` sampling indicators of a
`(2b+2)`-wise independent hash are `(2b+2)`-wise independent with rate `p = 2^{-j}`.
-/

/-- The indicator family `ω : ι → Bool` with law `P` is `r`-wise independent with common rate `p`:
every set `T` of at most `r` coordinates has the product Bernoulli(`p`) law. -/
def IsKWiseBernoulli {ι : Type} (P : PMF (ι → Bool)) (r : ℕ) (p : ℝ≥0∞) : Prop :=
  ∀ T : Finset ι, T.card ≤ r → ∀ a : ι → Bool,
    P.toOuterMeasure {ω | ∀ i ∈ T, ω i = a i} = ∏ i ∈ T, (if a i then p else 1 - p)

/-- The sampled size `X = #{i ∈ S : ω i}` of a fixed finite set `S` of names. -/
def sampledSize {ι : Type} (S : Finset ι) (ω : ι → Bool) : ℕ :=
  (S.filter fun i => ω i = true).card

end SpanForestStream.Unrestricted



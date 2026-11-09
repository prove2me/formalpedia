-- Prove2me | Definitions.Def_GapCliqueLB_Clique_Dispersers
-- name    : GapCliqueLB_Clique_Dispersers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:44:26.846077+00:00
-- url     : https://prove2.me/theorems/6cf02fb9-31e7-4b29-b2f2-b83b16fa26f3
-- title:
--   Covering dispersers, pairwise covering dispersers, and the partition minimum
-- statement:
--   A family $T=(T_1,\ldots,T_\ell)$ consists of proper subsets of a universe of size $k$, with $2\le r<k$ and $1\le s<\ell$. It is a covering disperser if, for every set $I$ of $s+1$ indices and every $r$-subset $R$ of the universe, some $i\in I$ satisfies $R\subseteq T_i$. It is a pairwise covering disperser when there are distinct $i,j\in I$ with $R\subseteq T_i\cup T_j$. The union exponent is $\max_{i\ne j}|T_i\cup T_j|$, with zero as the empty-family default outside the disperser range.
--
--   An exact pair cover $B$ of $[h]$ is a family of two- and three-element subsets in which each pair of distinct elements occurs in exactly one block. Define
--
--   $$b(h)=\inf\{|B|:B\text{ is an exact pair cover of }[h]\}.$$
--
--   All pairs themselves give such a cover for every $h$, so this natural-number infimum is an attained minimum. The empty cover gives $b(0)=b(1)=0$. For a given cover define $T_i=\{A\in B:i\notin A\}$, using a fixed bijection from $B$ to $\{0,\ldots,|B|-1\}$ when a numeric universe is needed. No closed formula for $b$ is imposed.
--
--   These are the set systems and exact optimization parameter used by Theorem 1.1.
-- source:
--   Reina Itakura, Karthik C.S., Mayank Motwani, Gary Peng, STOC 2027 submission #232 (October 2026), Definition 4.2, PDF p. 15 (printed p. 14); Definition 5.1, PDF p. 18 (printed p. 17); Proposition 5.5, PDF p. 20 (printed p. 19); b in Theorem 1.1, PDF p. 3 (printed p. 2), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/232.pdf

import Mathlib

namespace GapCliqueLB.Clique

/-- Definition 4.2 with all standing side conditions. -/
def CoveringDisperser {k ℓ : ℕ} (T : Fin ℓ → Finset (Fin k)) (s r : ℕ) : Prop :=
  (∀ i, T i ⊂ Finset.univ) ∧ 2 ≤ r ∧ r < k ∧ 1 ≤ s ∧ s < ℓ ∧
    ∀ I : Finset (Fin ℓ), I.card = s + 1 →
      ∀ R : Finset (Fin k), R.card = r → ∃ i ∈ I, R ⊆ T i

/-- Definition 5.1 with all standing side conditions and distinct witnesses. -/
def PairwiseCoveringDisperser {k ℓ : ℕ}
    (T : Fin ℓ → Finset (Fin k)) (s r : ℕ) : Prop :=
  (∀ i, T i ⊂ Finset.univ) ∧ 2 ≤ r ∧ r < k ∧ 1 ≤ s ∧ s < ℓ ∧
    ∀ I : Finset (Fin ℓ), I.card = s + 1 →
      ∀ R : Finset (Fin k), R.card = r →
        ∃ i ∈ I, ∃ j ∈ I, i ≠ j ∧ R ⊆ T i ∪ T j

/-- Maximum over distinct pairs, with value zero if there are no such pairs. -/
def unionExponent {k ℓ : ℕ} (T : Fin ℓ → Finset (Fin k)) : ℕ :=
  ((Finset.univ : Finset (Fin ℓ × Fin ℓ)).filter (fun p => p.1 ≠ p.2)).sup
    (fun p => (T p.1 ∪ T p.2).card)

/-- Exact partitions of all pairs into two- and three-element blocks. -/
def PairCover (h : ℕ) : Set (Finset (Finset (Fin h))) :=
  {B | (∀ A ∈ B, A.card = 2 ∨ A.card = 3) ∧
    ∀ i j : Fin h, i ≠ j → ∃! A, A ∈ B ∧ i ∈ A ∧ j ∈ A}

/-- The minimum in Theorem 1.1, never a substituted closed formula. -/
noncomputable def b (h : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ B ∈ PairCover h, B.card = m}

/-- Proposition 5.5: the universe is the subtype of blocks of B. -/
def partitionSets {h : ℕ} (B : Finset (Finset (Fin h)))
    (i : Fin h) : Finset B :=
  Finset.univ.filter (fun A => i ∉ A.val)

/-- A bijective indexing of the universe B by [|B|]; the choice changes no instance. -/
noncomputable def blockIndex {h : ℕ} (B : Finset (Finset (Fin h))) : B ≃ Fin B.card :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def indexedPartitionSets {h : ℕ} (B : Finset (Finset (Fin h)))
    (i : Fin h) : Finset (Fin B.card) :=
  (partitionSets B i).image (blockIndex B)

end GapCliqueLB.Clique



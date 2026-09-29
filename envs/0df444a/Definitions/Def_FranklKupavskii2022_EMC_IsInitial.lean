-- Prove2me | Definitions.Def_FranklKupavskii2022_EMC_IsInitial
-- name    : FranklKupavskii2022_EMC_IsInitial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:13:29.734387+00:00
-- url     : https://prove2.me/theorems/4a473f56-3d87-46d1-b714-b3b530c7500c
-- title:
--   The shifting partial order $\prec$ and initial (shifted) families
-- statement:
--   For two sets $A=\{a_1<\dots<a_k\}$ and $B=\{b_1<\dots<b_k\}$ of the same size, $A$ **precedes** $B$, written $A\prec B$, if
--
--   $$
--   a_i\le b_i\quad\text{for all } i\in[k],\qquad A\ne B.
--   $$
--
--   A family $\mathcal F\subseteq\binom{[m]}{k}$ is **initial** (shifted) if $G\prec F\in\mathcal F$ implies $G\in\mathcal F$ for every $k$-subset $G$ of $[m]$.
--
--   Shifting reduces the Erdős Matching Conjecture to initial families: every family can be replaced by an initial one of the same size and no larger matching number.
--
--   **Formalization Note** Two sets are compared by listing each increasingly and comparing entrywise; sets of different sizes are incomparable. The closure condition quantifies only over $k$-subsets of $[m]=\{1,\dots,m\}$. The inclusion $\mathcal F\subseteq\binom{[m]}k$ is not part of the predicate and is stated separately in each theorem.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Sect. 2, p. 3 (shifting partial order, initial families)

import Mathlib

namespace FranklKupavskii2022.EMC

/-- The shifting partial order `A ≺ B` on sets of equal size (Frankl–Kupavskii,
arXiv:1806.08855v3, Sect. 2, p. 3): "(a_1, …, a_k) precedes (b_1, …, b_k) if a_i ≤ b_i for all
i ∈ [k] and the two k-sets are distinct. One can define this for unordered sets A, B by simply
comparing their elements after ordering them increasingly."

**Formalization Note.** Both sets are listed increasingly (`Finset.sort`) and compared entrywise
with `List.Forall₂ (· ≤ ·)`; `Forall₂` forces the two lists to have equal length, so `A ≺ B`
implies `|A| = |B|`. -/
def Precedes (A B : Finset ℕ) : Prop :=
  List.Forall₂ (· ≤ ·) A.sort B.sort ∧ A ≠ B

/-- Initial (shifted) families (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2, p. 3): "A family
F ⊂ \binom{[m]}{k} is called initial (shifted) if G ≺ F ∈ F implies G ∈ F."

**Formalization Note.** The downward closure ranges over `k`-subsets `G` of `[m] = Finset.Icc 1 m`
only, as in the paper, where every set is a subset of `[m]`. (A `k`-set of naturals containing
`0` precedes members of `F` but is not a subset of `[m]`.) The requirement `F ⊆ \binom{[m]}{k}`
is not part of this predicate; the theorems state it separately. -/
def IsInitial (m k : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ G ∈ (Finset.Icc 1 m).powersetCard k, ∀ F' ∈ F, Precedes G F' → G ∈ F

end FranklKupavskii2022.EMC



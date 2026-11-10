-- Prove2me | Definitions.Def_CountOrderings_NFree_X3C
-- name    : CountOrderings_NFree_X3C
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:56:22.017018+00:00
-- url     : https://prove2.me/theorems/d4a5c335-6826-4266-a76e-11484d0a2ba0
-- title:
--   Instances of #X3C, exact covers, and #X3C(I)
-- statement:
--   An instance $I = (\mathcal{S}, U)$ of **#X3C** (counting exact covers by 3-sets) consists of a universe $U = \{u_0, \dots, u_{3h-1}\}$ with $3h$ elements and a family $S_0, \dots, S_{n-1}$ of $3$-element subsets of $U$, indexed by $\{0, \dots, n-1\}$.
--
--   An **exact cover** of $I$ is a set $X \subseteq \{0, \dots, n-1\}$ of indices with
--   $$|X| = h \qquad\text{and}\qquad \bigcup_{i \in X} S_i = U ;$$
--   since $|U| = 3h$, its sets are pairwise disjoint. $\mathrm{X3C}(I)$ is the set of exact covers and $\#\mathrm{X3C}(I) = |\mathrm{X3C}(I)|$.
--
--   The **standing assumptions** of the paper's reductions from #X3C are: every element of $U$ belongs to at least one $S_i$, and $h < n$.
--
--   **Formalization Note.** The family is indexed, so two indices may carry the same 3-set; for a family of $n$ distinct sets (the paper's $\mathcal{S} = \{S_1, \dots, S_n\}$ with $|\mathcal{S}| = n$) index sets and subfamilies correspond one to one. Indices start at $0$.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, pp. 7–8 (PDF pp. 8–9), §2 (#X3C, exact covers, standing assumptions)

import Mathlib

namespace CountOrderings.NFree

/-- An instance `I = (S, U)` of **#X3C** (counting exact covers by 3-sets): a universe
`U = {u_0, …, u_{3h-1}}` (written `Fin (3h)`) and an indexed family `S_0, …, S_{n-1}` of
3-element subsets of `U`. -/
structure X3CInstance where
  /-- `|U| = 3h`. -/
  h : ℕ
  /-- The number of sets in the family. -/
  n : ℕ
  /-- The sets `S_i ⊆ U`. -/
  S : Fin n → Finset (Fin (3 * h))
  /-- Every `S_i` has exactly three elements. -/
  card_S : ∀ i, (S i).card = 3

/-- The **standing assumptions** of the reductions from #X3C (p. 8): every element of `U`
belongs to at least one set of the family, and `h < n`. -/
def X3CInstance.Standing (I : X3CInstance) : Prop :=
  (∀ j : Fin (3 * I.h), ∃ i : Fin I.n, j ∈ I.S i) ∧ I.h < I.n

/-- An **exact cover** of `I`: a subfamily `X` (a set of indices) with `|X| = h` whose union is
`U`. -/
def X3CInstance.IsExactCover (I : X3CInstance) (X : Finset (Fin I.n)) : Prop :=
  X.card = I.h ∧ X.biUnion I.S = Finset.univ

open Classical in
/-- `X3C(I)`: the set of exact covers of `I`. -/
noncomputable def X3CInstance.exactCovers (I : X3CInstance) : Finset (Finset (Fin I.n)) :=
  (Finset.univ : Finset (Finset (Fin I.n))).filter I.IsExactCover

/-- `#X3C(I) = |X3C(I)|`: the number of exact covers of `I`. -/
noncomputable def X3CInstance.numExactCovers (I : X3CInstance) : ℕ :=
  I.exactCovers.card

end CountOrderings.NFree



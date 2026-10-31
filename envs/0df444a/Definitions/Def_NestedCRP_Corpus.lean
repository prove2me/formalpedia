-- Prove2me | Definitions.Def_NestedCRP_Corpus
-- name    : NestedCRP_Corpus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:45.587356+00:00
-- url     : https://prove2.me/theorems/0e4d8bf1-3635-40ff-8018-46984bf1a3fa
-- title:
--   Corpus, word sites, level allocations and sampler state
-- statement:
--   An observed corpus consists of $D$ documents over a vocabulary of size $V$, where document $d$ has $N_d$ words $w_{d,n}$. A word site is a pair $(d,n)$. Level allocations assign a level $z_{d,n}\in\mathbb N$ to each site, with no bound on the level. The state of the collapsed sampler is a pair (tree, level allocations), which is $\{c_{1:D},z_{1:D}\}$ of §5.3 with paths encoded by the tree. The module also provides the update of one site's level.
--
--   **Formalization Note** Document lengths are fixed, as the paper does not model them, and $N_d=0$ is allowed. Documents and words are 0-based.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §4, p.7:11; §5.3, p.7:17

import Mathlib
import Definitions.Def_NestedCRP_Tree

namespace NestedCRP

/-- The observed corpus: `D` documents over a vocabulary of size `V`, document `d` having `N d`
words `w d n`. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §4, p.7:11.

**Formalization Note** Document lengths are fixed: the paper does not model them. `N d = 0` is
allowed. Words and documents are 0-based. -/
structure Corpus (V D : ℕ) where
  N : Fin D → ℕ
  w : ∀ d, Fin (N d) → Fin V

variable {V D : ℕ}

/-- The word sites `(d, n)` of a corpus. -/
abbrev Corpus.Site (C : Corpus V D) : Type := Σ d : Fin D, Fin (C.N d)

/-- The word at a site. -/
def Corpus.word (C : Corpus V D) (s : C.Site) : Fin V := C.w s.1 s.2

/-- Level allocations `z`: a level `z d n : ℕ` for each word, with no bound on the level. -/
abbrev Corpus.Levels (C : Corpus V D) : Type := ∀ d, Fin (C.N d) → ℕ

/-- The state of the collapsed sampler: the tree and the level allocations. This is
`{c_{1:D}, z_{1:D}}` of §5.3, p.7:17, with the paths encoded by the tree. -/
abbrev Corpus.State (C : Corpus V D) : Type := Tree D × C.Levels

/-- `z` with the level of site `s` changed to `k`. -/
def Corpus.setLevel (C : Corpus V D) (z : C.Levels) (s : C.Site) (k : ℕ) : C.Levels :=
  fun d n => if (⟨d, n⟩ : C.Site) = s then k else z d n

end NestedCRP



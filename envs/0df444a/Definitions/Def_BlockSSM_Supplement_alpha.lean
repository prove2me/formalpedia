-- Prove2me | Definitions.Def_BlockSSM_Supplement_alpha
-- name    : BlockSSM_Supplement_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:01:59.220527+00:00
-- url     : https://prove2.me/theorems/7cb7fcb1-af6c-4a89-81c4-ea3a48fad25c
-- title:
--   The invariant $\alpha(P)=\min\{d(P/A): A\trianglelefteq P \text{ abelian}\}$
-- statement:
--   For a finite group $P$ let $d(X)$ denote the minimum number of generators of a group $X$. Define
--   $$
--   \alpha(P)=\min\{\,d(P/A)\;:\;A\trianglelefteq P,\ A\text{ abelian}\,\}.
--   $$
--   The trivial subgroup is abelian and normal, so the minimum is over a nonempty set.
--
--   The paper uses $\alpha$ for finite $p$-groups $P$; Theorem 14 bounds $D_b(P)$ below by $p\,\alpha(P)$.
--
--   **Formalization Note** $d$ is Mathlib's `Group.rank`, the least size of a generating set.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §6, p.6 (PDF p.7)

import Mathlib

universe u

namespace BlockSSM.Supplement

/-- **The invariant `α(P)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §6, p.6 (PDF p.7): "For a finite p-group P, define
α(P) = min{d(P/A) : A ⊴ P, A abelian}", where `d(X)` is the minimum number of generators of `X`.

**Formalization Note.** `d` is Mathlib's `Group.rank` (the least cardinality of a generating
finset). The trivial subgroup is abelian and normal, so the set is nonempty and `sInf` is its
minimum. The definition is stated for every finite group; the paper uses it for `p`-groups. -/
noncomputable def alpha (P : Type u) [Group P] [Finite P] : ℕ :=
  sInf {k : ℕ | ∃ (A : Subgroup P) (_ : A.Normal),
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ Group.rank (P ⧸ A) = k}

end BlockSSM.Supplement



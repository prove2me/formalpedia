-- Prove2me | Definitions.Def_ResistantSets_IsMinimalPoint
-- name    : ResistantSets_IsMinimalPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:20.38999+00:00
-- url     : https://prove2.me/theorems/a815dfa0-bcbc-4be5-a90c-84ccd034ab67
-- title:
--   Minimal point of a set $T\subseteq\{0,1\}^n$
-- statement:
--   A **minimal point** of $T\subseteq\{0,1\}^n$ is a point of $T$ of minimal support, the support $\{i : a_i=1\}$ being ordered by inclusion. So $a$ is a minimal point of $T$ when $a\in T$ and every $c\in T$ with $\{i : c_i=1\}\subseteq\{i : a_i=1\}$ equals $a$.
--
--   The supports of the minimal points of $S\triangle x$ are the members of the induced clutter $\operatorname{ind}(S\triangle x)$, and minimal points of twisted sets define valid pairs.
--
--   **Formalization Note** Minimality is inclusion-minimality of supports, not minimality of cardinality.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.7 ("A minimal point of S is simply a point in S of minimal support"), with p.3 (ind(S△x))

import Mathlib

namespace ResistantSets

/-- **Minimal point** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §2, p.7): "A minimal point of S is simply a point in S of minimal
support", the support being ordered by inclusion. So `a` is a minimal point of `T` if
`a ∈ T` and every `c ∈ T` whose support is contained in that of `a` equals `a`.

**Formalization Note** Minimality is inclusion-minimality of supports (as in the definition of
the induced clutter `ind(S△x)`, p.3), not minimality of cardinality. -/
def IsMinimalPoint {n : ℕ} (T : Finset (Fin n → Bool)) (a : Fin n → Bool) : Prop :=
  a ∈ T ∧ ∀ c ∈ T, (∀ i, c i = true → a i = true) → c = a

end ResistantSets



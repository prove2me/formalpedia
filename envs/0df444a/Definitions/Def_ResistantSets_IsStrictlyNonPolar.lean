-- Prove2me | Definitions.Def_ResistantSets_IsStrictlyNonPolar
-- name    : ResistantSets_IsStrictlyNonPolar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:08.455207+00:00
-- url     : https://prove2.me/theorems/7496072d-96a2-4ff1-b2bb-02b121ef55a7
-- title:
--   Strictly non-polar set
-- statement:
--   A set $S\subseteq\{0,1\}^n$ is **strictly non-polar** if it is non-polar but every proper restriction of it is polar. A restriction is proper if at least one 0- or 1-restriction is applied, so the proper restrictions are those of dimension $m$ with $1\le m<n$.
--
--   For resistant sets, strict non-polarity is equivalent to the cuboid being an ideal minimally non-packing clutter (Theorem 1.15), which is why the paper classifies such sets.
--
--   **Formalization Note** Restrictions have dimension at least $1$: the $0$-dimensional empty set would be non-polar, and counting it would make every set with an infeasible point fail strict non-polarity. The kept coordinates may be relabeled; polarity does not see the labels.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.6, §1.2 ("We say that S is strictly non-polar if it is non-polar, but every proper restriction is polar"), with p.4 (proper)

import Mathlib
import Definitions.Def_ResistantSets_IsPolar
import Definitions.Def_ResistantSets_restrict

namespace ResistantSets

/-- **Strictly non-polar set** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.2, p.6): "We say that S is strictly non-polar if it is
non-polar, but every proper restriction is polar." A restriction is proper if at least one
0- or 1-restriction is applied (p.4).

**Formalization Note** A proper restriction is `restrict S ι a` with `ι : Fin m ↪ Fin n` and
`1 ≤ m < n`. Restrictions have dimension at least 1 (the 0-dimensional `∅` would be non-polar
and make strict non-polarity impossible for every set with an infeasible point, contradicting
p.6). Allowing `ι` to relabel the kept coordinates changes nothing, because polarity is
invariant under relabeling and twisting. -/
def IsStrictlyNonPolar {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  ¬ IsPolar S ∧
    ∀ m : ℕ, 1 ≤ m → m < n → ∀ (ι : Fin m ↪ Fin n) (a : Fin n → Bool), IsPolar (restrict S ι a)

end ResistantSets



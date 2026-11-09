-- Prove2me | Definitions.Def_HypClass1_IsIncreasing
-- name    : HypClass1_IsIncreasing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:44.465222+00:00
-- url     : https://prove2.me/theorems/783e0ec6-8dbe-47d1-904d-e4ce7e8a52b6
-- title:
--   Increasing family $\mathcal B \subseteq 2^X$
-- statement:
--   A family $\mathcal B \subseteq 2^X$ of subsets of a finite set $X$ is **increasing** if $A \in \mathcal B$ and $A \subseteq A' \subseteq X$ imply $A' \in \mathcal B$.
--
--   **Formalization Note** $X$ is a finite type.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.42

import Mathlib

namespace HypClass1

/-- **Increasing family** `B ⊆ 2^X`: closed under taking supersets. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.42 ("Let B ⊆ 2^X be a
non-empty increasing family of X").

**Formalization Note.** `X` is a finite type `α` and `B : Finset (Finset α)`. -/
def IsIncreasing {α : Type*} (B : Finset (Finset α)) : Prop :=
  ∀ A ∈ B, ∀ A' : Finset α, A ⊆ A' → A' ∈ B

end HypClass1



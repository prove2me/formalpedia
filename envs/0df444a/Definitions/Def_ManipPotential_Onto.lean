-- Prove2me | Definitions.Def_ManipPotential_Onto
-- name    : ManipPotential_Onto
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:39.215488+00:00
-- url     : https://prove2.me/theorems/4f97f4cb-afae-4c4b-b113-32d0f6aadd6e
-- title:
--   Onto social choice function
-- statement:
--   An SCF $f$ is **onto** if every candidate wins somewhere: for each $c \in C$ there is a profile (with at least one voter) in which $c$ wins.
--
--   **Formalization Note** The profile witnessing $c$ is required to be nonempty. The empty list is not a profile of voters $N = [n]$, and allowing it would let an otherwise three-candidate rule count as onto.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.25

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential

/-- Ontoness (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.25): every candidate wins at some profile.

**Formalization Note** The profile is required to be nonempty (a profile has voters `N = [n]`);
the value of `f` on the empty list is never used. -/
def Onto {m : ℕ} (f : List (Ranking m) → Fin m) : Prop :=
  ∀ c : Fin m, ∃ P : List (Ranking m), P ≠ [] ∧ f P = c

end ManipPotential



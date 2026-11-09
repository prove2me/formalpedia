-- Prove2me | Definitions.Def_ManipPotential_Anonymous
-- name    : ManipPotential_Anonymous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:30.687583+00:00
-- url     : https://prove2.me/theorems/b5aa40d7-1e96-424c-896a-2155a9869883
-- title:
--   Anonymous social choice function
-- statement:
--   An SCF $f$ is **anonymous** if its output is invariant under relabelling the voters: for every voter permutation $\tau$ and profile $\succ_N$, $f(\succ_N) = f(\tau(\succ_N))$.
--
--   With anonymous rules only the number of times each ranking is cast matters, which is what lets the proof pass to profiles weighted by rational multiplicities.
--
--   **Formalization Note** Profiles are lists, and a relabelling of voters is a permutation of the list.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s", p.10

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential

/-- Anonymity (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s", p.10): the outcome is invariant under every
relabelling of the voters.

**Formalization Note** A voter permutation of a list profile is a list permutation. -/
def Anonymous {m : ℕ} (f : List (Ranking m) → Fin m) : Prop :=
  ∀ P Q : List (Ranking m), P.Perm Q → f P = f Q

end ManipPotential



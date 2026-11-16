-- Prove2me | Definitions.Def_ManipPotential_Supplement_irvScore
-- name    : ManipPotential_Supplement_irvScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:02:53.305059+00:00
-- url     : https://prove2.me/theorems/6980803a-da39-4be9-87af-8a6e9e0ea2b9
-- title:
--   Instant Runoff score among the remaining candidates
-- statement:
--   For a profile $\succ_N$ and a set $R \subseteq C$ of remaining candidates, the **Instant Runoff score** of $x \in R$ is the number of voters whose top choice within $R$ is $x$: each ballot gives one point to $\mathrm{top}_{\succ_i} R$.
--
--   **Formalization Note** The score of a candidate outside $R$ is $0$ and is never used.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Example 1.1 and Section 4.1.2, p.12

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential.Supplement

/-- The Instant Runoff score of candidate `x` among the remaining candidates `R` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…),
Example 1.1 and Section 4.1.2, p.12): the number of ballots whose top choice within `R` is `x`.

**Formalization Note** A ballot's top choice in `R` is the element of `R` of least position; the
score of `x ∉ R` is `0` and is never used. -/
def irvScore {m : ℕ} (P : List (Ranking m)) (R : Finset (Fin m)) (x : Fin m) : ℕ :=
  P.countP (fun r => decide (x ∈ R ∧ ∀ y ∈ R, r x ≤ r y))

end ManipPotential.Supplement



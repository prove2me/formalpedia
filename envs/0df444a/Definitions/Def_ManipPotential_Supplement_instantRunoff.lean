-- Prove2me | Definitions.Def_ManipPotential_Supplement_instantRunoff
-- name    : ManipPotential_Supplement_instantRunoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:04:02.274736+00:00
-- url     : https://prove2.me/theorems/1aba5b27-5aa5-48ce-99fb-578c286ba9da
-- title:
--   Instant Runoff $\mathrm{IRV}$ (parallel-universes ties)
-- statement:
--   Under **Instant Runoff** ($\mathrm{IRV}$) the candidate with the fewest top-choice votes is iteratively eliminated until only one candidate remains, who wins. With parallel-universes tiebreaking, $c \in \mathrm{IRV}(\succ_N)$ if some way of breaking ties among the lowest-scoring candidates at the elimination steps leaves $c$ as the winner.
--
--   **Formalization Note** $c \in \mathrm{IRV}(\succ_N)$ iff $c$ survives from the full candidate set $C$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Example 1.1 and Section 4.1.2, p.12

import Mathlib
import Definitions.Def_ManipPotential_Supplement_SCC
import Definitions.Def_ManipPotential_Supplement_IRVSurvives

namespace ManipPotential.Supplement

open Classical in
/-- Instant Runoff `IRV` with parallel-universes tiebreaking (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Example 1.1 and Section 4.1.2,
p.12): the candidate with the fewest top-choice votes is eliminated repeatedly until one remains;
`c ∈ IRV(≻_N)` if some way of breaking the elimination ties leaves `c` as the winner.

**Formalization Note** `c ∈ IRV P` iff `IRVSurvives P C c` from the full candidate set. -/
noncomputable def instantRunoff {m : ℕ} : SCC m :=
  fun P => Finset.univ.filter (fun c => IRVSurvives P Finset.univ c)

end ManipPotential.Supplement



-- Prove2me | Definitions.Def_ManipPotential_Supplement_SCC
-- name    : ManipPotential_Supplement_SCC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:53:58.673423+00:00
-- url     : https://prove2.me/theorems/9b9175d8-6571-4c41-9253-e4edc8445090
-- title:
--   Social choice correspondences $F : \mathcal L(C)^* \to \mathcal P(C)$
-- statement:
--   A **social choice correspondence** (SCC) is a map $F : \mathcal L(C)^* \to \mathcal P(C)$ that assigns to every preference profile, with any number of voters, a set $F(\succ_N) \subseteq C$ of (tied) winners.
--
--   All rules of Section 4 (plurality, plurality with runoff, instant runoff, positional scoring rules, Black's rule, Maximin) are SCCs; they are turned into social choice functions with a linear tiebreaker.
--
--   **Formalization Note** A profile is a list of rankings of any length (footnote 8: rules are defined on profiles with any number of voters), and the winner set is a finite set of candidates `Finset (Fin m)`; the empty set is allowed by the type, as $\mathcal P(C)$ is the full power set.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s", p.10

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential.Supplement

/-- A social choice correspondence (SCC) `F : L(C)* → P(C)` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s",
p.10): a map from preference profiles of any length to sets of (tied) winners.

**Formalization Note** A profile is a `List (Ranking m)` of any length (footnote 8, p.8: rules are
defined on profiles with any number of voters); the set of winners is a `Finset (Fin m)`. The empty
set is allowed by the type, as `P(C)` is the full power set. -/
abbrev SCC (m : ℕ) : Type := List (Ranking m) → Finset (Fin m)

end ManipPotential.Supplement



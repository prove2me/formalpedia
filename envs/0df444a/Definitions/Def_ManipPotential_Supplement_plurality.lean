-- Prove2me | Definitions.Def_ManipPotential_Supplement_plurality
-- name    : ManipPotential_Supplement_plurality
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:58:03.228551+00:00
-- url     : https://prove2.me/theorems/8d22e845-0067-4156-9b92-e19a3718abe3
-- title:
--   Plurality $\mathrm{PL}$
-- statement:
--   Under **Plurality** ($\mathrm{PL}$) the winners are the candidates ranked top by the greatest number of voters. Equivalently, $\mathrm{PL} = F^s$ for $s = (1, 0, \dots, 0)$, since each ballot gives one point to its top candidate.
--
--   **Formalization Note** Defined as the scoring rule of the plurality vector, as on p.15.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.1.1, p.11; Section 4.2, p.15

import Mathlib
import Definitions.Def_ManipPotential_Supplement_scoringRule
import Definitions.Def_ManipPotential_Supplement_pluralityVec

namespace ManipPotential.Supplement

/-- Plurality `PL` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.1.1, p.11; identified with `F^s` for `s = (1, 0, …, 0)` on
p.15): the candidates ranked top by the greatest number of voters.

**Formalization Note** Defined as the scoring rule of `pluralityVec m`; a ballot gives `1` point
to its top candidate and `0` to the others, so the score is the number of top-choice votes. -/
noncomputable def plurality {m : ℕ} : SCC m := scoringRule (pluralityVec m)

end ManipPotential.Supplement



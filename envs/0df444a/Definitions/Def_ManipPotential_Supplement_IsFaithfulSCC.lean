-- Prove2me | Definitions.Def_ManipPotential_Supplement_IsFaithfulSCC
-- name    : ManipPotential_Supplement_IsFaithfulSCC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:07:37.324558+00:00
-- url     : https://prove2.me/theorems/f837d0cc-a760-4e09-9049-fee6ad50dd62
-- title:
--   Faithful SCC
-- statement:
--   An SCC $F$ is **faithful** if, given a profile consisting of a single vote $\succ_1$, it outputs the top choice of that vote: $F(\succ_1) = \{\mathrm{top}_{\succ_1} C\}$ [Young 1974].
--
--   **Formalization Note** This is not the published `ManipPotential.Faithful` of the base mission, which concerns rules on rational profiles.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3.3, p.20

import Mathlib
import Definitions.Def_ManipPotential_Ranking_top
import Definitions.Def_ManipPotential_Supplement_SCC

namespace ManipPotential.Supplement

/-- A faithful SCC (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3.3, p.20, after [You74]): on a profile consisting of a
single vote `≻₁`, it outputs the top choice of that vote, `F(≻₁) = {top_{≻₁} C}`.

**Formalization Note** Not the published `ManipPotential.Faithful`, which concerns rules on rational
profiles. -/
def IsFaithfulSCC {m : ℕ} [NeZero m] (F : SCC m) : Prop :=
  ∀ r : Ranking m, F [r] = {Ranking.top r}

end ManipPotential.Supplement



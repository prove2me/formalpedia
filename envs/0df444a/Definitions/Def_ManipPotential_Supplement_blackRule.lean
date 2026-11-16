-- Prove2me | Definitions.Def_ManipPotential_Supplement_blackRule
-- name    : ManipPotential_Supplement_blackRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:06:09.048214+00:00
-- url     : https://prove2.me/theorems/0790a8d3-41a1-4526-96ef-322f61af14d4
-- title:
--   Black's Rule $\mathrm{BL}$
-- statement:
--   **Black's Rule** ($\mathrm{BL}$): if the profile has a Condorcet winner, output it; otherwise output the Borda Count winner(s).
--
--   **Formalization Note** The Condorcet winner is unique when it exists, so in that case the output is the singleton of the Condorcet winner.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3.1, p.19

import Mathlib
import Definitions.Def_ManipPotential_Supplement_IsCondorcetWinner
import Definitions.Def_ManipPotential_Supplement_borda

namespace ManipPotential.Supplement

open Classical in
/-- Black's Rule `BL` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3.1, p.19): if there is a Condorcet winner, output it;
otherwise output the Borda Count winner(s).

**Formalization Note** The Condorcet winner is unique when it exists, so the first branch is the
singleton `{c}`. -/
noncomputable def blackRule {m : ℕ} : SCC m := fun P =>
  if ∃ c, IsCondorcetWinner P c then Finset.univ.filter (IsCondorcetWinner P) else borda P

end ManipPotential.Supplement



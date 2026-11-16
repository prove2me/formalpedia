-- Prove2me | Definitions.Def_ManipPotential_Supplement_IsCondorcetWinner
-- name    : ManipPotential_Supplement_IsCondorcetWinner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:05:24.700396+00:00
-- url     : https://prove2.me/theorems/80281bda-47c0-4ab3-b165-f5c8a60251d7
-- title:
--   Condorcet winner
-- statement:
--   A candidate $c$ is the **Condorcet winner** of a profile $\succ_N$ if it pairwise defeats every other candidate:
--   $$M(\succ_N)[c, c'] > 0 \quad \text{for all } c' \in C \setminus \{c\}.$$
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3, "Condorcet Consistency", p.19

import Mathlib
import Definitions.Def_ManipPotential_Supplement_margin

namespace ManipPotential.Supplement

/-- `c` is the Condorcet winner of the profile: `M(≻_N)[c, c'] > 0` for all `c' ∈ C ∖ {c}`
(Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3, "Condorcet Consistency", p.19). -/
def IsCondorcetWinner {m : ℕ} (P : List (Ranking m)) (c : Fin m) : Prop :=
  ∀ c' : Fin m, c' ≠ c → 0 < margin P c c'

end ManipPotential.Supplement



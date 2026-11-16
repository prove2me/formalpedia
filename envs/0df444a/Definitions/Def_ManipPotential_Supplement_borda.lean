-- Prove2me | Definitions.Def_ManipPotential_Supplement_borda
-- name    : ManipPotential_Supplement_borda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:58:52.24912+00:00
-- url     : https://prove2.me/theorems/a68b1135-4153-4a9c-b3a1-a3680ae0c384
-- title:
--   Borda Count $\mathrm{BC}$
-- statement:
--   Under **Borda Count** ($\mathrm{BC}$) each voter gives $m - j$ points to her $j$-th ranked candidate ($j \in [m]$), and the candidates of highest total Borda score win. Scaling all points by $1/(m-1)$ does not change the winners, so $\mathrm{BC} = F^s$ for the normalized Borda vector.
--
--   **Formalization Note** Defined as the scoring rule of the normalized Borda vector, as on p.15 (for $m \ge 2$ the scaling is by a positive constant).
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Example 1.1 and Section 4.1.3, p.13; Section 4.2, p.15

import Mathlib
import Definitions.Def_ManipPotential_Supplement_scoringRule
import Definitions.Def_ManipPotential_Supplement_bordaVec

namespace ManipPotential.Supplement

/-- Borda Count `BC` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Example 1.1 and Section 4.1.3, p.13; identified with `F^s` for the
normalized Borda vector on p.15): each voter gives `m − j` points to her `j`-th ranked candidate and
the candidates of highest total score win.

**Formalization Note** Defined as the scoring rule of `bordaVec m`, i.e. the Borda points
`m − j` scaled by `1/(m − 1)`; as the paper notes (p.15), the scaling does not change the output
for `m ≥ 2`. -/
noncomputable def borda {m : ℕ} : SCC m := scoringRule (bordaVec m)

end ManipPotential.Supplement



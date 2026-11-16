-- Prove2me | Definitions.Def_ManipPotential_Supplement_IsMajoritarian
-- name    : ManipPotential_Supplement_IsMajoritarian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:07:11.878775+00:00
-- url     : https://prove2.me/theorems/e27382d8-888b-474e-a95a-f8e65cb8757e
-- title:
--   Majoritarian SCC
-- statement:
--   An SCC $F$ is **majoritarian** if it depends only on the signs of the margin matrix: for any two profiles $\succ_N, \succ'_N$ with
--   $$\operatorname{sign}\bigl(M(\succ_N)[c, c']\bigr) = \operatorname{sign}\bigl(M(\succ'_N)[c, c']\bigr) \quad \text{for all } c, c' \in C,$$
--   we have $F(\succ_N) = F(\succ'_N)$.
--
--   **Formalization Note** The two profiles may have different numbers of voters; the proof of Theorem 4.13 compares a profile with a single ballot.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3.3, p.20

import Mathlib
import Definitions.Def_ManipPotential_Supplement_SCC
import Definitions.Def_ManipPotential_Supplement_margin

namespace ManipPotential.Supplement

/-- A majoritarian SCC (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3.3, p.20): for any two profiles with
`sign(M(≻_N)[c, c']) = sign(M(≻'_N)[c, c'])` for all pairs `c, c'`, `F(≻_N) = F(≻'_N)`.

**Formalization Note** The two profiles may have different lengths (the proof of Theorem 4.13
compares a profile with a single ballot). -/
def IsMajoritarian {m : ℕ} (F : SCC m) : Prop :=
  ∀ P Q : List (Ranking m),
    (∀ c c' : Fin m, Int.sign (margin P c c') = Int.sign (margin Q c c')) → F P = F Q

end ManipPotential.Supplement



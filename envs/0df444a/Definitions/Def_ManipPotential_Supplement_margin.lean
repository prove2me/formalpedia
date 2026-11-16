-- Prove2me | Definitions.Def_ManipPotential_Supplement_margin
-- name    : ManipPotential_Supplement_margin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:04:37.570196+00:00
-- url     : https://prove2.me/theorems/a77f5646-5fb6-4d61-81d7-acf99a6aad7d
-- title:
--   Margin matrix $M(\succ_N)$
-- statement:
--   The **margin matrix** of a profile $\succ_N$ is the $m \times m$ integer matrix
--   $$M(\succ_N)[c, c'] := |\{ i \in N : c \succ_i c' \}| - |\{ i \in N : c' \succ_i c \}| .$$
--
--   It is used to define Condorcet winners, Black's rule, Maximin and majoritarian rules.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3, "Condorcet Consistency", p.19

import Mathlib
import Definitions.Def_ManipPotential_Supplement_pairCount

namespace ManipPotential.Supplement

/-- The margin matrix `M(≻_N)[c, c'] := |{i : c ≻_i c'}| − |{i : c' ≻_i c}|` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3,
"Condorcet Consistency", p.19).

**Formalization Note** Integer valued; `M[c, c] = 0`. -/
def margin {m : ℕ} (P : List (Ranking m)) (c c' : Fin m) : ℤ :=
  (pairCount P c c' : ℤ) - (pairCount P c' c : ℤ)

end ManipPotential.Supplement



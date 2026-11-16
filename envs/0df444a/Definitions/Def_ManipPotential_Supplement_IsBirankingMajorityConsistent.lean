-- Prove2me | Definitions.Def_ManipPotential_Supplement_IsBirankingMajorityConsistent
-- name    : ManipPotential_Supplement_IsBirankingMajorityConsistent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:08:43.168955+00:00
-- url     : https://prove2.me/theorems/501c5fc2-0ab4-4425-b7ad-b418c3fd9c45
-- title:
--   Biranking-majority-consistent SCF
-- statement:
--   A social choice function $f$ is **biranking-majority-consistent** if for every profile consisting of only two types of rankings $\succ_a, \succ_b$ (every voter submits $\succ_a$ or $\succ_b$) in which one ranking appears strictly more often than the other, $f$ picks the top choice of the more frequent ranking.
--
--   **Formalization Note** Stated for social choice functions $f : \mathcal L(C)^* \to C$, as Theorem 4.15 uses it, on profiles of any length.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 4, p.22

import Mathlib
import Definitions.Def_ManipPotential_Ranking_top

namespace ManipPotential.Supplement

/-- Biranking majority consistency of an SCF (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 4, p.22): for every profile
consisting of only two types of rankings `≻_a, ≻_b`, if one of them appears strictly more often than
the other, the rule picks the top choice of the more frequent ranking.

**Formalization Note** For an SCF `f : L(C)* → C` ("(only) picks" is `f P = top_a C`). Profiles of
any length, including those with only one ranking type (`b` absent, or `a = b`, where the hypothesis
`count b < count a` fails and nothing is required). -/
def IsBirankingMajorityConsistent {m : ℕ} [NeZero m] (f : List (Ranking m) → Fin m) : Prop :=
  ∀ (a b : Ranking m) (P : List (Ranking m)),
    (∀ r ∈ P, r = a ∨ r = b) → P.count b < P.count a → f P = Ranking.top a

end ManipPotential.Supplement



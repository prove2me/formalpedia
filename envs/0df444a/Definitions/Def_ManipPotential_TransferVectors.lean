-- Prove2me | Definitions.Def_ManipPotential_TransferVectors
-- name    : ManipPotential_TransferVectors
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T22:43:24.486443+00:00
-- url     : https://prove2.me/theorems/233037a3-688d-49d0-b308-7611402ff30e
-- title:
--   Transfer vectors $T_{ij}$ (17)
-- statement:
--   For a real parameter $\lambda$ and candidates $c_i,c_j$, the transfer vectors are
--   $$
--   T_{ij}=\{\lambda r-s:r,s\in\mathcal L(C),\ c_i\succ_r c_j\}
--   \cup\{s-\lambda r:r,s\in\mathcal L(C),\ c_j\succ_r c_i\},
--   $$
--   where a ranking $r$ also denotes its unit vector in $\mathbb R^{\mathcal L(C)}$ and the two rankings in each displayed expression range independently over all rankings.
--
--   These are the ballot replacements used in Proposition 6.12: bounded manipulation potential says that such a replacement cannot turn winner $c_i$ into winner $c_j$. The set also linearly generates the cone whose dual is the comparison cone (18)–(19).
--
--   **Formalization Note** `Ranking.Prefers r i j` means $c_i\succ_r c_j$, and `unitVec r` is the unit vector $e_r$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Eq. (17), p.34

import Mathlib
import Definitions.Def_ManipPotential_Ranking_Prefers
import Definitions.Def_ManipPotential_unitVec

namespace ManipPotential

/-- The finite set of transfer vectors for a candidate pair `(i,j)` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Eq. (17), p.34):
`T_ij = {λr − s : c_i ≻_r c_j} ∪ {s − λr : c_j ≻_r c_i}`.
The rankings `r,s` range independently over all rankings. -/
def TransferVectors {m : ℕ} (lam : ℝ) (i j : Fin m) : Set (Ranking m → ℝ) :=
  {u | (∃ r s : Ranking m, Ranking.Prefers r i j ∧
      u = lam • unitVec r - unitVec s) ∨
    (∃ r s : Ranking m, Ranking.Prefers r j i ∧
      u = unitVec s - lam • unitVec r)}

end ManipPotential



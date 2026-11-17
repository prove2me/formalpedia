-- Prove2me | Definitions.Def_SpencerEight_Supplement_IsSignedPerm
-- name    : SpencerEight_Supplement_IsSignedPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:48:59.7912+00:00
-- url     : https://prove2.me/theorems/2ba09b25-cea7-4d32-a9d0-74653b7f7748
-- title:
--   Signed permutation matrix
-- statement:
--   A real square matrix is a **signed permutation matrix** if its entries lie in $\{-1,0,1\}$ and each row and each column has exactly one nonzero entry.
--
--   All the lower-bound families of Section 15 consist of symmetric signed permutation matrices.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 15.2, p.289 (PDF p.289)

import Mathlib

namespace SpencerEight.Supplement

/-- A signed permutation matrix (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 15.2, p.289 (PDF p.289)): a real square
matrix with entries in `{−1, 0, 1}` and exactly one nonzero entry in each row and in each column. -/
def IsSignedPerm {m : Type*} (A : Matrix m m ℝ) : Prop :=
  (∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) ∧
    (∀ i, ∃! j, A i j ≠ 0) ∧ (∀ j, ∃! i, A i j ≠ 0)

end SpencerEight.Supplement



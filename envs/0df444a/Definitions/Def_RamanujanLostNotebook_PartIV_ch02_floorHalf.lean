-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch02_floorHalf
-- name    : RamanujanLostNotebook_PartIV_ch02_floorHalf
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T15:15:13.465741+00:00
-- url     : https://prove2.me/theorems/b72d85bf-5b3c-4b0e-8015-90149b6dc5f6
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 2: floorHalf
-- statement:
--   The function `F` of equation (2.1.4) (Ramanujan's nonstandard `[x]`):
--   `F x = ⌊x⌋` when `x` is not an integer and `F x = x - 1/2` when `x` is an integer.
--   In particular `F x = 0` for `0 < x < 1`, so that the sums `∑_{n ≥ 1} F (x / n) …` of the
--   chapter are finite: only the `n ≤ x` contribute.  They are written below as sums over
--   `Finset.Icc 1 ⌊x⌋₊`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 2.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- The function `F` of equation (2.1.4) (Ramanujan's nonstandard `[x]`):
`F x = ⌊x⌋` when `x` is not an integer and `F x = x - 1/2` when `x` is an integer.
In particular `F x = 0` for `0 < x < 1`, so that the sums `∑_{n ≥ 1} F (x / n) …` of the
chapter are finite: only the `n ≤ x` contribute.  They are written below as sums over
`Finset.Icc 1 ⌊x⌋₊`. -/
noncomputable def floorHalf (x : ℝ) : ℝ :=
  if (⌊x⌋ : ℝ) = x then x - 1 / 2 else (⌊x⌋ : ℝ)

end RamanujanLostNotebook.PartIV



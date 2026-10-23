-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch16_ch16S
-- name    : RamanujanLostNotebook_PartII_ch16_ch16S
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T03:13:25.599151+00:00
-- url     : https://prove2.me/theorems/e853a5d4-311a-40da-ab21-c261916a26a5
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 16: ch16S
-- statement:
--   The function S_s obtained by solving its defining equation (16.3.1), p.387.
--   For real s other than 1,2,3 all three zeta arguments avoid their pole at 1.
--   Only zero and nonzero multiples of four are used here. Riemann zeta at real
--   regular arguments is real; taking its real part retains that source value.
--   No claim about Mathlib's totalized value at a zeta pole is made.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 16.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch16_ch16STerm

namespace RamanujanLostNotebook.PartII

/-- The function S_s obtained by solving its defining equation (16.3.1), p.387.
For real s other than 1,2,3 all three zeta arguments avoid their pole at 1.
Only zero and nonzero multiples of four are used here. Riemann zeta at real
regular arguments is real; taking its real part retains that source value.
No claim about Mathlib's totalized value at a zeta pole is made. -/
noncomputable def ch16S (s : ℝ) : ℝ :=
  (∑' n : ℕ, ch16STerm s n) + (riemannZeta ((s - 1 : ℝ) : ℂ)).re / 2 -
    3 * (riemannZeta (s : ℂ)).re / (4 * Real.pi) -
    Real.pi * (riemannZeta ((s - 2 : ℝ) : ℂ)).re / 12

end RamanujanLostNotebook.PartII



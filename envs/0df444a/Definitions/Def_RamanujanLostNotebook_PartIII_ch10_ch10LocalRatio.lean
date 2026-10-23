-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10LocalRatio
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10LocalRatio
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T12:25:44.103124+00:00
-- url     : https://prove2.me/theorems/32a0a1a0-c67f-41ba-b8d2-f3ba15260146
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10LocalRatio
-- statement:
--   The quotient of consecutive prime-power divisor factors for s>0, x>1 and r≥1; denominator then strictly positive.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- The quotient of consecutive prime-power divisor factors for s>0, x>1 and r≥1; denominator then strictly positive. -/
noncomputable def ch10LocalRatio (s : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  (1 - Real.rpow x (-s * (r + 1))) / (1 - Real.rpow x (-s * r))

end RamanujanLostNotebook.PartIII

end



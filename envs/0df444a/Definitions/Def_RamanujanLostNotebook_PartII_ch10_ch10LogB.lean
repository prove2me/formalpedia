-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10LogB
-- name    : RamanujanLostNotebook_PartII_ch10_ch10LogB
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T08:40:33.597976+00:00
-- url     : https://prove2.me/theorems/8ccd7887-1ab6-40ac-8cb9-813a48e3a109
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10LogB
-- statement:
--   Factor logarithms of the second product in (10.3.2), with opposite signs for the theta and minus-theta factors. This fixes continuous product powers.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Factor logarithms of the second product in (10.3.2), with opposite signs for the theta and minus-theta factors. This fixes continuous product powers. -/
noncomputable def ch10LogB (alpha theta : ℂ) (n : ℕ) : ℂ :=
  let m : ℂ := 2 * (n : ℂ) + 1
  let u := (-1 : ℂ) ^ n * Complex.exp (-alpha * (m - theta) / 2)
  let v := (-1 : ℂ) ^ n * Complex.exp (-alpha * (m + theta) / 2)
  Complex.log (1 - u) - Complex.log (1 + u) -
    Complex.log (1 - v) + Complex.log (1 + v)

end RamanujanLostNotebook.PartII

end



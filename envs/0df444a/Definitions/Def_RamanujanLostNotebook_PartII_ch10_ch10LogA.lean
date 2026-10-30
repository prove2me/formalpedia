-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10LogA
-- name    : RamanujanLostNotebook_PartII_ch10_ch10LogA
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:39:59.06465+00:00
-- url     : https://prove2.me/theorems/68ce251c-9a80-406e-b8b9-202e4ddfeedf
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10LogA
-- statement:
--   Weighted factor logarithms of the first product in (10.3.2). Each log is the principal log of 1±u, not of the entire product; for positive real part of alpha and real |theta|<1, |u|<1.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Weighted factor logarithms of the first product in (10.3.2). Each log is the principal log of 1±u, not of the entire product; for positive real part of alpha and real |theta|<1, |u|<1. -/
noncomputable def ch10LogA (alpha theta : ℂ) (n : ℕ) : ℂ :=
  let m : ℂ := 2 * (n : ℂ) + 1
  let u := (-1 : ℂ) ^ n * Complex.exp (-alpha * (m - theta) / 2)
  let v := (-1 : ℂ) ^ n * Complex.exp (-alpha * (m + theta) / 2)
  m * (Complex.log (1 - u) - Complex.log (1 + u) +
    Complex.log (1 - v) - Complex.log (1 + v))

end RamanujanLostNotebook.PartII

end



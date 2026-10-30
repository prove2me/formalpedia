-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10LogC
-- name    : RamanujanLostNotebook_PartII_ch10_ch10LogC
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:39:55.891468+00:00
-- url     : https://prove2.me/theorems/0fbc0b8d-80dd-4354-8513-442865e452ce
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10LogC
-- statement:
--   Weighted factor logarithms of the third product in (10.3.2), indexed from 1 via n+1. The factors use phases exp(±i pi theta/2).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Weighted factor logarithms of the third product in (10.3.2), indexed from 1 via n+1. The factors use phases exp(±i pi theta/2). -/
noncomputable def ch10LogC (beta theta : ℂ) (n : ℕ) : ℂ :=
  let m : ℕ := n + 1
  let u := (-1 : ℂ) ^ m * Complex.I *
    Complex.exp (theta * (Real.pi : ℂ) * Complex.I / 2) * Complex.exp (-beta * m)
  let v := (-1 : ℂ) ^ m * Complex.I *
    Complex.exp (-theta * (Real.pi : ℂ) * Complex.I / 2) * Complex.exp (-beta * m)
  (m : ℂ) * (Complex.log (1 + u) - Complex.log (1 - u) +
    Complex.log (1 + v) - Complex.log (1 - v))

end RamanujanLostNotebook.PartII

end



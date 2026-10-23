-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3LaurentA
-- name    : RamanujanLostNotebook_PartIII_ch03_ch3LaurentA
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T09:04:19.6984+00:00
-- url     : https://prove2.me/theorems/89ed8d8c-605d-4c32-83d0-0a32ad503517
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 3: ch3LaurentA
-- statement:
--   The symmetric Laurent polynomial A_n=a^n+a^(-n) of (3.1.4), p.46.
--   In particular A_0=2; these are formal coefficients, not complex parameters.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 3.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3MonomialA

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- The symmetric Laurent polynomial A_n=a^n+a^(-n) of (3.1.4), p.46.
In particular A_0=2; these are formal coefficients, not complex parameters. -/
def ch3LaurentA (n : ℕ) : AddMonoidAlgebra ℤ ℤ :=
  ch3MonomialA (n : ℤ) + ch3MonomialA (-(n : ℤ))

end RamanujanLostNotebook.PartIII

end



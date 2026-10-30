-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11Inv
-- name    : RamanujanLostNotebook_PartII_ch11_ch11Inv
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:23:43.968149+00:00
-- url     : https://prove2.me/theorems/bedf90e7-b3e4-46ab-8dc9-1455b54f262e
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11Inv
-- statement:
--   A finite geometric polynomial. If U has constant term 1, this agrees with 1/U
--   through degree N. It defines exact coefficients for every N, not a numerical truncation.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- A finite geometric polynomial. If U has constant term 1, this agrees with 1/U
through degree N. It defines exact coefficients for every N, not a numerical truncation. -/
noncomputable def ch11Inv (U : Polynomial ℤ) (N : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (N + 1), (1 - U) ^ j

end RamanujanLostNotebook.PartII

end



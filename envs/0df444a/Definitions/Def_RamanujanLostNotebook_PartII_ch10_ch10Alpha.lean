-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10Alpha
-- name    : RamanujanLostNotebook_PartII_ch10_ch10Alpha
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T08:43:05.750648+00:00
-- url     : https://prove2.me/theorems/37617208-7365-4a2d-ae89-2955dfea4e50
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10Alpha
-- statement:
--   The positive nome parameter pi K(k′)/K(k), (10.1.2). K(k′) uses the positive complementary modulus.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10K

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- The positive nome parameter pi K(k′)/K(k), (10.1.2). K(k′) uses the positive complementary modulus. -/
noncomputable def ch10Alpha (k : ℝ) : ℝ :=
  Real.pi * ch10K (Real.sqrt (1 - k ^ 2)) / ch10K k

end RamanujanLostNotebook.PartII

end



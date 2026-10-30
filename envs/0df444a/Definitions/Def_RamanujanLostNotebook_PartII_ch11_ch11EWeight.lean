-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11EWeight
-- name    : RamanujanLostNotebook_PartII_ch11_ch11EWeight
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:33:30.074889+00:00
-- url     : https://prove2.me/theorems/aeacacc9-6131-404d-8bc4-8b985e2a30df
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11EWeight
-- statement:
--   Eisenstein cosine weight h_lambda(n), (11.3.7)-(11.3.8), for any integer n.
--   The canonical representative has nonzero denominator 2d-c.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11Bezout
import Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11EReps

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Eisenstein cosine weight h_lambda(n), (11.3.7)-(11.3.8), for any integer n.
The canonical representative has nonzero denominator 2d-c. -/
noncomputable def ch11EWeight (n : ℤ) (la : ℕ) : ℝ :=
  if la = 1 then 1 else if la = 3 then -1 else
    2 * ∑ cd ∈ ch11EReps la,
      let ab := ch11Bezout cd.1 cd.2
      Real.cos (((ab.1 * cd.2 + ab.2 * cd.1 - 2 * ab.1 * cd.1 -
        2 * ab.2 * cd.2 + (la : ℤ) : ℤ) : ℝ) * (n : ℝ) * Real.pi / la -
        6 * Real.arctan ((cd.1 : ℝ) * Real.sqrt 3 / (2 * (cd.2 : ℝ) - cd.1)))

end RamanujanLostNotebook.PartII

end



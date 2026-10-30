-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch13_ch13Q
-- name    : RamanujanLostNotebook_PartII_ch13_ch13Q
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:44:45.649418+00:00
-- url     : https://prove2.me/theorems/06c1425e-85c0-4ebb-978f-0e6554167c5f
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 13: ch13Q
-- statement:
--   Ramanujan's Q at the nome q, p.327. The Lambert family is absolutely
--   summable for ‖q‖<1; chapter conclusions state this rather than assuming it.
--   Outside that disk this totalized sum is not the source's analytic object.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 13.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch13_ch13LambertTerm

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Ramanujan's Q at the nome q, p.327. The Lambert family is absolutely
summable for ‖q‖<1; chapter conclusions state this rather than assuming it.
Outside that disk this totalized sum is not the source's analytic object. -/
def ch13Q (q : ℂ) : ℂ :=
  1 + 240 * ∑' n : ℕ, ch13LambertTerm 3 q n

end RamanujanLostNotebook.PartII

end



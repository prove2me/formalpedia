-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09EulerRegular
-- name    : RamanujanLostNotebook_PartII_ch09_ch09EulerRegular
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:06:14.335142+00:00
-- url     : https://prove2.me/theorems/7e96a003-fe05-47ce-a426-becf362740a8
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 9: ch09EulerRegular
-- statement:
--   Analytic meaning of the shared Euler product: its base is in the unit
--   disk, its defining family is multipliable, and its value is nonzero.
--   This is returned in theorem conclusions to rule out totalized products
--   and division by zero; it is never a hypothesis containing an identity.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 9.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_eulerF

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Analytic meaning of the shared Euler product: its base is in the unit
disk, its defining family is multipliable, and its value is nonzero.
This is returned in theorem conclusions to rule out totalized products
and division by zero; it is never a hypothesis containing an identity. -/
def ch09EulerRegular (q : ℂ) : Prop :=
  ‖q‖ < 1 ∧ Multipliable (fun k : ℕ => 1 - q * q ^ k) ∧ eulerF q ≠ 0

end RamanujanLostNotebook.PartII

end



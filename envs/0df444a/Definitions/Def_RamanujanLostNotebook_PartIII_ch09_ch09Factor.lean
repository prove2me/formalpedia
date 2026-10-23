-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch09_ch09Factor
-- name    : RamanujanLostNotebook_PartIII_ch09_ch09Factor
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T08:02:09.675097+00:00
-- url     : https://prove2.me/theorems/23dcb05b-350b-47b4-9ef8-8333537407fe
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 9: ch09Factor
-- statement:
--   The circular factor F_n(t²) defined by the constrained lattice sum in
--   (9.2.12). The printed argument in that display differs from (9.1.2); the
--   uniformizer convention removes this overload. Series convergence is asserted
--   in entry_9_1_1_a, rather than assumed. Values outside |t|<1 are unused.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 9.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch09_ch09FTerm

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- The circular factor F_n(t²) defined by the constrained lattice sum in
(9.2.12). The printed argument in that display differs from (9.1.2); the
uniformizer convention removes this overload. Series convergence is asserted
in entry_9_1_1_a, rather than assumed. Values outside |t|<1 are unused. -/
def ch09Factor (n : ℕ) (t : ℂ) : ℂ :=
  ∑' m : Fin n → ℤ, ch09FTerm n t m

end RamanujanLostNotebook.PartIII

end



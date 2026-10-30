-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch09_ch09FTerm
-- name    : RamanujanLostNotebook_PartIII_ch09_ch09FTerm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T07:58:59.359706+00:00
-- url     : https://prove2.me/theorems/267dd7fe-6091-4565-97e3-965855367ae2
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 9: ch09FTerm
-- statement:
--   The constrained lattice term of (9.2.12), pp.341–342. The variable t is a
--   uniformizing parameter: this is the book's F_n(t²), NOT F_n(t). The exponent
--   is nonnegative by Cauchy–Schwarz on the selected tuples; toNat changes no selected
--   exponent. For n=1 only m=0 survives. For |t|<1 the selected lattice series
--   converges absolutely. Unselected tuples contribute zero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 9.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- The constrained lattice term of (9.2.12), pp.341–342. The variable t is a
uniformizing parameter: this is the book's F_n(t²), NOT F_n(t). The exponent
is nonnegative by Cauchy–Schwarz on the selected tuples; toNat changes no selected
exponent. For n=1 only m=0 survives. For |t|<1 the selected lattice series
converges absolutely. Unselected tuples contribute zero. -/
def ch09FTerm (n : ℕ) (t : ℂ) (m : Fin n → ℤ) : ℂ :=
  if 0 ≤ ∑ i, m i ∧ (∑ i, m i) < (n : ℤ) then
    t ^ ((n : ℤ) * (∑ i, (m i) ^ 2) - (∑ i, m i) ^ 2).toNat
  else 0

end RamanujanLostNotebook.PartIII

end



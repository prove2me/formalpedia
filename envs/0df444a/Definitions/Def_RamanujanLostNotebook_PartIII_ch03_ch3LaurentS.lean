-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3LaurentS
-- name    : RamanujanLostNotebook_PartIII_ch03_ch3LaurentS
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:04:25.349237+00:00
-- url     : https://prove2.me/theorems/9c099dcb-097f-42a7-b87a-825d5d99c326
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 3: ch3LaurentS
-- statement:
--   S_n=∑_{k=-n}^n a^k, the modulus of (3.5.1), p.56.
--   Divisibility by S_n in Z[a,a⁻¹] expresses coefficientwise formal congruence.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 3.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3MonomialA

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- S_n=∑_{k=-n}^n a^k, the modulus of (3.5.1), p.56.
Divisibility by S_n in Z[a,a⁻¹] expresses coefficientwise formal congruence. -/
def ch3LaurentS (n : ℕ) : AddMonoidAlgebra ℤ ℤ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ch3MonomialA k

end RamanujanLostNotebook.PartIII

end



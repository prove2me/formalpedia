-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_shared_thetaChi
-- name    : RamanujanLostNotebook_PartII_shared_thetaChi
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:19:56.617991+00:00
-- url     : https://prove2.me/theorems/25125b89-1592-4ae0-9183-8f74e1cc7608
-- title:
--   Ramanujan's Lost Notebook Part II, shared: thetaChi
-- statement:
--   Ramanujan's `χ(q) = (-q; q^2)_∞` (unnumbered displays on p. 103, Chapter 5, and p. 241,
--   Chapter 10).  The book's `χ(-q^9)` is `thetaChi (-(q ^ 9))`, which is `(q^9; q^18)_∞`.
--
--   Domain: `‖q‖ < 1`.  Classical relations in Ramanujan's notation, such as
--   `χ(q) = f(q) / f(-q^2) = φ(q) / f(q)`, i.e. `thetaChi q = eulerF (-q) / eulerF (q ^ 2)`,
--   are theorems about these definitions.
--   Totalization: that of `qPochInf`; `thetaChi 0 = 1`.
--   Reference: Taylor expansion `1 + q + q^3 + q^4 + q^5 + q^6 + q^7 + 2q^8 + 2q^9 + …`;
--   `thetaChi (1/5) = 1.2100032051692334160…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Ramanujan's `χ(q) = (-q; q^2)_∞` (unnumbered displays on p. 103, Chapter 5, and p. 241,
Chapter 10).  The book's `χ(-q^9)` is `thetaChi (-(q ^ 9))`, which is `(q^9; q^18)_∞`.

Domain: `‖q‖ < 1`.  Classical relations in Ramanujan's notation, such as
`χ(q) = f(q) / f(-q^2) = φ(q) / f(q)`, i.e. `thetaChi q = eulerF (-q) / eulerF (q ^ 2)`,
are theorems about these definitions.
Totalization: that of `qPochInf`; `thetaChi 0 = 1`.
Reference: Taylor expansion `1 + q + q^3 + q^4 + q^5 + q^6 + q^7 + 2q^8 + 2q^9 + …`;
`thetaChi (1/5) = 1.2100032051692334160…`. -/
def thetaChi (q : ℂ) : ℂ :=
  qPochInf (-q) (q ^ 2)

end RamanujanLostNotebook.PartII

end



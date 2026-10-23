-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch05_ch05EvenTerm
-- name    : RamanujanLostNotebook_PartII_ch05_ch05EvenTerm
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T04:45:29.686302+00:00
-- url     : https://prove2.me/theorems/8a5f875d-10d2-4b06-97f4-e7c349c719c1
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 5: ch05EvenTerm
-- statement:
--   The unilateral row on the left of (5.2.3), printed p.98.
--   The natural index is n>=0; the base of all four numerator products is q².
--   Used before the double-parameter boundary of Entry 5.3.10, p.107.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- The unilateral row on the left of (5.2.3), printed p.98.
The natural index is n>=0; the base of all four numerator products is q².
Used before the double-parameter boundary of Entry 5.3.10, p.107. -/
def ch05EvenTerm (q a rho₁ rho₂ : ℂ) (n : ℕ) : ℂ :=
  qPoch rho₁ (q ^ 2) n * qPoch rho₂ (q ^ 2) n *
    qPoch (-a * q) (q ^ 2) n * qPoch (-q / a) (q ^ 2) n /
    qPoch (q ^ 2) (q ^ 2) (2 * n) * (q ^ 2 / (rho₁ * rho₂)) ^ n

end RamanujanLostNotebook.PartII

end



-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch05_ch05Partition
-- name    : RamanujanLostNotebook_PartIII_ch05_ch05Partition
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T12:56:14.348204+00:00
-- url     : https://prove2.me/theorems/7794fd1b-b6c9-4ef6-8ed9-d26c32002df3
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 5: ch05Partition
-- statement:
--   Partition number p(n), the coefficient of ∏_{k≥1}(1-X^k)^(-1).
--   The empty partition gives p(0)=1.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch05_ch05EtaCoeff

namespace RamanujanLostNotebook.PartIII

/-- Partition number p(n), the coefficient of ∏_{k≥1}(1-X^k)^(-1).
The empty partition gives p(0)=1. -/
noncomputable def ch05Partition (n : ℕ) : ℤ :=
  ch05EtaCoeff [(1, -1)] n

end RamanujanLostNotebook.PartIII



-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch05_ch05PartitionZ
-- name    : RamanujanLostNotebook_PartIII_ch05_ch05PartitionZ
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T13:01:24.146994+00:00
-- url     : https://prove2.me/theorems/26da2bd0-47fd-4096-ae8a-2b9a01df994d
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 5: ch05PartitionZ
-- statement:
--   Integer-indexed partition convention used in recurrences: p(n)=0 for n<0.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch05_ch05Partition

namespace RamanujanLostNotebook.PartIII

/-- Integer-indexed partition convention used in recurrences: p(n)=0 for n<0. -/
noncomputable def ch05PartitionZ (n : ℤ) : ℤ :=
  if 0 ≤ n then ch05Partition n.toNat else 0

end RamanujanLostNotebook.PartIII



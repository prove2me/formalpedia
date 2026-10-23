-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch08_ch08P
-- name    : RamanujanLostNotebook_PartI_ch08_ch08P
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T03:01:46.381984+00:00
-- url     : https://prove2.me/theorems/5917ee6c-d674-4e1c-a133-585d3e752acb
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 8: ch08P
-- statement:
--   Modified numerator P_N(a), (8.2.1)--(8.2.2), pp.199,208.
--   For N>=2 the final denominator modification adds a*P_(N-1)(0);
--   the prescribed initial values at N=0,1 remain 0,1.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 8.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch08_ch08PQ0

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Modified numerator P_N(a), (8.2.1)--(8.2.2), pp.199,208.
For N>=2 the final denominator modification adds a*P_(N-1)(0);
the prescribed initial values at N=0,1 remain 0,1. -/
noncomputable def ch08P (q a : ℂ) (N : ℕ) : ℂ :=
  if N < 2 then (ch08PQ0 q N).1 else
    (ch08PQ0 q N).1 + a * (ch08PQ0 q (N - 1)).1

end RamanujanLostNotebook.PartI

end



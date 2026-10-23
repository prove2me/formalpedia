-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch02_ch02S
-- name    : RamanujanLostNotebook_PartI_ch02_ch02S
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T09:29:13.175039+00:00
-- url     : https://prove2.me/theorems/2349a4d0-e24b-41ac-8708-ca356858dfc1
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 2: ch02S
-- statement:
--   S(q) on the same fifth-root cover: r H(-q)/G(-q). The compatible fifth root of -q is -r, so this is -R(-q). It is positive for real 0<q<1, as used on p.62.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 2.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_rrG
import Definitions.Def_RamanujanLostNotebook_PartI_shared_rrH

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- S(q) on the same fifth-root cover: r H(-q)/G(-q). The compatible fifth root of -q is -r, so this is -R(-q). It is positive for real 0<q<1, as used on p.62. -/
noncomputable def ch02S (q r : ℂ) : ℂ := r * rrH (-q) / rrG (-q)

end RamanujanLostNotebook.PartI

end



-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10K
-- name    : RamanujanLostNotebook_PartII_ch10_ch10K
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T08:39:59.649564+00:00
-- url     : https://prove2.me/theorems/59892686-3d7e-4d66-8074-a7b1150ad097
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10K
-- statement:
--   Complete elliptic integral K(k), printed p.225. For 0<k<1 the positive square root has no zero on the integration interval.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Complete elliptic integral K(k), printed p.225. For 0<k<1 the positive square root has no zero on the integration interval. -/
noncomputable def ch10K (k : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(Real.pi / 2), 1 / Real.sqrt (1 - k ^ 2 * Real.sin u ^ 2)

end RamanujanLostNotebook.PartII

end



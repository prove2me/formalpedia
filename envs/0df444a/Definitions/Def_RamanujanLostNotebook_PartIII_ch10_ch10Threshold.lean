-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Threshold
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10Threshold
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T12:29:45.139613+00:00
-- url     : https://prove2.me/theorems/c966c222-4c37-468a-a13e-68d2074580c8
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10Threshold
-- statement:
--   The unique real root x_r>1 of (10.61.315), specified by the first crossing. Its existence, uniqueness and equation must be proved, rather than assumed in an asymptotic theorem.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10LocalRatio

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- The unique real root x_r>1 of (10.61.315), specified by the first crossing. Its existence, uniqueness and equation must be proved, rather than assumed in an asymptotic theorem. -/
noncomputable def ch10Threshold (s e : ℝ) (r : ℕ) : ℝ :=
  sInf {x : ℝ | 1 < x ∧ ch10LocalRatio s r x ≤ Real.rpow x e}

end RamanujanLostNotebook.PartIII

end



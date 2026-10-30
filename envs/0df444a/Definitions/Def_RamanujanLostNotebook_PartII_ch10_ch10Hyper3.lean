-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10Hyper3
-- name    : RamanujanLostNotebook_PartII_ch10_ch10Hyper3
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:43:14.569338+00:00
-- url     : https://prove2.me/theorems/79375aa6-05a0-4a65-9b21-3240eff860c7
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10Hyper3
-- statement:
--   The 3F2 series from (10.1.1), with real positive modulus. No convergence test is embedded in the definition.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10Hyper3Term

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- The 3F2 series from (10.1.1), with real positive modulus. No convergence test is embedded in the definition. -/
noncomputable def ch10Hyper3 (k : ℝ) : ℝ := ∑' n : ℕ, ch10Hyper3Term k n

end RamanujanLostNotebook.PartII

end



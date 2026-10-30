-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Convergent
-- name    : RamanujanLostNotebook_PartI_ch07_ch07Convergent
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:58:02.706929+00:00
-- url     : https://prove2.me/theorems/9327e551-e146-4264-ae57-40947ded0211
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07Convergent
-- statement:
--   The projective convergent P_N/Q_N. Zero Q_N is a totalized value; each convergence assertion below also requires Q_N to be nonzero eventually, in its conclusion.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Continuants

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The projective convergent P_N/Q_N. Zero Q_N is a totalized value; each convergence assertion below also requires Q_N to be nonzero eventually, in its conclusion. -/
noncomputable def ch07Convergent (a b : ℕ → ℂ) (N : ℕ) : ℂ :=
  (ch07Continuants a b N).1 / (ch07Continuants a b N).2

end RamanujanLostNotebook.PartI

end



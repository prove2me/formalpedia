-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07MinusDenominator
-- name    : RamanujanLostNotebook_PartI_ch07_ch07MinusDenominator
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:57:23.942133+00:00
-- url     : https://prove2.me/theorems/9cb7be5a-e2a5-4c37-8820-6c59b6baab96
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07MinusDenominator
-- statement:
--   Positive denominators of the transformed Entry 7.3.1 (k=3) or 7.3.2 (k=4). The outer denominator is separately fixed to 1 by ch07Continuants, so b₀ is unused.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Continuants

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Positive denominators of the transformed Entry 7.3.1 (k=3) or 7.3.2 (k=4). The outer denominator is separately fixed to 1 by ch07Continuants, so b₀ is unused. -/
noncomputable def ch07MinusDenominator (k : ℕ) (x : ℝ) (n : ℕ) : ℂ :=
  if k = 3 then ((1 + Real.exp ((n : ℝ) * x) : ℝ) : ℂ)
  else ((Real.exp ((n : ℝ) * x) + Real.exp (-(n : ℝ) * x) : ℝ) : ℂ)

end RamanujanLostNotebook.PartI

end



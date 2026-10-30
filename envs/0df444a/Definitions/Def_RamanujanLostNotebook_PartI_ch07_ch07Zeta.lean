-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Zeta
-- name    : RamanujanLostNotebook_PartI_ch07_ch07Zeta
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:53:34.92498+00:00
-- url     : https://prove2.me/theorems/8b454747-2bc4-4877-b1f4-c09f4d9b6c6a
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07Zeta
-- statement:
--   ζ(s) for a natural integer s≥2, as the absolutely convergent series starting at 1. Values at s=0,1 are unused totalizations.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- ζ(s) for a natural integer s≥2, as the absolutely convergent series starting at 1. Values at s=0,1 are unused totalizations. -/
noncomputable def ch07Zeta (s : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ s

end RamanujanLostNotebook.PartI

end



-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Falling
-- name    : RamanujanLostNotebook_PartI_ch13_ch13Falling
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T10:22:27.422913+00:00
-- url     : https://prove2.me/theorems/cb38e6e2-201b-4df3-8cbb-a15c558b17dc
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 13: ch13Falling
-- statement:
--   Integer falling factorial, with subtraction in Z even for negative indices.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 13.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Integer falling factorial, with subtraction in Z even for negative indices. -/
def ch13Falling (n : ℤ) (k : ℕ) : ℂ :=
  ∏ i ∈ Finset.range k, ((n - (i : ℤ) : ℤ) : ℂ)

end RamanujanLostNotebook.PartI

end



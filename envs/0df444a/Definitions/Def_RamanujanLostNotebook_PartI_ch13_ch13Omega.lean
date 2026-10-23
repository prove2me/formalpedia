-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Omega
-- name    : RamanujanLostNotebook_PartI_ch13_ch13Omega
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T10:44:31.873991+00:00
-- url     : https://prove2.me/theorems/10e11381-cc8d-48d6-b99b-6743c8e79762
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 13: ch13Omega
-- statement:
--   The denominator of the nth factor in (13.1.1); i starts at one.
--   Its convergence and nonvanishing are conclusions of the Entry, not assumptions.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 13.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Y

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The denominator of the nth factor in (13.1.1); i starts at one.
Its convergence and nonvanishing are conclusions of the Entry, not assumptions. -/
def ch13Omega (q : ℂ) (N : ℕ) : ℂ :=
  1 - ∑' i : ℕ, ch13Y q (i + 1) * q ^ (N * (i + 1))

end RamanujanLostNotebook.PartI

end



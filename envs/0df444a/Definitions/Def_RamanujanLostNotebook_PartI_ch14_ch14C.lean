-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch14_ch14C
-- name    : RamanujanLostNotebook_PartI_ch14_ch14C
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:45:43.016563+00:00
-- url     : https://prove2.me/theorems/6e84cffb-8f4a-4d2c-ae44-ddc4d34967c6
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 14: ch14C
-- statement:
--   The constant of (14.1.5) and (14.3.2): 3√3/(4π) times the absolutely convergent character series at s=2. The index starts at 1.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 14.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch14_ch14Chi3

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The constant of (14.1.5) and (14.3.2): 3√3/(4π) times the absolutely convergent character series at s=2. The index starts at 1. -/
noncomputable def ch14C : ℝ :=
  3 * Real.sqrt 3 / (4 * Real.pi) *
    ∑' n : ℕ, (ch14Chi3 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2

end RamanujanLostNotebook.PartI

end



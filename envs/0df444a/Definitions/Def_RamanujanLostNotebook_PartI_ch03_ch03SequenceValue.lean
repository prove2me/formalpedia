-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03SequenceValue
-- name    : RamanujanLostNotebook_PartI_ch03_ch03SequenceValue
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T10:05:46.560129+00:00
-- url     : https://prove2.me/theorems/14e4bb71-5f8e-4a20-b861-8c3bfb4f43d0
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 3: ch03SequenceValue
-- statement:
--   Select the limit of a convergent complex sequence, and 0 when it has no
--   limit. In the Hausdorff space ℂ the selected limit is unique. The definition
--   asserts no convergence; statements consuming a continued fraction include
--   Tendsto to the selected value in their conclusions. No identity or product
--   formula is built into this selector.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 3.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Select the limit of a convergent complex sequence, and 0 when it has no
limit. In the Hausdorff space ℂ the selected limit is unique. The definition
asserts no convergence; statements consuming a continued fraction include
Tendsto to the selected value in their conclusions. No identity or product
formula is built into this selector. -/
noncomputable def ch03SequenceValue (s : ℕ → ℂ) : ℂ :=
  by
    classical
    exact if h : ∃ z : ℂ, Filter.Tendsto s Filter.atTop (nhds z) then Classical.choose h else 0

end RamanujanLostNotebook.PartI

end



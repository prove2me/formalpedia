-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Poch
-- name    : RamanujanLostNotebook_PartI_ch07_ch07Poch
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T04:54:13.823602+00:00
-- url     : https://prove2.me/theorems/d64bc1f5-3735-4f2a-8dc7-8b5a286e88a4
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07Poch
-- statement:
--   The positive real product (e^{-rx};e^{-kx})∞, read as the real part of the approved complex q-Pochhammer. Its positive-real and convergence meaning is asserted for k≥3, 1≤r<k, x>0; other inputs are unused.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The positive real product (e^{-rx};e^{-kx})∞, read as the real part of the approved complex q-Pochhammer. Its positive-real and convergence meaning is asserted for k≥3, 1≤r<k, x>0; other inputs are unused. -/
noncomputable def ch07Poch (k r : ℕ) (x : ℝ) : ℝ :=
  (qPochInf ((Real.exp (-(r : ℝ) * x) : ℝ) : ℂ)
    ((Real.exp (-(k : ℝ) * x) : ℝ) : ℂ)).re

end RamanujanLostNotebook.PartI

end



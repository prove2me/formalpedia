-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch15_ch15Elliptic
-- name    : RamanujanLostNotebook_PartI_ch15_ch15Elliptic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:10:00.520864+00:00
-- url     : https://prove2.me/theorems/545d9b6e-d400-486a-8d74-a453eaeab93a
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 15: ch15Elliptic
-- statement:
--   E(m;a,b)=∫_a^b(1-m sin²φ)^{-1/2}dφ, oriented interval integral. The parameter m is the squared modulus, not the modulus. For m<1 the denominator is strictly positive for every real φ and finite intervals are integrable.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 15.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- E(m;a,b)=∫_a^b(1-m sin²φ)^{-1/2}dφ, oriented interval integral. The parameter m is the squared modulus, not the modulus. For m<1 the denominator is strictly positive for every real φ and finite intervals are integrable. -/
def ch15Elliptic (m a b : ℝ) : ℝ :=
  ∫ phi in a..b, 1 / Real.sqrt (1 - m * Real.sin phi ^ 2)

end RamanujanLostNotebook.PartI

end



-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Sigma
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10Sigma
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T12:26:22.227221+00:00
-- url     : https://prove2.me/theorems/bcd3a467-7fab-4194-91b5-86edb742fd17
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10Sigma
-- statement:
--   Divisor power sum sigma_t(n) for positive n. The manuscript sigma_{-s} is ch10Sigma (-s). All evaluated divisors are positive, including at s=0.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Divisor power sum sigma_t(n) for positive n. The manuscript sigma_{-s} is ch10Sigma (-s). All evaluated divisors are positive, including at s=0. -/
noncomputable def ch10Sigma (t : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Nat.divisors n, Real.rpow (d : ℝ) t

end RamanujanLostNotebook.PartIII

end



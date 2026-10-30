-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch16_ch16STerm
-- name    : RamanujanLostNotebook_PartII_ch16_ch16STerm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T03:06:43.724102+00:00
-- url     : https://prove2.me/theorems/003e9eca-9829-451a-8468-cd2a8e1ca141
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 16: ch16STerm
-- statement:
--   The k=n+1 summand of (16.3.1), p.387: k^(1-s)/(exp(2 pi k)-1).
--   The base of Real.rpow is positive and the denominator is strictly positive.
--   The exponential denominator gives absolute convergence for every fixed real s.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 16.

import Mathlib

namespace RamanujanLostNotebook.PartII

/-- The k=n+1 summand of (16.3.1), p.387: k^(1-s)/(exp(2 pi k)-1).
The base of Real.rpow is positive and the denominator is strictly positive.
The exponential denominator gives absolute convergence for every fixed real s. -/
noncomputable def ch16STerm (s : ℝ) (n : ℕ) : ℝ :=
  Real.rpow ((n + 1 : ℕ) : ℝ) (1 - s) /
    (Real.exp (2 * ((n + 1 : ℕ) : ℝ) * Real.pi) - 1)

end RamanujanLostNotebook.PartII



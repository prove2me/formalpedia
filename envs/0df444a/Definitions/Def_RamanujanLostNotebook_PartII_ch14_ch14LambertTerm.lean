-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14LambertTerm
-- name    : RamanujanLostNotebook_PartII_ch14_ch14LambertTerm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:33:15.822261+00:00
-- url     : https://prove2.me/theorems/e948137b-cf5a-4cde-ba05-cf41cb6667c3
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 14: ch14LambertTerm
-- statement:
--   The m=n+1 summand m^s q^m/(1-q^m) of (14.1.2)--(14.1.4), p.355.
--   For |q|<1 the denominator cannot vanish and the series converges absolutely.
--   The index shift excludes m=0; at q=0 every term is zero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 14.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- The m=n+1 summand m^s q^m/(1-q^m) of (14.1.2)--(14.1.4), p.355.
For |q|<1 the denominator cannot vanish and the series converges absolutely.
The index shift excludes m=0; at q=0 every term is zero. -/
noncomputable def ch14LambertTerm (s : ℕ) (q : ℂ) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) ^ s * q ^ (n + 1) / (1 - q ^ (n + 1))

end RamanujanLostNotebook.PartII

end



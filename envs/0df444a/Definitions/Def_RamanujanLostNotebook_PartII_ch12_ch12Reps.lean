-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Reps
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Reps
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:19:08.092467+00:00
-- url     : https://prove2.me/theorems/dca6f8be-ebd5-4d6e-88a2-16c4fd900589
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Reps
-- statement:
--   Canonical representatives of primitive sums of two squares: c>d>0,
--   c²+d²=μ, gcd(c,d)=1. The exceptional orbits μ=1,2 are handled separately.
--   One such pair represents each sign/interchange orbit of Definition 11.4.1.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib

namespace RamanujanLostNotebook.PartII

/-- Canonical representatives of primitive sums of two squares: c>d>0,
c²+d²=μ, gcd(c,d)=1. The exceptional orbits μ=1,2 are handled separately.
One such pair represents each sign/interchange orbit of Definition 11.4.1. -/
def ch12Reps (mu : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (mu + 1)).product (Finset.range (mu + 1))).filter
    (fun cd => 0 < cd.2 ∧ cd.2 < cd.1 ∧ cd.1 ^ 2 + cd.2 ^ 2 = mu ∧
      Nat.Coprime cd.1 cd.2)

end RamanujanLostNotebook.PartII



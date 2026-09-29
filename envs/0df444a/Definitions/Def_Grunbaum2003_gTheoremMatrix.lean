-- Prove2me | Definitions.Def_Grunbaum2003_gTheoremMatrix
-- name    : Grunbaum2003_gTheoremMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:21:35.134681+00:00
-- url     : https://prove2.me/theorems/3645ff44-ed13-473c-8bb3-aebf15f31ad6
-- title:
--   Björner g-theorem matrix
-- statement:
--   The integer matrix entry M_d(j,k) = binom(d+1−j,d+1−k) − binom(j,d+1−k) used in Björner’s formulation of the g-theorem.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §10.6, printed p. 198a / PDF p. 235; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
namespace Grunbaum2003

/-- Björner's matrix M_d, §10.6 p.198a/PDF235. Its row index j ranges
from 0 to floor(d/2), and column k from 0 to d. Subtraction is in ℤ. -/
def gTheoremMatrix (d j k : ℕ) : ℤ :=
  (Nat.choose (d + 1 - j) (d + 1 - k) : ℤ) -
    (Nat.choose j (d + 1 - k) : ℤ)

end Grunbaum2003



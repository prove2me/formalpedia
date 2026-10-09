-- Prove2me | Definitions.Def_RamanujanNotebooks_ch38_ch38UnitPow
-- name    : RamanujanNotebooks_ch38_ch38UnitPow
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T08:50:28.562128+00:00
-- url     : https://prove2.me/theorems/c296c4a7-e755-42e8-b07e-9ef0688f145e
-- title:
--   Ramanujan's Notebooks, Part V, Ch. 38: ch38UnitPow
-- statement:
--   The complex power `d^{2nπi/log c} = exp(2nπi · log d / log c)` for real `c > 1`, `d > 0` and
--   an integer `n`, a point of the unit circle (Entries 11–13, pp. 536–540).
--   Domain: `c > 1` (so `log c > 0`) and `d > 0`.
--   Outside: for `c = 1` Lean divides by `0`; for `d ≤ 0` the real logarithm is Lean's convention;
--   not used.
--   Reference: `ch38UnitPow c c n = 1`; `ch38UnitPow 3 2 1 = exp(2πi log 3/log 2)`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part V (Springer, 1998), Chapter 38.

import Mathlib

namespace RamanujanNotebooks

/-- The complex power `d^{2nπi/log c} = exp(2nπi · log d / log c)` for real `c > 1`, `d > 0` and
an integer `n`, a point of the unit circle (Entries 11–13, pp. 536–540).
Domain: `c > 1` (so `log c > 0`) and `d > 0`.
Outside: for `c = 1` Lean divides by `0`; for `d ≤ 0` the real logarithm is Lean's convention;
not used.
Reference: `ch38UnitPow c c n = 1`; `ch38UnitPow 3 2 1 = exp(2πi log 3/log 2)`. -/
noncomputable def ch38UnitPow (d c : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (2 * (n : ℂ) * (Real.pi : ℂ) * Complex.I * ((Real.log d : ℝ) : ℂ)
    / ((Real.log c : ℝ) : ℂ))

end RamanujanNotebooks



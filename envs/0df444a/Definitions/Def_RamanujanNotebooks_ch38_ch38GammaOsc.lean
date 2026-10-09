-- Prove2me | Definitions.Def_RamanujanNotebooks_ch38_ch38GammaOsc
-- name    : RamanujanNotebooks_ch38_ch38GammaOsc
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T08:53:38.115993+00:00
-- url     : https://prove2.me/theorems/70ad5ede-9108-4a7f-9b6f-30ae3cfcf4ca
-- title:
--   Ramanujan's Notebooks, Part V, Ch. 38: ch38GammaOsc
-- statement:
--   The term `Γ(-2nπi/log c) · x^{2nπi/log c}` of the oscillating series in (11.2), (12.1) and
--   (13.1) (pp. 536–540), for real `c > 1`, `x > 0` and a nonzero integer `n`; the power of `x` is
--   `ch38UnitPow x c n`.
--   Domain: `c > 1`, `x > 0`, `n ≠ 0` (the argument of `Γ` is then a nonzero purely imaginary
--   number, not a pole).
--   Outside: `n = 0` is the pole `Γ(0)`, where Mathlib's value has no meaning; not used.
--   Reference: `|ch38GammaOsc c x n|² = (log c) / (2 n sinh(2π² n/log c))` for `n > 0`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part V (Springer, 1998), Chapter 38.

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch38_ch38UnitPow

namespace RamanujanNotebooks

/-- The term `Γ(-2nπi/log c) · x^{2nπi/log c}` of the oscillating series in (11.2), (12.1) and
(13.1) (pp. 536–540), for real `c > 1`, `x > 0` and a nonzero integer `n`; the power of `x` is
`ch38UnitPow x c n`.
Domain: `c > 1`, `x > 0`, `n ≠ 0` (the argument of `Γ` is then a nonzero purely imaginary
number, not a pole).
Outside: `n = 0` is the pole `Γ(0)`, where Mathlib's value has no meaning; not used.
Reference: `|ch38GammaOsc c x n|² = (log c) / (2 n sinh(2π² n/log c))` for `n > 0`. -/
noncomputable def ch38GammaOsc (c x : ℝ) (n : ℤ) : ℂ :=
  Complex.Gamma (-(2 * (n : ℂ) * (Real.pi : ℂ) * Complex.I) / ((Real.log c : ℝ) : ℂ))
    * ch38UnitPow x c n

end RamanujanNotebooks



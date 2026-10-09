-- Prove2me | Definitions.Def_RamanujanNotebooks_ch28_ch28ReciprocalI
-- name    : RamanujanNotebooks_ch28_ch28ReciprocalI
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T03:16:40.72746+00:00
-- url     : https://prove2.me/theorems/c02ac0af-040d-4bee-9f41-10b798a16040
-- title:
--   Ramanujan's Notebooks, Part IV, Ch. 28: ch28ReciprocalI
-- statement:
--   The function `I(α) = α^{-1/4} (1 + 4α ∫_0^∞ x e^{-αx²} / (e^{2πx} - 1) dx)` of (4.1),
--   p. 291 (Entries 4 and 5).
--   Domain: `α > 0` (the book's); the integrand is bounded near `0` (limit `1/(2π)`) and decays
--   exponentially, so the integral converges absolutely.
--   Outside: for `α = 0` the factor `α^{-1/4}` is `0 ^ (-1/4) = 0` in Lean; for `α < 0` the
--   integrand is still integrable, but `α^{-1/4}` is Lean's `Real.rpow` of a negative base and
--   the value has no meaning.
--   Reference: `I(π) = 1.06827437054194412034358…`, `I(1) = I(π²) = 1.15299380521989158081997…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 28.

import Mathlib

namespace RamanujanNotebooks

/-- The function `I(α) = α^{-1/4} (1 + 4α ∫_0^∞ x e^{-αx²} / (e^{2πx} - 1) dx)` of (4.1),
p. 291 (Entries 4 and 5).
Domain: `α > 0` (the book's); the integrand is bounded near `0` (limit `1/(2π)`) and decays
exponentially, so the integral converges absolutely.
Outside: for `α = 0` the factor `α^{-1/4}` is `0 ^ (-1/4) = 0` in Lean; for `α < 0` the
integrand is still integrable, but `α^{-1/4}` is Lean's `Real.rpow` of a negative base and
the value has no meaning.
Reference: `I(π) = 1.06827437054194412034358…`, `I(1) = I(π²) = 1.15299380521989158081997…`. -/
noncomputable def ch28ReciprocalI (α : ℝ) : ℝ :=
  α ^ (-(1 / 4 : ℝ))
    * (1 + 4 * α * ∫ x in Set.Ioi (0 : ℝ),
        x * Real.exp (-(α * x ^ 2)) / (Real.exp (2 * Real.pi * x) - 1))

end RamanujanNotebooks



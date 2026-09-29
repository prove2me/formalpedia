-- Prove2me | Definitions.Def_MetodosNumericos_errosDefs
-- name    : MetodosNumericos_errosDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T16:32:55.601688+00:00
-- url     : https://prove2.me/theorems/f23233ee-36f3-4958-8eef-276151f74d0d
-- title:
--   Decimal exponent, truncated rounding and symmetric rounding
-- statement:
--   The decimal exponent $e$ of a nonzero real, characterized by $0.1 \\le |x|/10^e < 1$, together with truncated rounding and symmetric rounding of $x$ to $t$ digits of the normalized mantissa.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 2, §2.3.5 p. 21 and §2.4.1–2.4.2, pp. 21–22.

import Mathlib

namespace MetodosNumericos

/-- The decimal exponent of a nonzero real number: the integer `e` for which
`0.1 ≤ |x| / 10 ^ e < 1`, i.e. the exponent of the normalized decimal form
`x = f × 10 ^ e` with `0.1 ≤ |f| < 1`. -/
noncomputable def decExp (x : ℝ) : ℤ := ⌊Real.logb 10 |x|⌋ + 1

/-- Truncated rounding (arredondamento truncado) of `x` to `t` decimal digits of the
normalized mantissa: the digits after the `t`-th are discarded. -/
noncomputable def truncRound (t : ℕ) (x : ℝ) : ℝ :=
  (⌊x * (10 : ℝ) ^ ((t : ℤ) - decExp x)⌋ : ℝ) * (10 : ℝ) ^ (decExp x - (t : ℤ))

/-- Symmetric rounding (arredondamento simétrico) of `x` to `t` decimal digits of the
normalized mantissa: the mantissa is rounded to the nearest multiple of `10 ^ (e - t)`,
half being rounded away from the truncated value. -/
noncomputable def symRound (t : ℕ) (x : ℝ) : ℝ :=
  (⌊x * (10 : ℝ) ^ ((t : ℤ) - decExp x) + 1 / 2⌋ : ℝ) * (10 : ℝ) ^ (decExp x - (t : ℤ))

end MetodosNumericos



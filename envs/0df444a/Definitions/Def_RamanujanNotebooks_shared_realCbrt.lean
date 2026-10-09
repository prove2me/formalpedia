-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_realCbrt
-- name    : RamanujanNotebooks_shared_realCbrt
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:15.798848+00:00
-- url     : https://prove2.me/theorems/a4da090f-8b80-4b80-be21-44d277c99d6e
-- title:
--   Ramanujan's Notebooks, shared: realCbrt
-- statement:
--   Real cube root: the unique real `y` with `y ^ 3 = x`, i.e. `x ^ (1/3)` for `x ≥ 0` and
--   `-((-x) ^ (1/3))` for `x < 0`.  This is the meaning of every real cube root sign `∛` and
--   every exponent `1/3` applied to a real number in the series, unless an entry says otherwise.
--   `Real.rpow` alone is not used because for a negative base it returns
--   `|x| ^ (1/3) * cos (π / 3)`, which is not a cube root.
--
--   Domain: all real `x`; total, no junk value: `(realCbrt x) ^ 3 = x` for every real `x`, the
--   function is odd, strictly increasing and continuous.
--   Reference: `realCbrt 8 = 2`, `realCbrt (-8) = -2`, `realCbrt 0 = 0`,
--   `realCbrt 2 = 1.2599210498948731647672…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

namespace RamanujanNotebooks

/-- Real cube root: the unique real `y` with `y ^ 3 = x`, i.e. `x ^ (1/3)` for `x ≥ 0` and
`-((-x) ^ (1/3))` for `x < 0`.  This is the meaning of every real cube root sign `∛` and
every exponent `1/3` applied to a real number in the series, unless an entry says otherwise.
`Real.rpow` alone is not used because for a negative base it returns
`|x| ^ (1/3) * cos (π / 3)`, which is not a cube root.

Domain: all real `x`; total, no junk value: `(realCbrt x) ^ 3 = x` for every real `x`, the
function is odd, strictly increasing and continuous.
Reference: `realCbrt 8 = 2`, `realCbrt (-8) = -2`, `realCbrt 0 = 0`,
`realCbrt 2 = 1.2599210498948731647672…`. -/
noncomputable def realCbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ ((1 : ℝ) / 3) else -((-x) ^ ((1 : ℝ) / 3))

end RamanujanNotebooks



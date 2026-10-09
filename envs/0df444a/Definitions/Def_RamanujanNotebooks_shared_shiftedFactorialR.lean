-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_shiftedFactorialR
-- name    : RamanujanNotebooks_shared_shiftedFactorialR
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:03.719808+00:00
-- url     : https://prove2.me/theorems/bd1cab17-f8a4-4167-8438-e63acc9a6ee8
-- title:
--   Ramanujan's Notebooks, shared: shiftedFactorialR
-- statement:
--   Real shifted factorial `(a)_k = a (a + 1) ⋯ (a + k - 1)` for real `a`; the real
--   counterpart of `shiftedFactorial`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Real shifted factorial `(a)_k = a (a + 1) ⋯ (a + k - 1)` for real `a`; the real
counterpart of `shiftedFactorial`. -/
def shiftedFactorialR (a : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (a + (j : ℝ))

end RamanujanNotebooks

end



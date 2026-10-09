-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_eisP
-- name    : RamanujanNotebooks_shared_eisP
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:21.52029+00:00
-- url     : https://prove2.me/theorems/e714af7a-90e1-4bdd-a6f5-dc0ec8d73436
-- title:
--   Ramanujan's Notebooks, shared: eisP
-- statement:
--   Ramanujan's `L = P(q) = 1 - 24 ∑_{k ≥ 1} k q^k / (1 - q^k)` (Part II, p. 318; called
--   `L` in the notebooks and by Berndt, `P` in Ramanujan's published paper; Part III, p. 455),
--   written with `k = m + 1`.  Domain: `‖q‖ < 1`.
--
--   The argument is `q`: with `q = e^{-2y}` the series (1.1) of Part III, Chapter 21, without
--   its term `-3/y`, is `eisP` at `e^{-2y}` (stated with `Real.exp`).
--   Reference: `1 - 24q - 72q^2 - 96q^3 - 168q^4 - …`, `P(1/5) = -7.7849042257746685160…`,
--   `P(e^{-2π}) = 3/π`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Ramanujan's `L = P(q) = 1 - 24 ∑_{k ≥ 1} k q^k / (1 - q^k)` (Part II, p. 318; called
`L` in the notebooks and by Berndt, `P` in Ramanujan's published paper; Part III, p. 455),
written with `k = m + 1`.  Domain: `‖q‖ < 1`.

The argument is `q`: with `q = e^{-2y}` the series (1.1) of Part III, Chapter 21, without
its term `-3/y`, is `eisP` at `e^{-2y}` (stated with `Real.exp`).
Reference: `1 - 24q - 72q^2 - 96q^3 - 168q^4 - …`, `P(1/5) = -7.7849042257746685160…`,
`P(e^{-2π}) = 3/π`. -/
def eisP (q : ℂ) : ℂ :=
  1 - 24 * (∑' m : ℕ, ((m : ℂ) + 1) * q ^ (m + 1) / (1 - q ^ (m + 1)))

end RamanujanNotebooks

end



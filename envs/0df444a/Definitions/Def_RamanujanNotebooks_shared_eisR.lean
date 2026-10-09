-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_eisR
-- name    : RamanujanNotebooks_shared_eisR
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:01.899988+00:00
-- url     : https://prove2.me/theorems/d8238e9e-b414-4473-844c-505a053a5d50
-- title:
--   Ramanujan's Notebooks, shared: eisR
-- statement:
--   Ramanujan's `N = R(q) = 1 - 504 ∑_{k ≥ 1} k^5 q^k / (1 - q^k)` (Part II, p. 318; Part
--   III, (1.3), p. 455).  Domain: `‖q‖ < 1`.  (Not the Rogers–Ramanujan continued fraction
--   `R(q)` of Part V, Chapter 32.)
--   Reference: `1 - 504q - 16632q^2 - 122976q^3 - …`, `R(1/5) = -3540.2492571969512213…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Ramanujan's `N = R(q) = 1 - 504 ∑_{k ≥ 1} k^5 q^k / (1 - q^k)` (Part II, p. 318; Part
III, (1.3), p. 455).  Domain: `‖q‖ < 1`.  (Not the Rogers–Ramanujan continued fraction
`R(q)` of Part V, Chapter 32.)
Reference: `1 - 504q - 16632q^2 - 122976q^3 - …`, `R(1/5) = -3540.2492571969512213…`. -/
def eisR (q : ℂ) : ℂ :=
  1 - 504 * (∑' m : ℕ, ((m : ℂ) + 1) ^ 5 * q ^ (m + 1) / (1 - q ^ (m + 1)))

end RamanujanNotebooks

end



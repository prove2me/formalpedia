-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_eisQ
-- name    : RamanujanNotebooks_shared_eisQ
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:17:59.735363+00:00
-- url     : https://prove2.me/theorems/8d8d5c1b-2020-4d20-b73d-9abffe69557f
-- title:
--   Ramanujan's Notebooks, shared: eisQ
-- statement:
--   Ramanujan's `M = Q(q) = 1 + 240 ∑_{k ≥ 1} k^3 q^k / (1 - q^k)` (Part II, p. 318; Part
--   III, (1.2), p. 455).  Domain: `‖q‖ < 1`.
--   Reference: `1 + 240q + 2160q^2 + 6720q^3 + …`, `Q(1/5) = 232.28574880641123875…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Ramanujan's `M = Q(q) = 1 + 240 ∑_{k ≥ 1} k^3 q^k / (1 - q^k)` (Part II, p. 318; Part
III, (1.2), p. 455).  Domain: `‖q‖ < 1`.
Reference: `1 + 240q + 2160q^2 + 6720q^3 + …`, `Q(1/5) = 232.28574880641123875…`. -/
def eisQ (q : ℂ) : ℂ :=
  1 + 240 * (∑' m : ℕ, ((m : ℂ) + 1) ^ 3 * q ^ (m + 1) / (1 - q ^ (m + 1)))

end RamanujanNotebooks

end



-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_qPochInf
-- name    : RamanujanNotebooks_shared_qPochInf
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:10.033714+00:00
-- url     : https://prove2.me/theorems/badc5649-23fa-4973-bd97-4d1d884fb36f
-- title:
--   Ramanujan's Notebooks, shared: qPochInf
-- statement:
--   Infinite q-Pochhammer symbol `(a)_∞ = (a; q)_∞ = ∏_{k ≥ 0} (1 - a q^k)` (Part III,
--   p. 12; p. 88).
--
--   Domain: `‖q‖ < 1`, every `a`; the product converges absolutely and equals
--   `lim_n (a; q)_n`.  It vanishes exactly when `a q^k = 1` for some `k ≥ 0`.
--   Outside: for `‖q‖ ≥ 1` the product is in general not multipliable and Lean returns `1`
--   (exception: `a = 0`, value `1`).
--   Reference: `(1/2; 1/5)_∞ = 0.43879683720363853126…`, `(0; q)_∞ = 1`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Infinite q-Pochhammer symbol `(a)_∞ = (a; q)_∞ = ∏_{k ≥ 0} (1 - a q^k)` (Part III,
p. 12; p. 88).

Domain: `‖q‖ < 1`, every `a`; the product converges absolutely and equals
`lim_n (a; q)_n`.  It vanishes exactly when `a q^k = 1` for some `k ≥ 0`.
Outside: for `‖q‖ ≥ 1` the product is in general not multipliable and Lean returns `1`
(exception: `a = 0`, value `1`).
Reference: `(1/2; 1/5)_∞ = 0.43879683720363853126…`, `(0; q)_∞ = 1`. -/
def qPochInf (a q : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - a * q ^ k)

end RamanujanNotebooks

end



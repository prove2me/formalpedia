-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_thetaPsi
-- name    : RamanujanNotebooks_shared_thetaPsi
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:26.002397+00:00
-- url     : https://prove2.me/theorems/60698144-f7fb-497b-b0ba-bb1e9b0091b1
-- title:
--   Ramanujan's Notebooks, shared: thetaPsi
-- statement:
--   Ramanujan's `ψ(q) = f(q, q^3) = ∑_{k ≥ 0} q^{k(k+1)/2}` (Entry 22(ii), Part III, p. 36).
--
--   Domain: `‖q‖ < 1`.  There `ψ(q) = (q^2; q^2)_∞ / (q; q^2)_∞`.  Outside: `0`.
--   Reference: `1 + q + q^3 + q^6 + q^10 + …`, `ψ(1/5) = 1.2080641024327700971…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Ramanujan's `ψ(q) = f(q, q^3) = ∑_{k ≥ 0} q^{k(k+1)/2}` (Entry 22(ii), Part III, p. 36).

Domain: `‖q‖ < 1`.  There `ψ(q) = (q^2; q^2)_∞ / (q; q^2)_∞`.  Outside: `0`.
Reference: `1 + q + q^3 + q^6 + q^10 + …`, `ψ(1/5) = 1.2080641024327700971…`. -/
def thetaPsi (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n * (n + 1) / 2)

end RamanujanNotebooks

end



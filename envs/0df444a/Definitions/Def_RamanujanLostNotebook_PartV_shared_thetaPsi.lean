-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPsi
-- name    : RamanujanLostNotebook_PartV_shared_thetaPsi
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:06:11.873572+00:00
-- url     : https://prove2.me/theorems/8202ddc3-2fe8-4f0d-8767-e900d9878610
-- title:
--   Ramanujan's Lost Notebook Part V, shared: thetaPsi
-- statement:
--   Ramanujan's `ψ(q) = f(q, q^3) = ∑_{n ≥ 0} q^{n(n+1)/2}` ((2.3.6), p. 8; (3.1.15),
--   p. 18; (4.1.2), p. 35).
--
--   Domain: `‖q‖ < 1`.  There `ψ(q) = (q^2; q^2)_∞ / (q; q^2)_∞`.  Outside: `0`.
--   Reference: `1 + q + q^3 + q^6 + q^10 + …`, `ψ(1/5) = 1.2080641024327700971…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Ramanujan's `ψ(q) = f(q, q^3) = ∑_{n ≥ 0} q^{n(n+1)/2}` ((2.3.6), p. 8; (3.1.15),
p. 18; (4.1.2), p. 35).

Domain: `‖q‖ < 1`.  There `ψ(q) = (q^2; q^2)_∞ / (q; q^2)_∞`.  Outside: `0`.
Reference: `1 + q + q^3 + q^6 + q^10 + …`, `ψ(1/5) = 1.2080641024327700971…`. -/
def thetaPsi (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n * (n + 1) / 2)

end RamanujanLostNotebook.PartV

end



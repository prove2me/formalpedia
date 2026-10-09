-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_thetaPhi
-- name    : RamanujanNotebooks_shared_thetaPhi
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:25.951479+00:00
-- url     : https://prove2.me/theorems/41ead90d-ad27-4b12-9429-2eb73e54d02d
-- title:
--   Ramanujan's Notebooks, shared: thetaPhi
-- statement:
--   Ramanujan's `φ(q) = f(q, q) = ∑_{k ∈ ℤ} q^{k^2}` (Entry 22(i), Part III, p. 36; (3.1),
--   p. 98).  The argument is `q` itself: Berndt's `φ(-q)` is `thetaPhi (-q)`.
--
--   Domain: `‖q‖ < 1`.  There `φ(-q) = (q; q)_∞ / (-q; q)_∞` ((22.4), p. 37).  Outside: `0`.
--   Reference: `1 + 2q + 2q^4 + 2q^9 + …`, `φ(1/5) = 1.4032010240131072067…`,
--   `φ(e^{-π}) = π^{1/4} / Γ(3/4)`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Ramanujan's `φ(q) = f(q, q) = ∑_{k ∈ ℤ} q^{k^2}` (Entry 22(i), Part III, p. 36; (3.1),
p. 98).  The argument is `q` itself: Berndt's `φ(-q)` is `thetaPhi (-q)`.

Domain: `‖q‖ < 1`.  There `φ(-q) = (q; q)_∞ / (-q; q)_∞` ((22.4), p. 37).  Outside: `0`.
Reference: `1 + 2q + 2q^4 + 2q^9 + …`, `φ(1/5) = 1.4032010240131072067…`,
`φ(e^{-π}) = π^{1/4} / Γ(3/4)`. -/
def thetaPhi (q : ℂ) : ℂ :=
  ∑' n : ℤ, q ^ (n.natAbs ^ 2)

end RamanujanNotebooks

end



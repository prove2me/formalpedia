-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_shared_thetaPhi
-- name    : RamanujanLostNotebook_PartII_shared_thetaPhi
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:17:18.42213+00:00
-- url     : https://prove2.me/theorems/142259a6-ff3a-4ea4-b88a-da61da21b237
-- title:
--   Ramanujan's Lost Notebook Part II, shared: thetaPhi
-- statement:
--   Ramanujan's `φ(q) = f(q, q) = ∑_{n ∈ ℤ} q^{n^2}` ((8.1.2), p. 174), with the natural
--   exponent `n.natAbs ^ 2`.  Chapter 1 defines the same function at `-q`:
--   `φ(-q) := f(-q, -q) = ∑_{n ∈ ℤ} (-1)^n q^{n^2}` ((1.4.9), p. 17), which is `thetaPhi (-q)`.
--
--   Domain: `‖q‖ < 1`, where the series converges absolutely.  The product form
--   `φ(-q) = (q; q)_∞ / (-q; q)_∞` printed in (1.4.9) and the equality
--   `thetaPhi q = ramanujanTheta q q` are theorems, not part of the definition.
--   Totalization: for `‖q‖ ≥ 1` the terms do not tend to `0` and the value is `0`.  At `q = 0`
--   only the term `n = 0` survives (`0 ^ 0 = 1`) and the value is `1`.
--   Reference: Taylor expansion `1 + 2q + 2q^4 + 2q^9 + 2q^16 + …`;
--   `thetaPhi (1/5) = 1.4032010240131072067…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Ramanujan's `φ(q) = f(q, q) = ∑_{n ∈ ℤ} q^{n^2}` ((8.1.2), p. 174), with the natural
exponent `n.natAbs ^ 2`.  Chapter 1 defines the same function at `-q`:
`φ(-q) := f(-q, -q) = ∑_{n ∈ ℤ} (-1)^n q^{n^2}` ((1.4.9), p. 17), which is `thetaPhi (-q)`.

Domain: `‖q‖ < 1`, where the series converges absolutely.  The product form
`φ(-q) = (q; q)_∞ / (-q; q)_∞` printed in (1.4.9) and the equality
`thetaPhi q = ramanujanTheta q q` are theorems, not part of the definition.
Totalization: for `‖q‖ ≥ 1` the terms do not tend to `0` and the value is `0`.  At `q = 0`
only the term `n = 0` survives (`0 ^ 0 = 1`) and the value is `1`.
Reference: Taylor expansion `1 + 2q + 2q^4 + 2q^9 + 2q^16 + …`;
`thetaPhi (1/5) = 1.4032010240131072067…`. -/
def thetaPhi (q : ℂ) : ℂ :=
  ∑' n : ℤ, q ^ (n.natAbs ^ 2)

end RamanujanLostNotebook.PartII

end



-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPhi
-- name    : RamanujanLostNotebook_PartV_shared_thetaPhi
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:06:07.119328+00:00
-- url     : https://prove2.me/theorems/103cc7ce-1d3a-4070-bf98-11b3bfd0a9b8
-- title:
--   Ramanujan's Lost Notebook Part V, shared: thetaPhi
-- statement:
--   Ramanujan's `φ(q) = f(q, q) = ∑_{n ∈ ℤ} q^{n^2}` (the book defines it through
--   `φ(-q)`, (2.3.1), p. 8, and (3.1.14), p. 18; `φ(q) := f(q, q)` on p. 88).
--
--   Domain: `‖q‖ < 1`.  There `φ(-q) = (q; q)_∞ / (-q; q)_∞`.  Outside: `0`.
--   Reference: `1 + 2q + 2q^4 + 2q^9 + …`, `φ(1/5) = 1.4032010240131072067…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Ramanujan's `φ(q) = f(q, q) = ∑_{n ∈ ℤ} q^{n^2}` (the book defines it through
`φ(-q)`, (2.3.1), p. 8, and (3.1.14), p. 18; `φ(q) := f(q, q)` on p. 88).

Domain: `‖q‖ < 1`.  There `φ(-q) = (q; q)_∞ / (-q; q)_∞`.  Outside: `0`.
Reference: `1 + 2q + 2q^4 + 2q^9 + …`, `φ(1/5) = 1.4032010240131072067…`. -/
def thetaPhi (q : ℂ) : ℂ :=
  ∑' n : ℤ, q ^ (n.natAbs ^ 2)

end RamanujanLostNotebook.PartV

end



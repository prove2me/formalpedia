-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch02_crankProd
-- name    : RamanujanLostNotebook_PartIII_ch02_crankProd
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:16:50.164077+00:00
-- url     : https://prove2.me/theorems/e0647f83-c47b-4adf-aee0-90dc3ce8febb
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 2: crankProd
-- statement:
--   Ramanujan's crank product `F_a(q) = (q; q)_∞ / ((a q; q)_∞ (q/a; q)_∞)` ((2.1.14), p. 11).
--   With `a = ζ_5` it is the `F_5(q)` of (2.1.5), p. 10, and with `a = ζ_7` the `F_7(q)` of (2.1.28),
--   p. 14 (the book notes the clash of notation, p. 11).
--   Domain: `‖q‖ < 1`, `a ≠ 0`, and no factor `1 - a q^k`, `1 - q^k / a` (`k ≥ 1`) vanishes; for a
--   root of unity `a` and `‖q‖ < 1` all three products converge absolutely and the denominator is
--   nonzero.  Totalization: a zero denominator gives `x / 0 = 0`, never the book's object.
--   Reference: `crankProd a 0 = 1`; at `a = 1` it is `1 / (q; q)_∞`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 2.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Ramanujan's crank product `F_a(q) = (q; q)_∞ / ((a q; q)_∞ (q/a; q)_∞)` ((2.1.14), p. 11).
With `a = ζ_5` it is the `F_5(q)` of (2.1.5), p. 10, and with `a = ζ_7` the `F_7(q)` of (2.1.28),
p. 14 (the book notes the clash of notation, p. 11).
Domain: `‖q‖ < 1`, `a ≠ 0`, and no factor `1 - a q^k`, `1 - q^k / a` (`k ≥ 1`) vanishes; for a
root of unity `a` and `‖q‖ < 1` all three products converge absolutely and the denominator is
nonzero.  Totalization: a zero denominator gives `x / 0 = 0`, never the book's object.
Reference: `crankProd a 0 = 1`; at `a = 1` it is `1 / (q; q)_∞`. -/
def crankProd (a q : ℂ) : ℂ :=
  qPochInf q q / (qPochInf (a * q) q * qPochInf (q / a) q)

end RamanujanLostNotebook.PartIII

end



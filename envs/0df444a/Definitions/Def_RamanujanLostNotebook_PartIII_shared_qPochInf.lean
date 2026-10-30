-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf
-- name    : RamanujanLostNotebook_PartIII_shared_qPochInf
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:21:21.793302+00:00
-- url     : https://prove2.me/theorems/4516c535-ec6d-42f6-9577-18fedd9c0b76
-- title:
--   Ramanujan's Lost Notebook Part III, shared: qPochInf
-- statement:
--   Infinite q-Pochhammer symbol `(a; q)_∞ = lim_{n → ∞} (a; q)_n = ∏_{k ≥ 0} (1 - a q^k)` for
--   `|q| < 1` (display before (2.1.1), p. 9; Section 8.1, p. 217; as a product on p. 181),
--   written with Mathlib's unconditional product `∏'` over `ℕ`.
--
--   Domain: `‖q‖ < 1` and every complex `a`.  There `∑_k ‖a q^k‖ < ∞`, so the product converges
--   absolutely, `∏'` is its classical value, it is the limit of `qPoch a q n`, and it vanishes
--   exactly when `a q^k = 1` for some `k ≥ 0`.
--   Totalization: for `‖q‖ ≥ 1` the value is whatever Mathlib's `tprod` assigns (`1` for a
--   non-multipliable family, but `0` when some factor is exactly `0`, e.g. `a = q = 1`), never the
--   book's object.  `a = 0` gives `1` for every `q`.
--   Reference: `qPochInf (1/2) (1/5) = 0.43879683720363853126…`; `(q; q)_∞` is `eulerF q`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Infinite q-Pochhammer symbol `(a; q)_∞ = lim_{n → ∞} (a; q)_n = ∏_{k ≥ 0} (1 - a q^k)` for
`|q| < 1` (display before (2.1.1), p. 9; Section 8.1, p. 217; as a product on p. 181),
written with Mathlib's unconditional product `∏'` over `ℕ`.

Domain: `‖q‖ < 1` and every complex `a`.  There `∑_k ‖a q^k‖ < ∞`, so the product converges
absolutely, `∏'` is its classical value, it is the limit of `qPoch a q n`, and it vanishes
exactly when `a q^k = 1` for some `k ≥ 0`.
Totalization: for `‖q‖ ≥ 1` the value is whatever Mathlib's `tprod` assigns (`1` for a
non-multipliable family, but `0` when some factor is exactly `0`, e.g. `a = q = 1`), never the
book's object.  `a = 0` gives `1` for every `q`.
Reference: `qPochInf (1/2) (1/5) = 0.43879683720363853126…`; `(q; q)_∞` is `eulerF q`. -/
def qPochInf (a q : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - a * q ^ k)

end RamanujanLostNotebook.PartIII

end



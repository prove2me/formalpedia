-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf
-- name    : RamanujanLostNotebook_PartII_shared_qPochInf
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:17:25.447111+00:00
-- url     : https://prove2.me/theorems/df8c4d5f-8f1d-4cee-97b3-e9c8aead1b3f
-- title:
--   Ramanujan's Lost Notebook Part II, shared: qPochInf
-- statement:
--   Infinite q-Pochhammer symbol `(a; q)_∞ = lim_{n → ∞} (a; q)_n = ∏_{k ≥ 0} (1 - a q^k)` for
--   `|q| < 1` ((1.1.4), p. 5), written with Mathlib's unconditional product `∏'` over `ℕ`.
--
--   Domain: `‖q‖ < 1` and every complex `a`.  There `∑_k ‖a q^k‖ < ∞`, so the product converges
--   absolutely, `∏'` is its classical value, it is the limit of `qPoch a q n`, and it vanishes
--   exactly when `a q^k = 1` for some `k ≥ 0`.
--   Totalization: for `‖q‖ ≥ 1` the value is whatever Mathlib's `tprod` assigns (`1` for a
--   non-multipliable family, but `0` when some factor is exactly `0`, e.g. `a = q = 1`), never the
--   book's object.  `a = 0` gives `1` for every `q`.
--   Reference: `qPochInf (1/2) (1/5) = 0.43879683720363853126…`; `(q; q)_∞` is `eulerF q`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Infinite q-Pochhammer symbol `(a; q)_∞ = lim_{n → ∞} (a; q)_n = ∏_{k ≥ 0} (1 - a q^k)` for
`|q| < 1` ((1.1.4), p. 5), written with Mathlib's unconditional product `∏'` over `ℕ`.

Domain: `‖q‖ < 1` and every complex `a`.  There `∑_k ‖a q^k‖ < ∞`, so the product converges
absolutely, `∏'` is its classical value, it is the limit of `qPoch a q n`, and it vanishes
exactly when `a q^k = 1` for some `k ≥ 0`.
Totalization: for `‖q‖ ≥ 1` the value is whatever Mathlib's `tprod` assigns (`1` for a
non-multipliable family, but `0` when some factor is exactly `0`, e.g. `a = q = 1`), never the
book's object.  `a = 0` gives `1` for every `q`.
Reference: `qPochInf (1/2) (1/5) = 0.43879683720363853126…`; `(q; q)_∞` is `eulerF q`. -/
def qPochInf (a q : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - a * q ^ k)

end RamanujanLostNotebook.PartII

end



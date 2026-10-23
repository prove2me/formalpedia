-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf
-- name    : RamanujanLostNotebook_PartV_shared_qPochInf
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:05:13.681762+00:00
-- url     : https://prove2.me/theorems/f5f5b343-58c3-48b0-9093-02458dc58ae7
-- title:
--   Ramanujan's Lost Notebook Part V, shared: qPochInf
-- statement:
--   Infinite q-Pochhammer symbol `(a; q)_∞ = ∏_{k ≥ 0} (1 - a q^k)` ((1.0.2), p. 1).
--
--   Domain: `‖q‖ < 1`, every `a`; the product converges absolutely and equals
--   `lim_n (a; q)_n`.  It vanishes exactly when `a q^k = 1` for some `k ≥ 0`.
--   Outside: for `‖q‖ ≥ 1` the product is in general not multipliable and Lean returns `1`
--   (exception: `a = 0`, value `1`).
--   Reference: `(1/2; 1/5)_∞ = 0.43879683720363853126…`, `(0; q)_∞ = 1`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Infinite q-Pochhammer symbol `(a; q)_∞ = ∏_{k ≥ 0} (1 - a q^k)` ((1.0.2), p. 1).

Domain: `‖q‖ < 1`, every `a`; the product converges absolutely and equals
`lim_n (a; q)_n`.  It vanishes exactly when `a q^k = 1` for some `k ≥ 0`.
Outside: for `‖q‖ ≥ 1` the product is in general not multipliable and Lean returns `1`
(exception: `a = 0`, value `1`).
Reference: `(1/2; 1/5)_∞ = 0.43879683720363853126…`, `(0; q)_∞ = 1`. -/
def qPochInf (a q : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - a * q ^ k)

end RamanujanLostNotebook.PartV

end



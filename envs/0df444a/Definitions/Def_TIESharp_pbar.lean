-- Prove2me | Definitions.Def_TIESharp_pbar
-- name    : TIESharp_pbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:58.428433+00:00
-- url     : https://prove2.me/theorems/54ac4fc8-4d04-4ecf-be82-47b4b3485490
-- title:
--   Normalized expected payment $\bar p^m_i(t)$
-- statement:
--   Holding the other machines' bids fixed, machine $i$'s **normalized expected payment** is its payment minus its value when it reports zero on every job:
--   $$\bar p^m_i(t)=p^m_i(t)-p^m_i(0,t_{-i}).$$
--   The subtracted term does not depend on machine $i$'s report, so all incentive comparisons (2.1) are unchanged.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §4, p.13

import Mathlib
import Definitions.Def_TIESharp_Family

set_option autoImplicit false

namespace TIESharp

/-- The **normalized expected payment** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, §4, p.13): `p̄^m_i(t) = p^m_i(t) − p^m_i(0, t_{-i})`, the payment
minus its value when machine `i` reports zero on all jobs.

**Formalization Note.** `(0, t_{-i})` is `Function.update t i 0`. -/
def pbar {n : ℕ} (F : Family n) (m : ℕ) (t : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  F.pay m t i - F.pay m (Function.update t i 0) i

end TIESharp



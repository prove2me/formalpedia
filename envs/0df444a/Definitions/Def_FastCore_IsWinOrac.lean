-- Prove2me | Definitions.Def_FastCore_IsWinOrac
-- name    : FastCore_IsWinOrac
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:50.851993+00:00
-- url     : https://prove2.me/theorems/2914a176-cd94-4efa-afb9-08a9f58585ef
-- title:
--   WIN-ORAC specification
-- statement:
--   An oracle $q$ **meets the specification of WIN-ORAC** for the bids $\{b_i\}$ if, for all truncations $\pi\ge0$, its answer $q(\pi)$ consists of
--
--   1. the max welfare with truncated bids, $w(N,\{\max(b_i(.)-\pi_i,0)\})$, and
--   2. a winning set for the truncated bids, chosen among the zero-free winner sets.
--
--   **Formalization Note** The specification is required only at $\pi\ge0$. This is a weaker hypothesis than requiring it everywhere, and Algorithm 1 queries only such points. Definition 6's `NULL` does not arise, because a zero-free winner set always exists: strip the zero-value bundles from any optimal allocation.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 6, p.14

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_FastCore_w
import Definitions.Def_FastCore_trunc
import Definitions.Def_FastCore_IsZeroFreeWinnerSet
import Definitions.Def_FastCore_Oracle

namespace FastCore

/-- `q` meets the specification of WIN-ORAC for the bids `b` (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 6, p.14): on
truncations `π ≥ 0` it returns the max welfare with truncated bids and a winning set for them.

**Formalization Note.** The specification is required at `π ≥ 0` only, which is a weaker hypothesis
than at every `π`, and the algorithm queries only such `π`. The winning set obeys the zero-value
convention of p.10 (`IsZeroFreeWinnerSet`). `NULL` does not arise, since such a set always exists. -/
def IsWinOrac {n m : ℕ} (b : Bids n m) (q : Oracle n) : Prop :=
  ∀ π : Fin n → ℝ, (∀ i, 0 ≤ π i) →
    (q π).1 = w (trunc b π) Finset.univ ∧ IsZeroFreeWinnerSet (trunc b π) (q π).2

end FastCore



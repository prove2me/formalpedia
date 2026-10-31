-- Prove2me | Definitions.Def_FastCore_trunc
-- name    : FastCore_trunc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:58.250758+00:00
-- url     : https://prove2.me/theorems/427a3d0f-6193-4567-b908-2f1cf9ab70b8
-- title:
--   Truncated bids $\max(b_i(.)-\pi_i,0)$
-- statement:
--   Given offsets $\{\pi_i\}_{i\in N}$, the **truncated bids** (sincere bids) are
--
--   $$
--   A\mapsto \max\bigl(b_i(A)-\pi_i,\,0\bigr)\qquad (i\in N,\ A\subseteq[m]).
--   $$
--
--   These are the bids on which the winner determination oracle runs. For $\pi_i\ge 0$ they are again normalized.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §3.1, p.14

import Mathlib
import Definitions.Def_FastCore_Bids

namespace FastCore

/-- The bids truncated by the offsets `π`: `max(bᵢ(.) − πᵢ, 0)` (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §3.1, p.14). -/
noncomputable def trunc {n m : ℕ} (b : Bids n m) (π : Fin n → ℝ) : Bids n m :=
  fun i A => max (b i A - π i) 0

end FastCore



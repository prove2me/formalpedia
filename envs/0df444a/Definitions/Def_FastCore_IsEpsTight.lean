-- Prove2me | Definitions.Def_FastCore_IsEpsTight
-- name    : FastCore_IsEpsTight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:00.860102+00:00
-- url     : https://prove2.me/theorems/771b8412-0549-40a8-a685-d96f97e5dfec
-- title:
--   $\epsilon$-tight core constraint
-- statement:
--   Given utilities $\{\pi_i\}_{i\in N}$, a subset $S\subseteq N$ is an **$\epsilon$-tight core constraint** if
--
--   $$
--   w(S)-\sum_{i\in S}\pi_i\ \le\ w(N)-\sum_{i\in N}\pi_i\ \le\ w(S)-\sum_{i\in S}\pi_i+\epsilon. \tag{4}
--   $$
--
--   For $\epsilon=0$ this is a tight core constraint.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 5, eq. (4), p.12

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_FastCore_w

namespace FastCore

/-- `S` is an `ε`-tight core constraint for `π` (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 5, eq. (4), p.12):
`w(S) − ∑_S πᵢ ≤ w(N) − ∑_N πᵢ ≤ w(S) − ∑_S πᵢ + ε`. -/
def IsEpsTight {n m : ℕ} (b : Bids n m) (π : Fin n → ℝ) (ε : ℝ) (S : Finset (Fin n)) : Prop :=
  w b S - ∑ i ∈ S, π i ≤ w b Finset.univ - ∑ i, π i ∧
    w b Finset.univ - ∑ i, π i ≤ w b S - ∑ i ∈ S, π i + ε

end FastCore



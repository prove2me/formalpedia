-- Prove2me | Definitions.Def_MaxWeightInstab_ExtArrivals
-- name    : MaxWeightInstab_ExtArrivals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:52.530593+00:00
-- url     : https://prove2.me/theorems/d095923d-a2a9-4116-b89a-3f6533e66152
-- title:
--   External arrivals of one time unit
-- statement:
--   In one time unit each of the $2J$ externally fed queues $\mathcal A_1,\dots,\mathcal A_J,\mathcal B_1,\dots,\mathcal B_J$ receives at most one external arrival. An arrival pattern is a vector of $2J$ bits; queues $\mathcal A_0$ and $\mathcal B_0$ receive no external arrivals.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, p.3

import Mathlib

namespace MaxWeightInstab

/-- The external arrivals of one time unit in the network of Figure 1 (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.3): "over each
time unit, there is at most 1 external arrival at each queue". `e (Sum.inl j) = true` means one
arrival at `𝒜_{j+1}`, `e (Sum.inr j) = true` one arrival at `ℬ_{j+1}` (`j = 0, …, J−1`). Queues
`𝒜₀` and `ℬ₀` receive no external arrivals. -/
abbrev ExtArrivals (J : ℕ) : Type := Fin J ⊕ Fin J → Bool

end MaxWeightInstab



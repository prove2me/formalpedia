-- Prove2me | Definitions.Def_FastCore_bump
-- name    : FastCore_bump
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:43.513314+00:00
-- url     : https://prove2.me/theorems/d2a7b326-9e89-479d-a31d-8eed2517840e
-- title:
--   Uniform increase on a set of bidders
-- statement:
--   For a vector $\pi$, a set $S\subseteq N$ and $\Delta\in\mathbb R$, this is the vector with coordinates $\pi_i+\Delta$ for $i\in S$ and $\pi_i$ otherwise. Core-Search uses it for $\tilde\pi$, $\bar\pi$ and $\underline\pi$.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Procedure 2, lines 4 and 9, p.16

import Mathlib

namespace FastCore

/-- The uniform increase of Core-Search (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Procedure 2, lines 4 and 9, p.16): `πᵢ + Δ` for
`i ∈ S` and `πᵢ` otherwise. -/
def bump {n : ℕ} (π : Fin n → ℝ) (S : Finset (Fin n)) (Δ : ℝ) : Fin n → ℝ :=
  fun i => if i ∈ S then π i + Δ else π i

end FastCore



-- Prove2me | Definitions.Def_FastCore_InCore
-- name    : FastCore_InCore
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:54.593982+00:00
-- url     : https://prove2.me/theorems/31102eda-1bbc-4338-9b5e-21fd03b96e54
-- title:
--   Core point in utility space
-- statement:
--   A utility vector $\{\pi_i\}_{i\in N}$ is **in the core** with respect to the bids if $\pi_i\ge 0$ for all $i$ and no coalition blocks:
--
--   $$
--   w(N)-\sum_{i\in N}\pi_i\ \ge\ w(S)-\sum_{i\in S}\pi_i\qquad\text{for all } S\subseteq N.
--   $$
--
--   This is equation (3), the form of Definition 2 used by every statement of the paper.
--
--   **Formalization Note** The seller's utility $\pi_0$ is not a separate coordinate. It is $w(N)-\sum_{i\in N}\pi_i$, which is the substitution that turns (2) into (3). The case $S=\emptyset$ gives $\pi_0\ge 0$.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 2 and eq. (3), pp.11–12

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_FastCore_w

namespace FastCore

/-- The utility vector `π` is in the core for the bids `b` (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 2 and eq. (3),
pp.11–12): `π ≥ 0` and `w(N) − ∑_N πᵢ ≥ w(S) − ∑_S πᵢ` for every `S ⊆ N`.

**Formalization Note.** The seller's revenue `π₀` is not a coordinate: it is `w(N) − ∑_N πᵢ`, the
substitution by which the paper rewrites (2) as (3). `S = ∅` gives `π₀ ≥ 0`. -/
def InCore {n m : ℕ} (b : Bids n m) (π : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ ∀ S, w b S - ∑ i ∈ S, π i ≤ w b Finset.univ - ∑ i, π i

end FastCore



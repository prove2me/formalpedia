-- Prove2me | Definitions.Def_Supermodularity_Games_BestJointResponse
-- name    : Supermodularity_Games_BestJointResponse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:30:18.342024+00:00
-- url     : https://prove2.me/theorems/94a6579c-294d-4064-8eec-d6bb0ad5d51c
-- title:
--   The best joint response correspondence Y(x) = ×_{i∈N} Y_i(x_{-i})
-- statement:
--   With $S$, $f$ and each player's best-response set $Y_i(x_{-i})$ as in
--   `BestResponse`, the **best joint response correspondence** is
--   $$
--   Y(x) \;=\; \prod_{i \in N} Y_i(x_{-i}),
--   $$
--   the set of joint strategies $x'$ whose $i$-th component is a best response for
--   player $i$ against $x_{-i}$, simultaneously for every player $i$.
--
--   **Formalization Note** `BestJointResponse S f x` is defined directly as
--   `{x' | ∀ i, x' i ∈ BestResponse S f i x}` rather than as a literal `Set.pi` product,
--   which is definitionally the same set for a dependent-function type and keeps the
--   later theorems' statements uncluttered.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 178, Chapter 4 (definition of the best joint response correspondence)

import Mathlib
import Definitions.Def_Supermodularity_Games_BestResponse

namespace Supermodularity.Games

/-- `BestJointResponse S f x` is the best joint response correspondence
`Y(x) = ×_{i ∈ N} Y_i(x_{-i})`: the set of joint strategies `x'` each of whose
components `x' i` is a best response for player `i` given the reference point
`x` (whose own `i`-th coordinate is ignored, as in `BestResponse`). -/
def BestJointResponse {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x : ∀ i, Fin (m i) → ℝ) : Set (∀ i, Fin (m i) → ℝ) :=
  {x' : ∀ i, Fin (m i) → ℝ | ∀ i, x' i ∈ BestResponse S f i x}

end Supermodularity.Games



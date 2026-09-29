-- Prove2me | Definitions.Def_OnlinePrimalDual_GroupSteiner_expectedCost
-- name    : OnlinePrimalDual_GroupSteiner_expectedCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:56:50.65352+00:00
-- url     : https://prove2.me/theorems/0927bb7e-46e0-4be1-8e3f-69bd4514b547
-- title:
--   Expected cost of the random cover
-- statement:
--   `expectedCost ρ c := 𝔼[∑_{e ∈ C} c_e]`, the expected total cost of the random cover `C` drawn
--   from `ρ`, with respect to an edge-cost function `c`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 230, Lemma 11.2

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover

namespace OnlinePrimalDual.GroupSteiner

/-- The expected cost `𝔼[∑_{e ∈ C} cₑ]` of the random cover `C` drawn from `ρ`, with respect to
an edge-cost function `c` (Buchbinder & Naor, FnT TCS 2009, Lemma 11.2, p. 230). -/
def RandomCover.expectedCost {E : Type*} [Fintype E] [DecidableEq E] (ρ : RandomCover E)
    (c : E → ℝ) : ℝ :=
  ∑ C, ρ.p C * ∑ e ∈ C, c e

end OnlinePrimalDual.GroupSteiner



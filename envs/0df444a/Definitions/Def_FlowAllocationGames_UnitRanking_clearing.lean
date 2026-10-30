-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_clearing
-- name    : FlowAllocationGames_UnitRanking_clearing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:08:47.589082+00:00
-- url     : https://prove2.me/theorems/85e9b0da-ea98-491a-a6d2-368a76f74d96
-- title:
--   Clearing state $\hat f$ of a profile
-- statement:
--   For a strategy profile $a$, the **clearing state** $\hat f$ is the coordinatewise supremum of the feasible flows:
--
--   $$
--   \hat f_e = \sup \{ f_e : f \text{ feasible for } a \} \qquad (e \in E).
--   $$
--
--   For a profile of monotone strategies the feasible flows form a nonempty complete lattice and are bounded by the capacities, so $\hat f$ is the greatest feasible flow, the supremum of the lattice. It is the unique feasible flow that maximizes the total flow, which the paper calls the clearing state; it determines the utilities.
--
--   **Formalization Note** For a profile without feasible flows the supremum of the empty set is $0$ by convention; the mission uses the clearing state only for unit-ranking profiles, where the set is nonempty and bounded by $c_e$.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 13

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_IsFeasible

namespace FlowAllocationGames.UnitRanking

/-- **Clearing state of a profile.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, p. 13:
"we concentrate on the supremum of the lattice. For every profile a, we focus on the unique
feasible flow that maximizes the total flow in the network. We denote this feasible flow by f̂ and
call it the clearing state of strategy profile a."

`clearing Γ a e` is the supremum, over all feasible flows `f` of `a`, of `f e`: the coordinatewise
supremum of the feasible flows.

**Formalization Note.** For a profile of monotone strategies the feasible flows form a nonempty
complete lattice (Theorem 2, milestone `theorem_2_feasible_complete_lattice`) and every feasible
flow is bounded by the capacities, so each set here is nonempty and bounded above by `c e`; its
`sSup` is then a maximum, and `clearing Γ a` is the greatest feasible flow, the paper's `f̂`
(milestone `clearing_isFeasible_greatest`). For a profile without feasible flows the value is
`ℕ`'s junk value `sSup ∅ = 0`; the mission only uses `clearing` on unit-ranking profiles. -/
noncomputable def clearing {n m : ℕ} (Γ : Game n m) (a : Profile m) : Fin m → ℕ :=
  fun e => sSup {k | ∃ f, IsFeasible Γ a f ∧ f e = k}

end FlowAllocationGames.UnitRanking



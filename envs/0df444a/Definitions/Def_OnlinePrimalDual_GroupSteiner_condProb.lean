-- Prove2me | Definitions.Def_OnlinePrimalDual_GroupSteiner_condProb
-- name    : OnlinePrimalDual_GroupSteiner_condProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:56:18.071699+00:00
-- url     : https://prove2.me/theorems/bfcff63e-8507-40c0-a9b0-b7637cae0a1a
-- title:
--   Conditional probability of one edge given another is in the cover
-- statement:
--   `condProb ρ e e' := ℙ[e ∈ C ∣ e' ∈ C]`, using Lean's `x/0 = 0` convention when
--   `ℙ[e' ∈ C] = 0`. Used to state the rounding algorithm's third update rule, which conditions
--   on the parent edge already being in the cover.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 230, Algorithm box, third bullet

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_marg

namespace OnlinePrimalDual.GroupSteiner

/-- The conditional probability `ℙ[e ∈ C ∣ e' ∈ C]` that edge `e` belongs to the random cover
`C`, given that edge `e'` does (`0` if `ℙ[e' ∈ C] = 0`, matching Lean/Mathlib's `x / 0 = 0`
convention; the algorithm's rule (Algorithm box, p. 230) only ever invokes this quantity with
`e' = parent e` and `marg e' > 0`, since the algorithm never conditions on a zero-probability
event). Used to state the rounding algorithm's third update rule (p. 230, third bullet). -/
noncomputable def RandomCover.condProb {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : RandomCover E) (e e' : E) : ℝ :=
  (∑ C ∈ Finset.univ.filter (fun C => e ∈ C ∧ e' ∈ C), ρ.p C) / ρ.marg e'

end OnlinePrimalDual.GroupSteiner



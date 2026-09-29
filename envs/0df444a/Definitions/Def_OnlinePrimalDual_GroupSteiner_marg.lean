-- Prove2me | Definitions.Def_OnlinePrimalDual_GroupSteiner_marg
-- name    : OnlinePrimalDual_GroupSteiner_marg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:55:46.179643+00:00
-- url     : https://prove2.me/theorems/ef56e7f1-0609-49fe-ab9d-17ca821f63f6
-- title:
--   Marginal probability that an edge is in the random cover
-- statement:
--   `marg ρ e := ℙ[e ∈ C]`, the marginal probability that edge `e` belongs to the random cover
--   `C` drawn from `ρ`, i.e. the sum of `ρ.p C` over every `C` containing `e`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 230, Lemma 11.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover

namespace OnlinePrimalDual.GroupSteiner

/-- The marginal probability `ℙ[e ∈ C]` that a fixed edge `e` belongs to the random cover `C`
drawn from `ρ` (Buchbinder & Naor, FnT TCS 2009, Lemma 11.1, p. 230). -/
def RandomCover.marg {E : Type*} [Fintype E] [DecidableEq E] (ρ : RandomCover E) (e : E) : ℝ :=
  ∑ C ∈ Finset.univ.filter (fun C => e ∈ C), ρ.p C

end OnlinePrimalDual.GroupSteiner



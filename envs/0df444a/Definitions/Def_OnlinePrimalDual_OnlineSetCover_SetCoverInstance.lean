-- Prove2me | Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
-- name    : OnlinePrimalDual_OnlineSetCover_SetCoverInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:37:27.38115+00:00
-- url     : https://prove2.me/theorems/bd342130-01be-4ab7-9c60-83cd6df88d96
-- title:
--   The (weighted) online set-cover instance
-- statement:
--   A finite universe of elements `E`, known to the algorithm in advance, and a finite family of
--   sets `T` with positive costs `c`. `elemSets e` records, for each element, the family of sets
--   containing it (the book's implicit incidence relation `e ∈ s`).
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 135-137, Section 5.1

import Mathlib

namespace OnlinePrimalDual.OnlineSetCover

/-- Buchbinder & Naor, *The Design of Competitive Online Algorithms via a Primal-Dual Approach*,
FnT TCS 2009, Section 5.1, p. 135-137 (PDF p. 46-48). The (weighted) online set-cover instance:
a finite universe of elements `E`, known to the algorithm in advance (the book's standing
assumption, p. 136: "we assume that the universe of elements `X` is known to the algorithm along
with the family of sets `S`. It is unknown, however, which subset `X′ ⊆ X` of the elements the
algorithm would eventually have to cover"), and a finite family of sets `T` with positive costs
`c`. `elemSets e` is the family of sets containing element `e` (the book's implicit incidence
relation `e ∈ s`), played in the role Chapter 4's `CoveringInstance.S` plays for a constraint's
variables — here the "constraint" is the requirement that element `e` eventually be covered, and
the "primal variables" are the sets. Costs are strengthened from the book's "non-negative" to
strictly positive for the same reason as `Framework.CoveringInstance` (every set's dual weight
`w_s` is compared against `c_s` inside a division-free algebraic bound in this chapter, but the
companion `Framework` mission's algorithms this chapter's own fractional subroutine reuses do
divide by `c_i`; kept positive here too for consistency and to avoid a `c_s = 0` set trivially
absorbing unbounded weight for zero cost). -/
structure SetCoverInstance (E T : Type*) [Fintype E] [Fintype T] [DecidableEq T] where
  /-- `elemSets e` is the finite set of sets `s` with `e ∈ s` ("`s ∋ e`", used throughout
  Section 5.1 as `∑_{s|e∈s} ws`). -/
  elemSets : E → Finset T
  /-- The (positive) cost coefficients `cs` of the sets. -/
  c : T → ℝ
  hc_pos : ∀ t, 0 < c t

end OnlinePrimalDual.OnlineSetCover



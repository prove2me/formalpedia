-- Prove2me | Definitions.Def_ProcessingNetworks_Stability_Stable
-- name    : ProcessingNetworks_Stability_Stable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:17:50.931171+00:00
-- url     : https://prove2.me/theorems/a11dc349-5753-4940-b094-43cb735d3c4a
-- title:
--   Definition 3.6 — SPN stability
-- statement:
--   **Definition 3.6.** An SPN satisfying Assumption 3.1 is **stable** if the (mutually
--   equivalent, by Proposition 3.5) conditions of that proposition hold: the ambient Markov chain $X$
--   is positive recurrent, equivalently has a unique stationary distribution, equivalently the
--   buffer-contents process $Z(t)$ converges in distribution to a non-defective limit.
--
--   `IsStable M` takes positive recurrence of the continuous-time chain of the Markov representation
--   $M$ (Definition D.15, through its jump matrix `M.jump` and exit rates `M.rate`) as the defining
--   clause, since it is the one of the three conditions that mentions only the chain itself, not the
--   ambient probability space $\Omega$ or the process $Z$. The companion goal theorem of this mission,
--   `equivalent_stability_conditions`, is exactly what certifies that the other two clauses are
--   interchangeable with this one, so `IsStable` faithfully captures Definition 3.6 regardless of
--   which of the three equivalent conditions is used to check it in a given application.
--
--   **Formalization note.** The book treats the three conditions of Proposition 3.5 as literally
--   interchangeable ("stable if the equivalent statements... hold"); picking one as the definition
--   and proving the other two equivalent to it (rather than defining `IsStable` as a three-way
--   conjunction) is the more standard mathematical convention and loses nothing, given the equivalence
--   theorem is itself part of this mission.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 47, Definition 3.6

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.Stability

open MeasureTheory

/-- Definition 3.6 (SPN stability), Dai & Harrison, p. 47: an SPN satisfying Assumption 3.1 is
stable if the (by Proposition 3.5, mutually equivalent) conditions of that proposition hold. This
mission takes positive recurrence of the ambient continuous-time chain (Definition D.15, through
its jump matrix `M.jump` and exit rates `M.rate`) as the defining clause — one of the three
equivalent statements, per Definition 3.6's own "if"; `equivalent_stability_conditions` (the goal
theorem) is what shows the other two clauses are interchangeable with it. -/
def IsStable {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) : Prop :=
  PositiveRecurrent M.jump M.rate

end ProcessingNetworks.Stability



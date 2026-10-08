-- Prove2me | Definitions.Def_Nash1950_Countering_Setting
-- name    : Nash1950_Countering_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:59:00.94716+00:00
-- url     : https://prove2.me/theorems/03c33147-44d6-4bb0-b98d-97fc43711451
-- title:
--   Countering profiles, countering sets, and their graph
-- statement:
--   In a finite strategic game, let $P$ and $Q$ be tuples of weight vectors, one for each player. The tuple $Q$ **counters** $P$ when $Q$ is a mixed-strategy profile and, for every player $i$, the strategy $Q_i$ maximizes that player's expected payoff against the other players' strategies in $P$:
--
--   $$
--   Q\text{ counters }P\quad\Longleftrightarrow\quad Q\in\Sigma\ \text{and}\ \forall i\,\forall\tau_i\in\Sigma_i,\ U_i(\tau_i,P_{-i})\le U_i(Q_i,P_{-i}).
--   $$
--
--   The **countering set** of $P$ is the set of all such $Q$. The **graph** consists of pairs $(P,Q)$ with $P$ a mixed-strategy profile and $Q$ countering $P$. These are the objects used by the correspondence theorem.
--
--   **Formalization Note.** The players form a finite type, each finite pure-strategy set is represented by a type, and a mixed strategy is a nonnegative real weight vector summing to one. The comparison evaluates both strategies against the countered profile $P$.
-- source:
--   Nash, Equilibrium points in n-person games, Proc. Natl. Acad. Sci. USA 36 (1950), p. 49, ¶2–¶3 (PDF p. 3)

import Mathlib
import Definitions.Def_agt_games

namespace Nash1950.Countering

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)]

/-- `Q` counters `P` when every coordinate of `Q` is a lottery that maximizes
its owner's expected payoff against the other coordinates of `P`. -/
def Counters (u : ι → (∀ i, S i) → ℝ) (P Q : ∀ i, S i → ℝ) : Prop :=
  AGT.IsMixedProfile Q ∧
    ∀ i (τ : S i → ℝ), AGT.IsLottery τ →
      AGT.expectedPayoff u (Function.update P i τ) i ≤
        AGT.expectedPayoff u (Function.update P i (Q i)) i

/-- The set of mixed profiles countering `P`. -/
def counteringSet (u : ι → (∀ i, S i) → ℝ) (P : ∀ i, S i → ℝ) :
    Set (∀ i, S i → ℝ) :=
  {Q | Counters u P Q}

/-- The graph of the countering correspondence on the product of mixed-strategy spaces. -/
def counteringGraph (u : ι → (∀ i, S i) → ℝ) :
    Set ((∀ i, S i → ℝ) × (∀ i, S i → ℝ)) :=
  {x | AGT.IsMixedProfile x.1 ∧ Counters u x.1 x.2}

end Nash1950.Countering



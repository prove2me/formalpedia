-- Prove2me | Definitions.Def_Supermodularity_Games_IsSupermodularGame
-- name    : Supermodularity_Games_IsSupermodularGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:31:14.953143+00:00
-- url     : https://prove2.me/theorems/ce2f4e82-7203-4ad2-9d36-97f50d9af463
-- title:
--   A supermodular game (Chapter 4, p. 178-179)
-- statement:
--   With $S$ and $f$ as in `BestResponse`, the noncooperative game
--   $(N, S, \{f_i : i \in N\})$ is a **supermodular game** if:
--
--   1. $S$ is a **sublattice** of $\mathbb{R}^m$ (closed under the coordinatewise join
--      and meet);
--   2. for each player $i$ and each $x_{-i} \in S_{-i}$, the payoff
--      $y_i \mapsto f_i(y_i, x_{-i})$ is **supermodular** on the section
--      $S_i(x_{-i})$; and
--   3. for each player $i$, $f_i(y_i, x_{-i})$ has **increasing differences** in
--      $(y_i, x_{-i})$ on $S_i \times S_{-i}$.
--
--   Both condition 2 (supermodularity in a player's own strategy, others' strategies
--   fixed) and condition 3 (increasing differences between a player's own strategy and
--   the others') are required, and both are needed for the results that follow; the
--   book notes these correspond exactly to Theorem 2.8.1's hypotheses (chunk
--   `02-monotonicity`).
--
--   **Formalization Note** The player set $N$ is `ι`, a `Fintype`; a joint strategy is
--   `∀ i, Fin (m i) → ℝ`, and $x_{-i}$ is represented implicitly via
--   `Function.update` exactly as in `BestResponse`. `SupermodularOn` and
--   `IncreasingDifferencesOn` are the definitions from chunk `02-monotonicity`
--   (Theorem 2.6.1/2.8.1's own hypotheses), reused verbatim rather than restated, so
--   that a supermodular game's defining conditions are literally the hypotheses of that
--   chunk's theorems, instantiated at each player's own payoff. `IsSublattice` is
--   Mathlib's own binary-join/meet-closure predicate, matching the book's "$S$ is a
--   sublattice."
--
--   **Moderator's note.** Supermodularity of `fᵢ(·, x₋ᵢ)` is required on the projection $S_i$ (for each $x_{-i} \in S_{-i}$) and increasing differences on $S_i \times S_{-i}$, exactly as Topkis defines a supermodular game (p. 178–179); an earlier draft used only the feasible sections of $S$, a weaker hypothesis.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 178-179, Chapter 4 (definition of a supermodular game)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn

namespace Supermodularity.Games

/-- The projection `Sᵢ` of `S` onto player `i`'s strategies (Topkis p. 178): the
strategies `y` occurring as the `i`-th coordinate of some feasible joint strategy. -/
def proj {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (i : ι) : Set (Fin (m i) → ℝ) :=
  {y | ∃ x, Function.update x i y ∈ S}

/-- The projection `S₋ᵢ` of `S` onto the other players' strategies (Topkis p. 178),
represented by full joint strategies whose `i`-th coordinate is irrelevant. -/
def projOthers {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (i : ι) : Set (∀ i, Fin (m i) → ℝ) :=
  {x | ∃ y, Function.update x i y ∈ S}

/-- `IsSupermodularGame S f` says the noncooperative game with feasible joint
strategy set `S` and payoff functions `f` is a **supermodular game** (Topkis p. 178–179):
`S` is a sublattice of `ℝᵐ`; for each player `i` and each `x₋ᵢ ∈ S₋ᵢ` the payoff
`yᵢ ↦ fᵢ(yᵢ, x₋ᵢ)` is supermodular on the projection `Sᵢ`; and `fᵢ(yᵢ, x₋ᵢ)` has
increasing differences in `(yᵢ, x₋ᵢ)` on `Sᵢ × S₋ᵢ`. Other players' strategies enter
through `Function.update x i y`, whose `i`-th coordinate of `x` is overwritten. -/
structure IsSupermodularGame {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ) : Prop where
  sublattice : IsSublattice S
  supermodular : ∀ i, ∀ x ∈ projOthers S i,
    Supermodularity.Monotonicity.SupermodularOn
      (fun y : Fin (m i) → ℝ => f i (Function.update x i y)) (proj S i)
  increasing_differences : ∀ i : ι,
    Supermodularity.Monotonicity.IncreasingDifferencesOn
      (fun (y : Fin (m i) → ℝ) (x : ∀ i, Fin (m i) → ℝ) => f i (Function.update x i y))
      (proj S i ×ˢ projOthers S i)

end Supermodularity.Games



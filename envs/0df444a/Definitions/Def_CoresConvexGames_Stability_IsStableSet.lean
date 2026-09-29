-- Prove2me | Definitions.Def_CoresConvexGames_Stability_IsStableSet
-- name    : CoresConvexGames_Stability_IsStableSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:50:27.962987+00:00
-- url     : https://prove2.me/theorems/fec74096-9ddf-4ae3-9383-2f5ad1b16746
-- title:
--   Stable set (von Neumann–Morgenstern solution) of feasible payoff vectors
-- statement:
--   Let $N$ be a finite set of players and $v$ a game; a payoff vector $a$ is feasible if $a(N)\le v(N)$, and domination is as in (21): $a$ dominates $b$ if some nonempty coalition $S$ has $a(S)\le v(S)$ and $a_i>b_i$ for all $i\in S$.
--
--   A set $V$ of feasible payoff vectors is **stable** if every feasible payoff vector $b$ is either a member of $V$ or dominated by a member of $V$, but not both:
--
--   $$
--   \text{for every feasible } b:\qquad b\in V \iff \text{no } a\in V \text{ dominates } b .
--   $$
--
--   Stable sets are the von Neumann–Morgenstern solutions of the game: internally no member of $V$ dominates another, externally every feasible vector outside $V$ is dominated from within $V$.
--
--   **Formalization Note** Players are `Fin n`. Following the paper (not the classical definition with imputations, which a footnote on the same page mentions), the stable set and the alternative "member or dominated, but not both" range over feasible vectors. "Exactly one of the two" is encoded as `b ∈ V ↔ ¬ ∃ a ∈ V, Dominates f a b`.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 24, §4.3, definition of stable set (paragraph after (21))

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_IsFeasible
import Definitions.Def_CoresConvexGames_Stability_Dominates

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 24, §4.3: a set `V` of feasible payoff vectors is *stable* if every
feasible payoff vector is either a member of `V` or dominated by a member of `V`, but not
both. -/
def IsStableSet {n : ℕ} (f : Finset (Fin n) → ℝ) (V : Set (Fin n → ℝ)) : Prop :=
  (∀ a ∈ V, IsFeasible f a) ∧
    ∀ b : Fin n → ℝ, IsFeasible f b → (b ∈ V ↔ ¬ ∃ a ∈ V, Dominates f a b)

end CoresConvexGames.Stability



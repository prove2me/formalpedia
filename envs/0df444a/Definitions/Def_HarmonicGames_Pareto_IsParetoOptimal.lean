-- Prove2me | Definitions.Def_HarmonicGames_Pareto_IsParetoOptimal
-- name    : HarmonicGames_Pareto_IsParetoOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:45:40.634505+00:00
-- url     : https://prove2.me/theorems/4242749c-a926-49d2-b54b-e600ee4c60a5
-- title:
--   Definition 5.3 — Pareto optimal strategy profile
-- statement:
--   Consider a game with a finite set of players $\mathcal M$, strategy sets $E^m$ and utilities $u^m : E \to \mathbb R$ on the strategy profiles $E = \prod_m E^m$. A strategy profile $p \in E$ is **Pareto optimal** if there is no other profile $q$ at which all players weakly increase their payoffs and some player strictly increases its payoff, i.e. no $q$ with
--
--   $$
--   u^m(q) \ge u^m(p) \ \text{ for all } m \in \mathcal M, \qquad u^k(q) > u^k(p) \ \text{ for some } k \in \mathcal M. \qquad (53)
--   $$
--
--   Pareto optimality is the efficiency notion of Section 5.3, where it is compared with the pure Nash equilibria of a game.
--
--   **Formalization Note** The utilities are a plain function `u : ι → (∀ k, S k) → ℝ`, the same shape as in the published `agt_games` bundle, so the definition applies to `payoff E u` for a game `u`. A profile $q$ satisfying (53) is necessarily different from $p$, so "another strategy profile" needs no separate clause.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 31, Definition 5.3, (53)

import Mathlib

/-!
Pareto optimality of a pure strategy profile (Definition 5.3 of Candogan, Menache, Ozdaglar,
Parrilo).
-/

namespace HarmonicGames.Pareto

/-- **Definition 5.3 (Pareto optimality)**, (53). For a game with players `ι`, strategy sets
`S m` and utilities `u m : (∀ k, S k) → ℝ`, a strategy profile `p` is **Pareto optimal** iff
there is no profile `q` at which all players weakly increase their payoffs and some player
strictly increases its payoff: no `q` with `u m q ≥ u m p` for all `m` and `u k q > u k p` for
some `k`. -/
def IsParetoOptimal {ι : Type} {S : ι → Type} (u : ι → (∀ k, S k) → ℝ) (p : ∀ k, S k) : Prop :=
  ¬ ∃ q : ∀ k, S k, (∀ m, u m p ≤ u m q) ∧ ∃ k, u k p < u k q

end HarmonicGames.Pareto



-- Prove2me | Definitions.Def_CachonCoord_Proportional_Nash
-- name    : CachonCoord_Proportional_Nash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:16:40.701978+00:00
-- url     : https://prove2.me/theorems/4cb6c63e-af59-422b-bc88-a47dbfe8dded
-- title:
--   §6.5.1, p. 50 — pure Nash equilibrium of an n-player game with nonnegative real strategies
-- statement:
--   A **pure-strategy Nash equilibrium** of a game with $n$ players, in which each player $i$ chooses a nonnegative real number $q_i$ (an order quantity) and receives the payoff $u_i(q_1,\dots,q_n)$, is a profile $q^* = (q^*_1,\dots,q^*_n)$ with every $q^*_i \ge 0$ such that no player gains from a unilateral deviation:
--
--   $$
--   u_i(q^*_1,\dots,q^*_{i-1}, x, q^*_{i+1},\dots,q^*_n) \le u_i(q^*) \qquad \text{for all } i \text{ and all } x \ge 0 .
--   $$
--
--   This is the notion used on p. 50 of the chapter: "A set of order quantities $\{q^*_1,\dots,q^*_n\}$ is a Nash equilibrium of the decentralized system if each retailer's order quantity is a best response."
--
--   **Formalization Note** Players are indexed by `Fin n` and payoffs are given as a function of the player and the whole profile; a deviation is `Function.update`. No platform definition of a Nash equilibrium over nonnegative real strategies fits, so it is defined here.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 50 (definition of a Nash equilibrium of the decentralized system)

import Mathlib

namespace CachonCoord.Proportional

/-- Pure-strategy Nash equilibrium of an `n`-player game in which every player chooses a
nonnegative real number (an order quantity) and `payoff i q` is player `i`'s payoff at the
strategy profile `q`. The profile `q` is a Nash equilibrium if every coordinate is feasible
(`q i ≥ 0`) and no player gains by a unilateral deviation to any other feasible `x ≥ 0`
(Cachon 2003, 3rd draft, §6.5.1, p. 50: "each retailer's order quantity is a best response"). -/
def IsNash {n : ℕ} (payoff : Fin n → (Fin n → ℝ) → ℝ) (q : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧
    ∀ (i : Fin n) (x : ℝ), 0 ≤ x → payoff i (Function.update q i x) ≤ payoff i q

end CachonCoord.Proportional



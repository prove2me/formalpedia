-- Prove2me | Definitions.Def_CachonCoord_TwoLocation_Game
-- name    : CachonCoord_TwoLocation_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:43:12.998318+00:00
-- url     : https://prove2.me/theorems/fa7157aa-7b3b-4324-a00a-ef71ae619987
-- title:
--   §6.8.3, p. 79 — Nash equilibrium of a two-player cost-minimization game with real strategies
-- statement:
--   Consider a two-player game in which player $r$ chooses $s_r \in \mathbb R$, player $s$ chooses $s_s \in \mathbb R$, and the players have cost functions $\pi_r(s_r, s_s)$ and $\pi_s(s_r, s_s)$ that they want to minimize. A pair $\{s_r^*, s_s^*\}$ is a **Nash equilibrium** if neither player can lower its own cost by a unilateral deviation:
--   $$\pi_r(s_r^*, s_s^*) \le \pi_r(x, s_s^*) \quad\text{and}\quad \pi_s(s_r^*, s_s^*) \le \pi_s(s_r^*, y) \qquad \text{for all } x, y \in \mathbb R,$$
--   that is, $s_r^* = s_r(s_s^*)$ and $s_s^* = s_s(s_r^*)$ for best responses $s_i(\cdot)$.
--
--   The two-location base-stock game of §6.8 uses this notion both without contracts and under the Cachon–Zipkin transfers.
--
--   **Formalization Note** Strategies range over all of $\mathbb R$, with no upper bound imposed (the page notes that such a bound "has no impact on the analysis", p. 79).
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.3, p. 79 (definition of best response and Nash equilibrium)

import Mathlib

namespace CachonCoord.TwoLocation

/-- A (pure-strategy) Nash equilibrium of a two-player cost-minimization game in which each
player chooses a real number (here: a base stock level, which may be negative). Player `r` has
cost `costR (s_r, s_s)`, player `s` has cost `costS (s_r, s_s)`; `{s_r, s_s}` is a Nash
equilibrium when neither firm can lower its own cost by a unilateral deviation
(Cachon 2003, §6.8.3, p. 79). -/
def IsNashMin (costR costS : ℝ → ℝ → ℝ) (sr ss : ℝ) : Prop :=
  IsMinOn (fun x => costR x ss) Set.univ sr ∧ IsMinOn (fun y => costS sr y) Set.univ ss

end CachonCoord.TwoLocation



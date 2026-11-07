-- Prove2me | Definitions.Def_SmoothedNash_devPayoff
-- name    : SmoothedNash_devPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:25.520393+00:00
-- url     : https://prove2.me/theorems/038efcf6-9a18-40ae-a9c9-7b5961dcc634
-- title:
--   Deviation payoff $U_{i,a}(x) = u_i(a, x_{-i})$
-- statement:
--   For a game $u$, a profile $x = (x_1, \dots, x_m)$ of mixed strategies, a player $i$ and an action $a \in [n]$, the **deviation payoff** is
--   $$
--   U_{i,a}(x) := u_i(a, x_{-i}),
--   $$
--   the expected payoff to player $i$ when $i$ plays the pure action $a$ and every other player $j$ independently samples an action from $x_j$.
--
--   The vector of all deviation payoffs is the only information about the game that Algorithm 2 queries.
--
--   **Formalization Note** The profile $(a, x_{-i})$ replaces player $i$'s strategy by the point mass $e_a$, and the expectation is the published `AGT.expectedPayoff`.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §1.1.2, p.6, and Assumption 1.18, p.7

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_pureStrat

namespace SmoothedNash

/-- The **deviation payoff** `U_{i,a}(x) := u_i(a, x_{-i})` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §1.1.2, p.6, and
Assumption 1.18, p.7): the expected payoff of player `i` when `i` plays the pure action `a` and every
other player `j` plays the mixed strategy `x_j`, independently.

**Formalization Note** The profile `(a, x_{-i})` is `Function.update x i (pureStrat a)` and the
expectation is the published `AGT.expectedPayoff`. -/
noncomputable def devPayoff {m n : ℕ} (u : Game m n) (x : Fin m → Fin n → ℝ) (i : Fin m)
    (a : Fin n) : ℝ :=
  AGT.expectedPayoff (S := fun _ : Fin m => Fin n) u (Function.update x i (pureStrat a)) i

end SmoothedNash



-- Prove2me | Definitions.Def_SmoothedNash_Game
-- name    : SmoothedNash_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:39.309875+00:00
-- url     : https://prove2.me/theorems/af709eaa-a7b7-4ca6-905a-1cfd4adc78c5
-- title:
--   Finite normal-form game with $m$ players and $n$ actions
-- statement:
--   A **finite normal-form game** with $m$ players, each having $n$ actions, is given by payoff functions
--   $$
--   u_i : [n]^m \to \mathbb R, \qquad i \in [m],
--   $$
--   where $u_i(a_1, \dots, a_m)$ is the payoff to player $i$ when the players choose the action profile $(a_1, \dots, a_m)$.
--
--   This is the game format of the whole mission. The paper's games have payoffs in $[0, 1]$; that range is the separate predicate `PayoffsIn01`, assumed by the theorems that need it.
--
--   **Formalization Note** Players are `Fin m` and actions `Fin n` (numbered from $0$). With players $\iota = $ `Fin m` and strategy sets $S_i = $ `Fin n` this is the payoff format of the published `AGT.agt_games`, whose lotteries, mixed profiles and expected payoffs the mission reuses.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §1.1.2, p.6

import Mathlib

namespace SmoothedNash

/-- A finite normal-form game with `m` players, each having `n` actions (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53),
§1.1.2, p.6): `u i a` is the payoff of player `i` at the pure action profile `a : Fin m → Fin n`.

**Formalization Note** Players are `Fin m` and actions `Fin n`, 0-based versions of the paper's
`[m]` and `[n]`. Payoffs are real numbers; the paper's range `[0, 1]` is the separate predicate
`PayoffsIn01`, which every theorem that needs it assumes. With `ι := Fin m` and
`S := fun _ => Fin n` this is exactly the payoff format `u : ι → (∀ i, S i) → ℝ` of the published
`AGT.agt_games`, whose lotteries, mixed profiles and expected payoffs the mission reuses. -/
abbrev Game (m n : ℕ) : Type := Fin m → (Fin m → Fin n) → ℝ

end SmoothedNash



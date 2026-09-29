-- Prove2me | Definitions.Def_CalibratedCE_Convergence_MatchingPennies
-- name    : CalibratedCE_Convergence_MatchingPennies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:28:01.039031+00:00
-- url     : https://prove2.me/theorems/3400e540-712f-406e-88a7-4fb00a03b889
-- title:
--   Matching pennies with a constant forecast and an alternating tie-break (p. 46)
-- statement:
--   The version of matching pennies on p. 46 has strategies H, T for the row player and h, t for the column player, with payoffs (row/column)
--
--   | | h | t |
--   |---|---|---|
--   | H | $1/-1$ | $-1/1$ |
--   | T | $-1/1$ | $1/-1$ |
--
--   With heads $= 0$ and tails $= 1$ this is $u_1(a, b) = 1$ if $a = b$ and $-1$ otherwise, and $u_2 = -u_1$.
--
--   "In each round the row player will forecast that there is a 50% chance that column will play heads and a 50% chance that column will play tails, i.e., $(0.5, 0.5)$ is the forecast. The column player will do likewise. [...] Consider the following tie breaking rule: on even numbered rounds play heads and tails on the other rounds. Notice that the resulting sequence of plays will be: Tt, Hh, Tt, Hh, ...." This file defines the payoffs $u_1, u_2$, the constant forecast $(1/2, 1/2)$, and the play sequence $T, H, T, H, \dots$ used by both players.
--
--   The example shows that the stationarity of the tie-breaking rule cannot be dropped from Theorem 1.
--
--   **Formalization Note** The paper's round $s+1$ is index $s$; the first round is odd, so index $s$ plays tails exactly when $s$ is even.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 46 (matching pennies example)

import Mathlib

namespace CalibratedCE.Convergence

/-- Row player's payoff in the matching pennies game of Foster–Vohra (1997), p. 46, with
strategies `0 = H/h` (heads) and `1 = T/t` (tails): `1` on a match, `-1` otherwise. -/
def mpU₁ : Fin 2 → Fin 2 → ℝ := fun a b => if a = b then 1 else -1

/-- Column player's payoff in matching pennies: the negative of the row player's. -/
def mpU₂ : Fin 2 → Fin 2 → ℝ := fun a b => -mpU₁ a b

/-- The constant forecast `(0.5, 0.5)` issued by each player in every round. -/
noncomputable def mpForecast : ℕ → Fin 2 → ℝ := fun _ _ => 1 / 2

/-- The play produced by the non-stationary tie-break "heads on even numbered rounds, tails on
the others": round `s + 1` of the paper is index `s`, so index `s` plays tails (`1`) when `s`
is even. Both players play this sequence: `Tt, Hh, Tt, Hh, …`. -/
def mpPlay : ℕ → Fin 2 := fun s => if s % 2 = 0 then 1 else 0

end CalibratedCE.Convergence



-- Prove2me | Definitions.Def_FixpNash_WeakApprox_GameConstants
-- name    : FixpNash_WeakApprox_GameConstants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:19.548041+00:00
-- url     : https://prove2.me/theorems/176e6c4d-b82b-4967-b457-46af4edec03a
-- title:
--   pp. 20–21 — the constants n, M and c = 1 + M of a finite game
-- statement:
--   For a finite game $\Gamma$ with players $i$, finite pure-strategy sets $S_i$ and payoff functions $u_i$ on the pure strategy profiles $S=\prod_i S_i$, the proof of Proposition 3 uses three constants determined by the game:
--
--   1. $n$, **the maximum number of pure strategies of a player**,
--   $$n=\max_i |S_i|;$$
--   2. $M$, **the maximum difference, over all players $i$, between the maximum and the minimum payoff of player $i$ under any pure strategy profile**,
--   $$M=\max_i\Bigl(\max_{s\in S}u_i(s)-\min_{s\in S}u_i(s)\Bigr);$$
--   3. $c=1+M$.
--
--   Every gain $g_{i,j}(x)$ at a mixed profile lies in $[-M,M]$, since both terms of the gain are averages of payoffs of player $i$; the constants $n$ and $c$ enter the tolerance $\varepsilon'=\varepsilon^2/(4c^2n^3)$ of Proposition 3.
--
--   **Formalization Note** $n$ is a natural number (`Finset.sup` of the cardinalities, $0$ when there are no players). $M$ is written with real suprema and infima over finite types: they are the maxima and minima of the page whenever there is a player and every $S_i$ is nonempty, which holds for every game that has a mixed profile. $M$ is the per-player spread, not the largest payoff entry of the game (`DGPNash.WellSupported.maxPayoff`).
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Proposition 3, pp. 20–21

import Mathlib

namespace FixpNash.WeakApprox

/-- `n`, the maximum number of pure strategies of a player, `max_i |S_i|` (pp. 20–21).
It is `0` when there are no players. -/
def maxNumStrategies {ι : Type*} [Fintype ι] (S : ι → Type*) [∀ i, Fintype (S i)] : ℕ :=
  Finset.univ.sup fun i => Fintype.card (S i)

/-- `M`, the maximum over the players `i` of the difference between the maximum and the minimum
payoff of player `i` over all pure strategy profiles (p. 21):
`M = max_i (max_s u_i(s) - min_s u_i(s))`. The suprema and infima range over finite types; they
are maxima and minima whenever there is at least one player and every `S_i` is nonempty. -/
noncomputable def payoffSpread {ι : Type*} [Fintype ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (u : ι → (∀ i, S i) → ℝ) : ℝ :=
  ⨆ i : ι, ((⨆ s : (∀ k, S k), u i s) - ⨅ s : (∀ k, S k), u i s)

/-- The constant `c = 1 + M` of p. 21. -/
noncomputable def cConst {ι : Type*} [Fintype ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (u : ι → (∀ i, S i) → ℝ) : ℝ :=
  1 + payoffSpread u

end FixpNash.WeakApprox



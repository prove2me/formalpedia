-- Prove2me | Definitions.Def_OceanicGames_Limit_WeightedMajority
-- name    : OceanicGames_Limit_WeightedMajority
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:43.656163+00:00
-- url     : https://prove2.me/theorems/bde74a55-ff66-4a40-8bb6-7e6ea9164f28
-- title:
--   Finite weighted majority game with a quota
-- statement:
--   For a finite list of real voting weights $u_1,\ldots,u_N$ and quota $c$, the weighted majority game assigns a coalition $S$ the value
--
--   $$v_{c,u}(S)=\begin{cases}1,&\sum_{j\in S}u_j\ge c,\\0,&\sum_{j\in S}u_j<c.\end{cases}$$
--
--   This is the characteristic function used in the finite-game Shapley formula (A.4). Nonnegative weights are assumptions of the theorems that use it; the quota is an arbitrary real number.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), Appendix (A.4), p. 26; https://www.rand.org/pubs/research_memoranda/RM2649.html

import Mathlib

namespace OceanicGames.Limit

/-- The finite weighted majority game of Appendix (A.4), with a coalition winning
when its total weight is at least the quota. -/
noncomputable def wmGame {N : ℕ} (c : ℝ) (u : Fin N → ℝ) : Finset (Fin N) → ℝ :=
  fun S => if c ≤ ∑ j ∈ S, u j then 1 else 0

end OceanicGames.Limit



-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_Profile
-- name    : FlowAllocationGames_UnitRanking_Profile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:05:34.681219+00:00
-- url     : https://prove2.me/theorems/7407a51e-877a-4d8f-bec6-f5d17fed46d5
-- title:
--   Integral strategy profile
-- statement:
--   A **strategy profile** $a = (a_e)_{e \in E}$ assigns to every edge $e$ a parametrized flow allocation function $a_e : \mathbb{N}_0 \to \mathbb{N}_0$. The value $a_e(y)$ is the amount the tail of $e$ forwards on $e$ when its total supply is $y$. The strategy of player $v$ is the family $(a_e)_{e\in E^+(v)}$.
--
--   Unit-ranking games use integral strategies, so that feasible flows are integral; constraints on profiles are imposed separately (monotone and unit-ranking profiles).
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, pp. 9–10; §2.2, p. 13

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **Integral strategy profile.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, pp. 9–10
(a strategy of `v` is a family of flow allocation functions `ae`, `e ∈ E⁺(v)`; a profile is
`a = (ae)e∈E`) and §2.2, p. 13: "We define the parametrized flow functions ae(y) for every outgoing
edge e ∈ E⁺(v) on the non-negative integer numbers ae(y) : N0 → N0."

A profile assigns to every edge `e` a function `a e : ℕ → ℕ`; `a e y` is the amount the tail of
`e` forwards on `e` when its total supply is `y`.

**Formalization Note.** The strategy of player `v` is the restriction of the profile to the edges
with tail `v`; no constraint is imposed here (see `IsMonotoneProfile`, `IsUnitRankingProfile`). -/
abbrev Profile (m : ℕ) : Type := Fin m → ℕ → ℕ

end FlowAllocationGames.UnitRanking



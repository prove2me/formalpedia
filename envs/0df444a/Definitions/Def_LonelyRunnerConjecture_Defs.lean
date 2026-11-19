-- Prove2me | Definitions.Def_LonelyRunnerConjecture_Defs
-- name    : LonelyRunnerConjecture_Defs
-- status  : Definition
-- author  : @LG
-- created : 2026-11-17T01:11:12.427197+00:00
-- url     : https://prove2.me/theorems/fc557e40-56fd-4a42-b939-6d6e7dc7181f
-- title:
--   Lonely runner: distance to the nearest integer and $\mathrm{LRC}(k)$
-- statement:
--   Write $\|x\|=\min(\{x\},1-\{x\})$ for the distance from a real number $x$ to the nearest integer, where $\{x\}$ is the fractional part; this is the circular distance from position $x$ to the start $0$ on a unit-length track. For $k\in\mathbb N$, $\mathrm{LRC}(k)$ asserts that for every set $S$ of $k$ distinct positive integer speeds there is a time $t\in\mathbb R$ with $\|tv\|\ge\frac{1}{k+1}$ for every $v\in S$. These two declarations are the shared vocabulary of the mission; `distToNearestInt` equals `|x - round x|`.
-- source:
--   Epoch AI, FrontierMath: Open Problems — The Lonely Runner Conjecture, https://epoch.ai/frontiermath/open-problems/lonely-runner (distance formula and conjecture).

import Mathlib

namespace LonelyRunnerConjecture

/-- The distance from a real number `x` to the nearest integer,
`min (fract x, 1 - fract x)`, where `fract x = Int.fract x` is the fractional part.
Equivalently, the circular distance from position `x` to the starting point `0`
on a track of unit length. -/
noncomputable def distToNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- The lonely runner conjecture for `k` moving runners: for every set `S` of `k`
distinct positive integer speeds, there is a time `t` at which every runner is at
distance at least `1 / (k + 1)` from the starting point `0`. -/
noncomputable def LRC (k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = k → (∀ v ∈ S, 0 < v) →
    ∃ t : ℝ, ∀ v ∈ S, (1 : ℝ) / (k + 1 : ℝ) ≤ distToNearestInt (t * (v : ℝ))

end LonelyRunnerConjecture



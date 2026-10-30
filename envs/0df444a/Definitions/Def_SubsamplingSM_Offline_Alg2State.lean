-- Prove2me | Definitions.Def_SubsamplingSM_Offline_Alg2State
-- name    : SubsamplingSM_Offline_Alg2State
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:53:32.488158+00:00
-- url     : https://prove2.me/theorems/0c54b564-179a-49aa-8f85-a99ef6f27cc4
-- title:
--   State of Algorithm 2 (Equivalent-SampleGreedy)
-- statement:
--   A state of Algorithm 2 consists of
--   1. the current solution $S$,
--   2. the set $O$ (which starts as an optimal solution and is kept independent),
--   3. the set $N'$ of elements not yet considered,
--   4. the sets $O_u$ and $S_u$ for every element $u\in N$, and
--   5. the set of elements $u$ with $Y_u=1$, that is, $u\in S$ and $u\notin O$ at the beginning of the iteration in which $u$ is considered.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 2, Line 1, p. 9, and §4.1.2, p. 15

import Mathlib

namespace SubsamplingSM.Offline

/-- **State of Algorithm 2 (Equivalent-SampleGreedy).**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 2, Line 1, p. 9: "Let `N′ ← N`, `S ← ∅`, `O ← OPT`, and `Ou ← ∅`,
`Su ← ∅` for each `u ∈ N`."

The fields are the current solution `S`, the set `O`, the pool `N′` of elements not yet
considered, the sets `O_u` and `S_u` for each element `u`, and the set `Ys` of elements
`u` with `Y_u = 1` (p. 15: "`u ∈ S` and, in addition, `u` does not belong to `O` at the
beginning of the iteration in which `u` is considered"). -/
structure Alg2State (α : Type*) where
  /-- the current solution `S` -/
  S : Finset α
  /-- the set `O` -/
  O : Finset α
  /-- the pool `N′` of elements not yet considered -/
  N' : Finset α
  /-- the set `O_u` of each element `u` -/
  Ou : α → Finset α
  /-- the set `S_u` of each element `u` -/
  Su : α → Finset α
  /-- the elements `u` with `Y_u = 1` -/
  Ys : Finset α

end SubsamplingSM.Offline



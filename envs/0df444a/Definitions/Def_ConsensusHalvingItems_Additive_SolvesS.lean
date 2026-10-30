-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_SolvesS
-- name    : ConsensusHalvingItems_Additive_SolvesS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:28:46.0677+00:00
-- url     : https://prove2.me/theorems/c78cd6cc-c0e8-4ade-bfd7-e6a27bbf85c9
-- title:
--   The equation system $S$ of the algorithm
-- statement:
--   In Step 2 of the algorithm for Theorem 2.2, $S$ is the system of $n$ linear equations in the unknowns $y_1, \dots, y_m$
--
--   $$
--   \sum_{j \in M} \Bigl(y_j - \tfrac{1}{2}\Bigr) \cdot u_i(j) = 0 \qquad (i \in N).
--   $$
--
--   A vector $y$ solves $S$ when all $n$ equations hold. For a fractional set $y$, this says exactly that $y$ is a consensus halving (equation (1) of the paper). No bound $0 \le y_j \le 1$ is part of $S$.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, Step 2, p. 5

import Mathlib

namespace ConsensusHalvingItems.Additive

/-- **The equation system S of Step 2.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, Step 2, p. 5: "Let S denote the set of n
equations Σ_{j∈M} (yj − 1/2) · ui(j) = 0 for i ∈ N".

`SolvesS u y` holds when `y` satisfies all `n` equations of S:
`∑_j (y j - 1/2) * u i j = 0` for every agent `i`.

**Formalization Note.** 0-based indices; no bound `y ∈ [0,1]` is part of S. -/
def SolvesS {n m : ℕ} (u : Fin n → Fin m → ℚ) (y : Fin m → ℚ) : Prop :=
  ∀ i, ∑ j, (y j - 1 / 2) * u i j = 0

end ConsensusHalvingItems.Additive



-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving
-- name    : ConsensusHalvingItems_Additive_IsConsensusHalving
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:28:12.886696+00:00
-- url     : https://prove2.me/theorems/620cd10e-df30-45fe-a00d-71874f00fecc
-- title:
--   Consensus halving (additive utilities)
-- statement:
--   A **consensus halving** is a partition of the items into two fractional sets $M_1$ and $M_2$ such that every agent values both parts equally: $u_i(M_1) = u_i(M_2)$ for all agents $i$. A partition into two fractional sets is determined by its first part $x$, the second being $1 - x$ (the fractions of each item sum to $1$). With additive utilities, $x$ is a consensus halving exactly when
--
--   1. $x$ is a fractional set: $0 \le x_j \le 1$ for every item $j$, and
--   2. for every agent $i$,
--   $$
--   \sum_{j \in M} x_j \cdot u_i(j) = \sum_{j \in M} (1 - x_j) \cdot u_i(j).
--   $$
--
--   Both conditions are required; the bound $x_j \in [0,1]$ is what makes the count of cut items meaningful.
--
--   **Formalization Note** The partition $(M_1, M_2)$ is encoded as $(x, 1 - x)$; agents `Fin n`, items `Fin m` (0-based); rational values of any sign.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Definition 2.1, p. 4; §2, p. 4 (partitions into fractional sets; additivity)

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_IsFractionalSet
import Definitions.Def_ConsensusHalvingItems_Additive_additiveUtil

namespace ConsensusHalvingItems.Additive

/-- **Consensus halving (additive utilities).**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, Definition 2.1, p. 4: "A consensus halving is a partition of M into
two fractional sets of items M1 and M2 such that ui(M1) = ui(M2) for all i ∈ N." A partition
"has the property that for every item j ∈ M, the fractions of item j in the k fractional sets sum
up to exactly 1" (§2, p. 4).

A two-part partition is determined by its first part `x` (the second is `1 - x`). The vector
`x` is a consensus halving for the value matrix `u` when `x` is a fractional set (every
`x j ∈ [0, 1]`) and every agent `i` values both parts equally:
`∑_j x j * u i j = ∑_j (1 - x j) * u i j`.

**Formalization Note.** The partition `(M₁, M₂)` is encoded as `(x, 1 - x)`; the second part
is a fractional set exactly when the first is. The utilities are the additive ones of §2. -/
def IsConsensusHalving {n m : ℕ} (u : Fin n → Fin m → ℚ) (x : Fin m → ℚ) : Prop :=
  IsFractionalSet x ∧ ∀ i, additiveUtil u i x = additiveUtil u i (fun j => 1 - x j)

end ConsensusHalvingItems.Additive



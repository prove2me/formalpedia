-- Prove2me | Definitions.Def_WeightedCongestionBR_maxBitLen
-- name    : WeightedCongestionBR_maxBitLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:17.095909+00:00
-- url     : https://prove2.me/theorems/94051f31-69f9-48b8-9b05-5b5a7c31a9e0
-- title:
--   Largest bit length $L$
-- statement:
--   $L=\max_{q\in V}\ell(q)$, the largest bit length among the rational numbers that Algorithm 1 handles on a rational instance.
--
--   **Formalization Note** $V$ is finite, so the supremum in $\mathbb N$ is attained.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 4, p.18

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_RatData
import Definitions.Def_WeightedCongestionBR_bitLen
import Definitions.Def_WeightedCongestionBR_ratValues
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- `L := max_{q ∈ V} ℓ(q)`, the largest bit length of a number handled by Algorithm 1 on a rational
instance (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, cost model of Theorem 4, p.18; Reading 1 of the mission).

**Formalization Note** `V = ratValues G D m s_init` is finite, so the supremum in `ℕ` is a maximum. -/
noncomputable def maxBitLen {n r d : ℕ} (G : Game n r) (D : RatData n r d) (m : ℕ)
    (sinit : G.Profile) : ℕ :=
  sSup (bitLen '' ratValues G D m sinit)

end WeightedCongestionBR



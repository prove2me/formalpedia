-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_additiveUtil
-- name    : ConsensusHalvingItems_Additive_additiveUtil
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:27:35.171845+00:00
-- url     : https://prove2.me/theorems/7524bb9e-530e-474f-91dd-b196cec0fa0e
-- title:
--   Additive utility of a fractional set
-- statement:
--   Agent $i$ has **additive** utilities when its utility for a fractional set $x$ is the fraction-weighted sum of its item values:
--
--   $$
--   u_i(x) = \sum_{j \in M} x_j \cdot u_i(j).
--   $$
--
--   This is the standing assumption of §2 of the paper, under which Theorem 2.2 is stated.
--
--   **Formalization Note** Agents `Fin n`, items `Fin m` (0-based); values are rationals of any sign.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, §2, p. 4 ("In this section, we assume that the agents' utility functions are additive")

import Mathlib

namespace ConsensusHalvingItems.Additive

/-- **Additive utility of a fractional set.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, §2, p. 4: "In this section, we assume that the agents' utility
functions are additive. This means that for a set M′ containing a fraction xj of item j, the
utility of agent i is given by ui(M′) = Σ_{j∈M} xj · ui(j)."

For the value matrix `u` (`u i j` is `u_i(j)`), agent `i`'s utility for the fractional set
`x` is `∑_j x j * u i j`.

**Formalization Note.** 0-based indices; rational values of any sign (Readings 2 and 4). -/
def additiveUtil {n m : ℕ} (u : Fin n → Fin m → ℚ) (i : Fin n) (x : Fin m → ℚ) : ℚ :=
  ∑ j, x j * u i j

end ConsensusHalvingItems.Additive



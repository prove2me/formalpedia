-- Prove2me | Definitions.Def_ManipPotential_TransferStep
-- name    : ManipPotential_TransferStep
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:29:55.720907+00:00
-- url     : https://prove2.me/theorems/fd9fdb16-518c-467a-b2df-03e175bb4d4d
-- title:
--   A positive transfer move with nonnegative replacement background
-- statement:
--   For distinct candidates $c_i,c_j$, a rational profile move $Q\mapsto Q'$ is a **transfer step** when it adds a positive rational multiple $a>0$ of one of the transfer vectors in Eq. (17), and the block removed in that move leaves a nonnegative background profile.
--
--   Explicitly, either $c_i\succ_r c_j$ and
--   $$
--   Q'=Q+a\big((K+1)e_r-e_s\big),\qquad Q-ae_s\ge0,
--   $$
--   or $c_j\succ_r c_i$ and
--   $$
--   Q'=Q+a\big(e_s-(K+1)e_r\big),\qquad Q-a(K+1)e_r\ge0.
--   $$
--   The background condition is exactly what is needed to invoke bounded manipulation potential along the move.
--
--   **Formalization Note** Profiles are functions `Ranking m → ℚ`, unit vectors are `unitVec`, and nonnegativity is pointwise. The definition does not itself require $i\ne j$; that hypothesis belongs to results about paths.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, Step 1, transfer moves (17) and their backgrounds, pp.35–37, especially footnote 18, p.37.

import Mathlib
import Definitions.Def_ManipPotential_unitVec
import Definitions.Def_ManipPotential_Ranking_Prefers

namespace ManipPotential

/-- One positive rational ballot-replacement move encoded by a transfer vector in (17),
including positivity of the background used to apply bounded manipulation potential. -/
def TransferStep {m : ℕ} (K : ℕ) (i j : Fin m)
    (Q Q' : Ranking m → ℚ) : Prop :=
  ∃ r s : Ranking m, ∃ a : ℚ, 0 < a ∧
    ((Ranking.Prefers r i j ∧
      Q' = Q + a • (((K : ℚ) + 1) • unitVec r - unitVec s) ∧
      0 ≤ Q - a • unitVec s) ∨
     (Ranking.Prefers r j i ∧
      Q' = Q + a • (unitVec s - ((K : ℚ) + 1) • unitVec r) ∧
      0 ≤ Q - a • ((K : ℚ) + 1) • unitVec r))

end ManipPotential



-- Prove2me | Definitions.Def_MaxEntOCRS_DeltaMat
-- name    : MaxEntOCRS_DeltaMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:28.844335+00:00
-- url     : https://prove2.me/theorems/478717ff-ac53-4fe5-99aa-2dbf39c6bf0b
-- title:
--   The matrix $\Delta$ of Eq. (2)
-- statement:
--   For a law $\nu$ of a random subset of a finite index set, the matrix $\Delta$ is
--   $$
--   \Delta_{ii} = p_i^2, \qquad \Delta_{ij} = p_i p_j - p_{ij} \quad (i \ne j).
--   $$
--   Off the diagonal it is minus the covariance matrix of the indicators $X_i$. On the diagonal it is $p_i^2$, because the local partition function has no $a_i b_i$ term. It enters the expansion $K = PQ - a^{\mathsf T}\Delta b + w$ and Lemma 8.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5, Eq. (2)

import Mathlib
import Definitions.Def_MaxEntOCRS_incProb
import Definitions.Def_MaxEntOCRS_pairIncProb

namespace MaxEntOCRS

/-- The matrix `Δ` of Eq. (2) (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5): `Δ_ii = p_i²` and `Δ_ij = p_i p_j − p_ij` for
`i ≠ j`. (The diagonal is `p_i²`, not the variance: the local partition function has no
`a_i b_i` term.) -/
noncomputable def DeltaMat {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Finset ι → ℝ)
    (i j : ι) : ℝ :=
  if i = j then incProb ν i ^ 2 else incProb ν i * incProb ν j - pairIncProb ν i j

end MaxEntOCRS



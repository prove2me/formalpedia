-- Prove2me | Definitions.Def_MaxEntOCRS_pairIncProb
-- name    : MaxEntOCRS_pairIncProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:15.383656+00:00
-- url     : https://prove2.me/theorems/864ded64-1e4e-4551-8eba-59158d03eeee
-- title:
--   Joint inclusion probability $p_{ij} = \mathbb E X_i X_j$
-- statement:
--   For a law $\nu$ of a random subset $F$ of a finite index set,
--   $$
--   p_{ij} = \mathbb E X_i X_j = \sum_{F \ni i, j} \nu(F),
--   $$
--   so that $\mathrm{Cov}(X_i, X_j) = p_{ij} - p_i p_j$, and $p_{ii} = p_i$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib

namespace MaxEntOCRS

/-- `p_ij = E X_i X_j = Pr_ν(i ∈ F and j ∈ F)` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5). -/
noncomputable def pairIncProb {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Finset ι → ℝ)
    (i j : ι) : ℝ :=
  ∑ F, if i ∈ F ∧ j ∈ F then ν F else 0

end MaxEntOCRS



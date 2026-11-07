-- Prove2me | Definitions.Def_MaxEntOCRS_incProb
-- name    : MaxEntOCRS_incProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:08.516602+00:00
-- url     : https://prove2.me/theorems/60f77b4b-9d20-4405-b450-7e1e694dce25
-- title:
--   Inclusion probability $p_i = \mathbb E X_i$
-- statement:
--   For a law $\nu$ of a random subset $F$ of a finite index set, $X_i = \mathbf 1\{i \in F\}$ and
--   $$
--   p_i = \mathbb E X_i = \sum_{F \ni i} \nu(F).
--   $$
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib

namespace MaxEntOCRS

/-- `p_i = E X_i = Pr_ν(i ∈ F)` for a law `ν` of a random subset `F` of a finite index set
(Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5). -/
noncomputable def incProb {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ F, if i ∈ F then ν F else 0

end MaxEntOCRS



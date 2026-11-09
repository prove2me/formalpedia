-- Prove2me | Definitions.Def_ManipPotential_Cmp
-- name    : ManipPotential_Cmp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:51.776326+00:00
-- url     : https://prove2.me/theorems/2fb854c8-d93e-439b-98bf-8078f4099b38
-- title:
--   Comparison cone $C_{ij}$ (18)–(19)
-- statement:
--   For distinct indices $i, j$ and $\lambda > 0$, the **comparison cone** $C_{ij} \subseteq \mathbb R^{m!}$ is the set of vectors $w$ with
--   $$
--   \lambda w_r \ge w_s \quad \text{for all } r, s \in \mathcal L(C) \text{ with } c_i \succ_r c_j, \qquad (18)
--   $$
--   $$
--   \lambda w_r \le w_s \quad \text{for all } r, s \in \mathcal L(C) \text{ with } c_j \succ_r c_i. \qquad (19)
--   $$
--   In the paper $\lambda = K + 1$; a nonzero vector of $C_{ij}$ is a comparison vector for $(c_i, c_j)$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Eqs. (18)–(19), p.35

import Mathlib
import Definitions.Def_ManipPotential_Ranking_Prefers

namespace ManipPotential

/-- The comparison cone `C_ij` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Eqs. (18)–(19), p.35): vectors `w ∈ ℝ^{m!}` with
`λ w_r ≥ w_s` for all `r, s` with `c_i ≻_r c_j`, and `λ w_r ≤ w_s` for all `r, s` with `c_j ≻_r c_i`.
The parameter `lam` is `λ`. -/
def Cmp {m : ℕ} (lam : ℝ) (i j : Fin m) : Set (Ranking m → ℝ) :=
  {w | (∀ r s : Ranking m, Ranking.Prefers r i j → w s ≤ lam * w r) ∧
       (∀ r s : Ranking m, Ranking.Prefers r j i → lam * w r ≤ w s)}

end ManipPotential



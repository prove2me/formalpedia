-- Prove2me | Definitions.Def_MissionAbort_rateMatrix
-- name    : MissionAbort_rateMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:50:51.272923+00:00
-- url     : https://prove2.me/theorems/8a37de3d-143c-48e8-b2f7-a5c33b8ef16c
-- title:
--   The rate matrix $Q$
-- statement:
--   The transition rate matrix $Q=(q_{ij})$ of the surrogate chain, with the off-diagonal entries of (5) and $q_{ii}=-\sum_{j\ne i}q_{ij}$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, (5), p.14

import Mathlib
import Definitions.Def_MissionAbort_hazard
import Definitions.Def_MissionAbort_offRate

namespace MissionAbort

open MeasureTheory

/-- The transition rate matrix `Q` of the surrogate chain (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1,
(5), p.14): the off-diagonal entries are `offRate`, and `q_ii = −∑_{j ≠ i} q_ij`. -/
noncomputable def rateMatrix (F : Measure ℝ) (ζ lam : ℝ) (m₁ m₂ : ℕ) :
    Matrix (Fin (m₁ + m₂ + 1)) (Fin (m₁ + m₂ + 1)) ℝ :=
  fun x y =>
    if x = y then -∑ j ∈ Finset.univ.erase x, offRate F ζ lam m₁ m₂ x j
    else offRate F ζ lam m₁ m₂ x y

end MissionAbort



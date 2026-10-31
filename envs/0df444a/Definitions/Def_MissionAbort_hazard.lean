-- Prove2me | Definitions.Def_MissionAbort_hazard
-- name    : MissionAbort_hazard
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:03.800555+00:00
-- url     : https://prove2.me/theorems/53315393-a2f5-4f33-afef-7fc52a5028f9
-- title:
--   Discrete hazard (6)
-- statement:
--   For $i\in[m_2-1]$,
--   $$
--   p_i(\lambda)=\frac{F(i/\lambda)-F((i-1)/\lambda)}{1-F((i-1)/\lambda)}.
--   $$
--
--   **Formalization Note** When $F((i-1)/\lambda)=1$ the ratio is $0/0$ on the page, and $0$ in Lean. The state concerned is reached with probability zero: at the first $i$ with $F(i/\lambda)=1$ one has $p_i(\lambda)=1$, so the rate onward vanishes.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, (6), p.14

import Mathlib

namespace MissionAbort

open MeasureTheory

/-- The discrete hazard (6) (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.14):
`pᵢ(λ) = [F(i/λ) − F((i − 1)/λ)] / [1 − F((i − 1)/λ)]`, `i ∈ [m₂ − 1]`.

**Formalization Note.** If `F((i − 1)/λ) = 1` the page's ratio is `0/0`, and Lean's value is `0`. Such a
state of the surrogate chain has probability zero of being reached: at the first `i` with `F(i/λ) = 1`,
`pᵢ(λ) = 1`, so the rate onward is `0`. -/
noncomputable def hazard (F : Measure ℝ) (lam : ℝ) (i : ℕ) : ℝ :=
  (F.real (Set.Iic ((i : ℝ) / lam)) - F.real (Set.Iic (((i : ℝ) - 1) / lam))) /
    (1 - F.real (Set.Iic (((i : ℝ) - 1) / lam)))

end MissionAbort



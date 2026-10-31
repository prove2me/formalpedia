-- Prove2me | Definitions.Def_MissionAbort_timeLaw
-- name    : MissionAbort_timeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:49.669747+00:00
-- url     : https://prove2.me/theorems/3c3b15dd-55ac-4d77-9d41-68c6ab90a52c
-- title:
--   The law of $(T_{12},T_{13},T_{23})$
-- statement:
--   The product law of three independent times: the first with law $G$, the second exponential with rate $\zeta$, and the third with law $F$. With $G,F$ the original laws it is the law of $(T_{12},T_{13},T_{23})$; with the Erlang mixtures $G^{(\lambda)},F^{(\lambda)}$ it is the law of $(T_{12}^{(\lambda)},T_{13},T_{23}^{(\lambda)})$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3.1, p.9, and Proposition 1, p.14

import Mathlib

namespace MissionAbort

open ProbabilityTheory

/-- The law of `(T₁₂, T₁₃, T₂₃)` (Sun, Hu & Ye, arXiv:2505.03225v1, §3.1, p.9): independent, with
laws `G`, exponential of rate `ζ`, and `F`. It is also used with `G⁽λ⁾`, `F⁽λ⁾` in place of `G`,
`F` (Proposition 1, p.14). -/
noncomputable def timeLaw (G : MeasureTheory.Measure ℝ) (ζ : ℝ) (F : MeasureTheory.Measure ℝ) :
    MeasureTheory.Measure (ℝ × ℝ × ℝ) :=
  G.prod ((expMeasure ζ).prod F)

end MissionAbort



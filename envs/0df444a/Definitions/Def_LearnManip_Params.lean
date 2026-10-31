-- Prove2me | Definitions.Def_LearnManip_Params
-- name    : LearnManip_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:44.058568+00:00
-- url     : https://prove2.me/theorems/ed27cf71-19c4-4621-b379-3250e625043c
-- title:
--   Model parameters $\alpha\in[0,1)$, $\gamma>0$, $\eta\ge0$
-- statement:
--   The primitive parameters of the baseline model: the discount factor $\alpha\in[0,1)$ of the firm, the distortion cost rate $\gamma>0$ and the growth factor $\eta\ge0$ of the dissemination cost rate $c_t=c_1\eta^{t-1}$.
--
--   These three numbers, with the prior and the initial cost rate, determine the manipulation problem.
--
--   **Formalization Note.** The paper has $\gamma\in\mathbb R_+$, and its proofs assume $\gamma>0$ (p.33). The values $\alpha=0$ and $\eta=0$ are in the model and are kept. All three are nonnegative reals by type.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), §2, pp.7, 9, 11

import Mathlib

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The primitive parameters of the baseline model of Keppo, Kim, Zhang, *Learning Manipulation
Through Information Dissemination* (SSRN 3465030, 2021-09-04), §2, pp.7–11: the discount factor
`α ∈ [0,1)` of (8), the distortion cost rate `γ` of (6) and the growth factor `η ∈ [0,∞)` of the
dissemination cost rate `c_t = c₁ η^{t-1}`.

**Formalization Note.** The paper has `γ ∈ ℝ₊`, and its proofs assume `γ > 0` (p.33: "`q* = ∞` when
`c = 0` or `γ = 0`"); the field `γ_pos` records this. `α = 0` and `η = 0` are in the model. All three
are `ℝ≥0`, so nonnegativity is carried by the type. -/
structure Params where
  /-- The discount factor. -/
  α : ℝ≥0
  /-- The distortion cost rate. -/
  γ : ℝ≥0
  /-- The growth factor of the dissemination cost rate. -/
  η : ℝ≥0
  α_lt_one : α < 1
  γ_pos : 0 < γ

end LearnManip



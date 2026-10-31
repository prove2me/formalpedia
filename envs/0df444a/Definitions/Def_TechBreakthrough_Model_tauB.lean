-- Prove2me | Definitions.Def_TechBreakthrough_Model_tauB
-- name    : TechBreakthrough_Model_tauB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:45.588863+00:00
-- url     : https://prove2.me/theorems/cfc7ae48-9af0-4758-bc49-39dc2d950da7
-- title:
--   The stopping time $\tau_b$
-- statement:
--   For a starting level $m$ of the maximum process,
--
--   $$\tau_b\equiv\inf\{t\ge0:M_t\ge\underline m\text{ and }x_R\le X_t\le b(M_t)\},\qquad\inf\emptyset=\infty,$$
--
--   the hitting time of the stopping region. It need not be finite.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Theorem 1 (iii), p.19; p.27

import Definitions.Def_TechBreakthrough_Model
import Definitions.Def_TechBreakthrough_runningMax
import Definitions.Def_TechBreakthrough_discountedAt

open scoped NNReal

namespace TechBreakthrough

namespace Model

variable (M : Model)

/-- The stopping time `τ_b = inf {t ≥ 0 : M_t ≥ m̲ and x_R ≤ X_t ≤ b(M_t)}`, for the maximum process
started at `m`, arXiv:2106.05112v1, Theorem 1 (iii), p.19; `inf ∅ = ∞`. -/
noncomputable def tauB (xR mLow : ℝ) (b : ℝ → ℝ) (m : ℝ) (ω : M.Ω) : WithTop ℝ≥0 :=
  firstTime {t | mLow ≤ runningMax m t ω ∧ xR ≤ M.X t ω ∧ M.X t ω ≤ b (runningMax m t ω)}

end Model

end TechBreakthrough



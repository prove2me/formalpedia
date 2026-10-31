-- Prove2me | Definitions.Def_MissionAbort_jointExpectation
-- name    : MissionAbort_jointExpectation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:03.061377+00:00
-- url     : https://prove2.me/theorems/956cd803-2c11-430e-acfb-a20682ef5367
-- title:
--   The joint expectation of times and signals
-- statement:
--   For a law $\mathcal L$ of the transition times, the expectation of a function $f$ of the times $T$ and the signals $Y_{1:N}$, when $T\sim\mathcal L$ and the signals have the kernel of the mission given $T$:
--   $$
--   \sum_{y}\int f(u,y)\prod_{n=1}^N e\big(\mathrm{state}(u;n\delta),y_n\big)\,\mathrm d\mathcal L(u).
--   $$
--   The same kernel is used for the original and the surrogate times.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, p.EC.2

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_emit
import Definitions.Def_MissionAbort_state
import Definitions.Def_MissionAbort_signalLikelihood

namespace MissionAbort

open MeasureTheory

/-- The expectation `E[f(T, Y_{1:N})]` when `T` has law `L` and, given `T = u`, the signals have the
conditional law `signalLikelihood M u` (Sun, Hu & Ye, arXiv:2505.03225v1, Appendix A.2, p.EC.2).
The same emission kernel is used for the original and the surrogate times ("by our construction of the
surrogate signals", p.EC.2). -/
noncomputable def jointExpectation {K : ℕ} (M : Model K) (L : Measure (ℝ × ℝ × ℝ))
    (f : (ℝ × ℝ × ℝ) × (Fin M.N → Fin (K + 1)) → ℝ) : ℝ :=
  ∑ y : Fin M.N → Fin (K + 1), ∫ u, f (u, y) * signalLikelihood M u y ∂L

end MissionAbort



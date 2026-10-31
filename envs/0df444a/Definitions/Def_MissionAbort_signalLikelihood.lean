-- Prove2me | Definitions.Def_MissionAbort_signalLikelihood
-- name    : MissionAbort_signalLikelihood
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:50:02.919987+00:00
-- url     : https://prove2.me/theorems/be26201e-0b2b-4317-af27-4842da119a51
-- title:
--   The signal kernel
-- statement:
--   The conditional probability of a signal vector $y=(y_1,\dots,y_N)$ given transition times $u$:
--   $$
--   \prod_{n=1}^N e\big(\mathrm{state}(u;n\delta),y_n\big),
--   $$
--   where $e$ is the emission probability. It expresses that the signals are conditionally independent given the failure process, with $Y_n$ depending only on the state at $n\delta$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, p.EC.2

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_emit
import Definitions.Def_MissionAbort_state

namespace MissionAbort

/-- The conditional probability of the signal vector `y = (y₁, …, y_N)` given the transition times
`u` (Sun, Hu & Ye, arXiv:2505.03225v1, Appendix A.2, p.EC.2): the signals are conditionally
independent, with the `n`-th drawn from the state at time `nδ`.

**Formalization Note.** `y i` with `i : Fin N` is the page's `y_{i+1}`, read at time `(i + 1)δ`. -/
noncomputable def signalLikelihood {K : ℕ} (M : Model K) (u : ℝ × ℝ × ℝ)
    (y : Fin M.N → Fin (K + 1)) : ℝ :=
  ∏ i : Fin M.N, emit M (state u (((i.val + 1 : ℕ) : ℝ) * M.δ)) (y i)

end MissionAbort



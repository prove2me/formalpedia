-- Prove2me | Definitions.Def_MissionAbort_costContinue
-- name    : MissionAbort_costContinue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:44.114482+00:00
-- url     : https://prove2.me/theorems/ace86c65-5e35-40a8-b2ec-9fc304f203db
-- title:
--   The continue cost-to-go $\mathbb C_c$
-- statement:
--   The cost-to-go of continuing at time $n\delta$ given $Y_{1:n}=y$:
--   $$
--   \mathbb C_c(n,y)=(C_s+C_m)\,\mathbb P(\xi\le(n+1)\delta\mid Y_{1:n}=y)+\sum_{k\in[K]}\mathbb P(Y_{n+1}=k\mid Y_{1:n}=y)\,\mathbb C(n+1,y\cdot k).
--   $$
--   At $n=0$ this is the optimal value of the problem, which has no decision at time $0$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, p.EC.4; (12), p.17

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_histEvent
import Definitions.Def_MissionAbort_condProb
import Definitions.Def_MissionAbort_costAbort
import Definitions.Def_MissionAbort_continueStep
import Definitions.Def_MissionAbort_value

namespace MissionAbort

open MeasureTheory

/-- The cost-to-go of continuing at time `nδ` given `Y_{1:n} = y` (Sun, Hu & Ye, arXiv:2505.03225v1,
Appendix A.2, p.EC.4; (12), p.17): `Cc(n, y) = (Cs + Cm) P(ξ ≤ (n + 1)δ | Y_{1:n} = y) +
∑_{k ∈ [K]} P(Y_{n+1} = k | Y_{1:n} = y) C(n + 1, y·k)`. At `n = 0` this is the optimal value of the
problem, which has no decision at time `0`. -/
noncomputable def costContinue {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) (n : ℕ)
    (y : Fin n → Fin (K + 1)) : ℝ :=
  continueStep M μ S Y n y (fun k =>
    value M μ S Y (n + 1) (Fin.snoc (α := fun _ => Fin (K + 1)) y k.succ))

end MissionAbort



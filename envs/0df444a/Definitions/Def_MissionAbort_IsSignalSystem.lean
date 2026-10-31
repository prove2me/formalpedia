-- Prove2me | Definitions.Def_MissionAbort_IsSignalSystem
-- name    : MissionAbort_IsSignalSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:54.047138+00:00
-- url     : https://prove2.me/theorems/ed3e8144-5662-4a3e-b78d-792f541fab30
-- title:
--   The structure shared by the two systems
-- statement:
--   A probability space with a state process $S$ and signals $Y$ is a signal system if the state at each grid time and the signals are measurable, the failed state is absorbing on the decision grid almost surely, and almost surely $Y_n=0$ exactly when the system has failed at time $n\delta$, for $n\in[N]$.
--
--   These are the properties of the failure process that the dynamic programming argument needs: the failure is self-announcing, and it persists.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3, pp.9–10; §4.1, p.14

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_decisionGrid

namespace MissionAbort

open MeasureTheory

/-- The two properties the abort problem needs from a state-signal pair `(S, Y)`, shared by the original
and the surrogate system (Sun, Hu & Ye, arXiv:2505.03225v1, pp.9–10, p.14): measurability at the times
read, the failed state is absorbing on the decision grid, and the failure is self-announcing, that is,
`Yₙ = 0` exactly when the system has failed at `nδ`, almost surely. -/
structure IsSignalSystem {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  measurable_S : ∀ t ∈ decisionGrid M, Measurable (S t)
  measurable_Y : ∀ n, 1 ≤ n → n ≤ M.N → Measurable (Y n)
  failed_absorbing : ∀ᵐ ω ∂μ, ∀ s ∈ decisionGrid M, ∀ t ∈ decisionGrid M, s ≤ t →
    S s ω = .failed → S t ω = .failed
  signal_zero_iff : ∀ᵐ ω ∂μ, ∀ n, 1 ≤ n → n ≤ M.N → (Y n ω = 0 ↔ S (n * M.δ) ω = .failed)

end MissionAbort



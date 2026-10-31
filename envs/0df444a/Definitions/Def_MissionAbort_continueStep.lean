-- Prove2me | Definitions.Def_MissionAbort_continueStep
-- name    : MissionAbort_continueStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:27.591504+00:00
-- url     : https://prove2.me/theorems/1f6b97b0-4f06-4fa6-bd2b-0f84beeeb356
-- title:
--   One step of the continuation recursion
-- statement:
--   Given values $V(k)$ for the next signal $k\in[K]$, the quantity
--   $$
--   (C_s+C_m)\,\mathbb P(\xi\le(n+1)\delta\mid Y_{1:n}=y)+\sum_{k\in[K]}\mathbb P(Y_{n+1}=k\mid Y_{1:n}=y)\,V(k).
--   $$
--   The sum is over $[K]$, and the failure mass is in the first term.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, (12), p.17; Appendix A.2, p.EC.4

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_histEvent
import Definitions.Def_MissionAbort_condProb

namespace MissionAbort

open MeasureTheory

/-- One step of the continuation recursion (Sun, Hu & Ye, arXiv:2505.03225v1, (12), p.17 in signal
coordinates, and Appendix A.2, p.EC.4): given values `V k` for the next signal `k ∈ [K]`,
`(Cs + Cm) P(ξ ≤ (n + 1)δ | Y_{1:n} = y) + ∑_{k ∈ [K]} P(Y_{n+1} = k | Y_{1:n} = y) V(k)`.

**Formalization Note.** The sum is over `[K]`, not `{0, …, K}`: the failure mass is the first term.
`k : Fin K` is the signal value `k.succ`. -/
noncomputable def continueStep {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) (n : ℕ)
    (y : Fin n → Fin (K + 1)) (V : Fin K → ℝ) : ℝ :=
  (M.Cs + M.Cm) * condProb μ {ω | S (((n + 1 : ℕ) : ℝ) * M.δ) ω = .failed} (histEvent Y n y) +
    ∑ k : Fin K, condProb μ {ω | Y (n + 1) ω = k.succ} (histEvent Y n y) * V k

end MissionAbort



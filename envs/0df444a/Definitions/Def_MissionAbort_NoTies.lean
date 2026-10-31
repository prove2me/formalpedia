-- Prove2me | Definitions.Def_MissionAbort_NoTies
-- name    : MissionAbort_NoTies
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:39.57815+00:00
-- url     : https://prove2.me/theorems/4be4db22-830a-4d47-87af-85eae4bcef36
-- title:
--   Reading of the uniqueness assumption
-- statement:
--   The two costs-to-go differ, $\mathbb C_{ab}(n,y)\ne\mathbb C_c(n,y)$, at every $n\in[N-1]$ and every history $y\in[K]^n$ of positive probability.
--
--   This is how the proof of Theorem 1 uses the sentence "We assume the set of optimal actions is unique" of p.11 (pp.EC.3–EC.4). Read as a statement that the minimizer of (1) is a singleton, the sentence cannot hold for $N\ge 3$, because rules at histories after an earlier abort do not affect the cost.
--
--   **Formalization Note** The restriction to $[K]^n$ is necessary: both costs equal $C_m+C_s$ when $y_n=0$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4, p.11; Appendix A.2, pp.EC.3–EC.4

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_histEvent
import Definitions.Def_MissionAbort_condProb
import Definitions.Def_MissionAbort_costAbort
import Definitions.Def_MissionAbort_continueStep
import Definitions.Def_MissionAbort_value
import Definitions.Def_MissionAbort_costContinue

namespace MissionAbort

open MeasureTheory

/-- The reading of the uniqueness assumption of p.11 (Sun, Hu & Ye, arXiv:2505.03225v1, §4, p.11,
"We assume the set of optimal actions is unique"), as the proof uses it (Appendix A.2, pp.EC.3–EC.4,
"`Cab(N − 1, y) ≠ Cc(N − 1, y)`"): the two costs-to-go differ at every `n ∈ [N − 1]` and every
history `y ∈ [K]ⁿ` of positive probability.

**Formalization Note.** Uniqueness read as "the minimizer of (1) is a singleton" is unsatisfiable for
`N ≥ 3`, because rules at histories after an earlier abort do not affect the cost. The restriction to
`[K]ⁿ` is needed since `Cab = Cc = Cm + Cs` when `yₙ = 0`. -/
def NoTies {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → n < M.N → ∀ y : Fin n → Fin (K + 1), (∀ i, y i ≠ 0) →
    0 < μ.real (histEvent Y n y) → costAbort M μ S Y n y ≠ costContinue M μ S Y n y

end MissionAbort



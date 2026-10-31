-- Prove2me | Definitions.Def_MissionAbort_IsSeqOptimal
-- name    : MissionAbort_IsSeqOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:36.070636+00:00
-- url     : https://prove2.me/theorems/e3613544-57ee-4784-b7e0-bb11fc68a409
-- title:
--   Rules that compare the costs-to-go
-- statement:
--   A rule family compares the costs-to-go if at every $n\in[N-1]$ and every history $y\in[K]^n$ of positive probability it aborts only if $\mathbb C_{ab}(n,y)\le\mathbb C_c(n,y)$ and continues only if $\mathbb C_c(n,y)\le\mathbb C_{ab}(n,y)$.
--
--   **Formalization Note** Ties may go either way, which covers the strict rule of p.EC.2 and the smallest-$\mathfrak T^*$ stipulation of pp.11, 15, which disagree at ties. Histories after an earlier abort are included.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, p.EC.2

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_Rule
import Definitions.Def_MissionAbort_histEvent
import Definitions.Def_MissionAbort_condProb
import Definitions.Def_MissionAbort_costAbort
import Definitions.Def_MissionAbort_continueStep
import Definitions.Def_MissionAbort_value
import Definitions.Def_MissionAbort_costContinue

namespace MissionAbort

open MeasureTheory

/-- The rule family `a` compares the two costs-to-go (Sun, Hu & Ye, arXiv:2505.03225v1, Appendix A.2,
p.EC.2, "can be determined by comparing the two costs-to-go"): at every `n ∈ [N − 1]` and every history
`y ∈ [K]ⁿ` of positive probability, it aborts only if `Cab ≤ Cc` and continues only if `Cc ≤ Cab`.

**Formalization Note.** Ties may go either way, which covers both the strict rule of p.EC.2 and the
smallest-`𝔗` stipulation of pp.11, 15, which disagree at ties. Histories after an earlier abort are
included: the signals keep running. Histories with a `0` are left to `IsAdmissible`, and null histories
carry no information. -/
def IsSeqOptimal {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) (a : Rule K) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → n < M.N → ∀ y : Fin n → Fin (K + 1), (∀ i, y i ≠ 0) →
    0 < μ.real (histEvent Y n y) →
      (a n y = true → costAbort M μ S Y n y ≤ costContinue M μ S Y n y) ∧
      (a n y = false → costContinue M μ S Y n y ≤ costAbort M μ S Y n y)

end MissionAbort



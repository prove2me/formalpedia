-- Prove2me | Definitions.Def_MissionAbort_value
-- name    : MissionAbort_value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:50:50.413715+00:00
-- url     : https://prove2.me/theorems/e06caee2-9cbe-4fb3-926a-7f72a3190c82
-- title:
--   The optimal cost-to-go $\mathbb C$
-- statement:
--   The optimal cost-to-go, defined by backward recursion:
--   $$
--   \mathbb C(N,y)=(C_s+C_m)\,\mathbb P(\xi\le N\delta+w_N\mid Y_{1:N}=y),\qquad \mathbb C(n,y)=\min\{\mathbb C_{ab}(n,y),\mathbb C_c(n,y)\},\ n\le N-1.
--   $$
--
--   **Formalization Note** The module also holds the auxiliary recursion on the number of remaining epochs.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, p.EC.3; (14), p.17

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_histEvent
import Definitions.Def_MissionAbort_condProb
import Definitions.Def_MissionAbort_costAbort
import Definitions.Def_MissionAbort_continueStep

namespace MissionAbort

open MeasureTheory

/-- The auxiliary backward recursion of `value`, indexed by the number `d` of remaining epochs.
`d = 0` is the terminal cost, and each further step takes the smaller of the two costs-to-go. -/
noncomputable def valueAux {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) :
    (d n : ℕ) → (Fin n → Fin (K + 1)) → ℝ
  | 0, n, y =>
    (M.Cs + M.Cm) * condProb μ {ω | S (n * M.δ + M.w n) ω = .failed} (histEvent Y n y)
  | d + 1, n, y =>
    min (costAbort M μ S Y n y)
      (continueStep M μ S Y n y (fun k =>
        valueAux M μ S Y d (n + 1) (Fin.snoc (α := fun _ => Fin (K + 1)) y k.succ)))

/-- The optimal cost-to-go `C(n, y)` (Sun, Hu & Ye, arXiv:2505.03225v1, Appendix A.2, p.EC.3; (9), (14),
pp.17): `C(N, y) = (Cs + Cm) P(ξ ≤ Nδ + w_N | Y_{1:N} = y)`, and for `n ≤ N − 1`,
`C(n, y) = min{Cab(n, y), Cc(n, y)}`. -/
noncomputable def value {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) (n : ℕ) (y : Fin n → Fin (K + 1)) : ℝ :=
  valueAux M μ S Y (M.N - n) n y

end MissionAbort



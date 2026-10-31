-- Prove2me | Definitions.Def_MissionAbort_cost
-- name    : MissionAbort_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:32.069987+00:00
-- url     : https://prove2.me/theorems/cb640481-bc8e-49c2-9547-52f43bfb15a6
-- title:
--   The cost function
-- statement:
--   The cost of ending with cluster $c$ at stopping index $n$:
--   $$
--   C(c,n\delta)=(C_m+C_s)\mathbb 1\{c=\text{failed}\}+C_m\mathbb 1\{c\ne\text{failed},\ n<N\}.
--   $$
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4, p.11

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model

namespace MissionAbort

/-- The cost function (Sun, Hu & Ye, arXiv:2505.03225v1, §4, p.11):
`C(X, 𝔗) = (Cm + Cs) 𝟙{X = 3} + Cm 𝟙{X < 3, 𝔗 < H}`, with `𝔗 = nδ`, so `𝔗 < H` is `n < N`. -/
noncomputable def cost {K : ℕ} (M : Model K) (c : Cluster) (n : ℕ) : ℝ :=
  (if c = .failed then M.Cm + M.Cs else 0) + (if c ≠ .failed ∧ n < M.N then M.Cm else 0)

end MissionAbort



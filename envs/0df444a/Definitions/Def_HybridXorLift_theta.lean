-- Prove2me | Definitions.Def_HybridXorLift_theta
-- name    : HybridXorLift_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:18:46.439935+00:00
-- url     : https://prove2.me/theorems/7b06fc1a-4ef4-49df-a132-e6c6eb0672d1
-- title:
--   Discount factor $\theta_i(h)$
-- statement:
--   With $a = 1/100$, the **discount factor** of block $i$ at history $h$ is
--   $$
--   \theta_i(h) = \exp\Big[\frac{2}{q}\big(a r + q - w_i(h)\big)\Big],
--   $$
--   which decreases as the block is queried; the extra $q$ is a buffer that keeps the factor above one in the step where the block becomes revealed.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §4.2, Eq. (4.10), p.16 (PDF p.18)

import Definitions.Def_HybridXorLift_cumWeight

namespace HybridXorLift

/-- The discount factor `θ_i(h) = exp[(2/q)(ar + q − w_i(h))]` with `a = 1/100` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §4.2,
Eq. (4.10), p.16 (PDF p.18)). -/
noncomputable def theta {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α) (q : ℕ)
    (h : List (Step (Fin n × Fin r))) (i : Fin n) : ℝ :=
  Real.exp ((2 / (q : ℝ)) * ((r : ℝ) / 100 + (q : ℝ) - cumWeight A h i))

end HybridXorLift



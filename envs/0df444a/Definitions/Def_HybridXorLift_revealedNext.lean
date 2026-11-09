-- Prove2me | Definitions.Def_HybridXorLift_revealedNext
-- name    : HybridXorLift_revealedNext
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:19:06.615286+00:00
-- url     : https://prove2.me/theorems/4560e05a-5c95-42bd-bca9-ecb723194421
-- title:
--   Common revealed set $J^+(h)$ of the children
-- statement:
--   All children of a history $h$ have the same cumulative weights $w_i(hy) = w_i(h) + \beta_i(h)$, and therefore the same revealed set
--   $$
--   J^+(h) = \{\, i \in [n] : w_i(h) + \beta_i(h) \ge r/100 \,\}.
--   $$
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §4.2, p.15 (PDF p.17)

import Definitions.Def_HybridXorLift_cumWeight

namespace HybridXorLift

/-- The common revealed set `J⁺(h)` of the children of `h` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §4.2, p.15 (PDF p.17)): "All
children of h have the same weights `w_i(hy) = w_i(h) + β_i(h)`, and therefore the same revealed
set, which we denote `J⁺(h)`"; so `J⁺(h) = {i : w_i(h) + β_i(h) ≥ ar}` with `a = 1/100`. -/
noncomputable def revealedNext {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α)
    (h : List (Step (Fin n × Fin r))) : Finset (Fin n) :=
  Finset.univ.filter fun i => (r : ℝ) / 100 ≤ cumWeight A h i + queryWeightAt A h i

end HybridXorLift



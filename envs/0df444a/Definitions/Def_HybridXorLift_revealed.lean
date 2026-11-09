-- Prove2me | Definitions.Def_HybridXorLift_revealed
-- name    : HybridXorLift_revealed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:18:39.026244+00:00
-- url     : https://prove2.me/theorems/b00bca27-e36b-4a89-b2b3-2b6b4314fa0e
-- title:
--   Revealed set $J(h)$
-- statement:
--   Set $a = 1/100$. The **revealed set** of a history $h$ is
--   $$
--   J(h) = \{\, i \in [n] : w_i(h) \ge a r \,\},
--   $$
--   the blocks that have received query weight at least $r/100$ before $h$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §4.2, Eq. (4.8), p.15 (PDF p.17)

import Definitions.Def_HybridXorLift_cumWeight

namespace HybridXorLift

/-- The revealed set `J(h) = {i ∈ [n] : w_i(h) ≥ ar}` with `a = 1/100` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §4.2, Eq. (4.8),
p.15 (PDF p.17)). -/
noncomputable def revealed {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α)
    (h : List (Step (Fin n × Fin r))) : Finset (Fin n) :=
  Finset.univ.filter fun i => (r : ℝ) / 100 ≤ cumWeight A h i

end HybridXorLift



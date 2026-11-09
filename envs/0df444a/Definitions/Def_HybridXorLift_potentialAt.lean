-- Prove2me | Definitions.Def_HybridXorLift_potentialAt
-- name    : HybridXorLift_potentialAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:21:50.657461+00:00
-- url     : https://prove2.me/theorems/42dcb1f0-576e-4be5-8650-6a9ab1c9104f
-- title:
--   Weighted potential along an outer string $F_z(h)$
-- statement:
--   For an outer string $z$ and a history $h$,
--   $$
--   F_z(h) = F_{J(h),\, z_{J(h)}}(h),
--   $$
--   the weighted potential with the blocks revealed at $h$ fixed to their values in $z$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §4.2, p.16 (PDF p.18)

import Definitions.Def_HybridXorLift_weightedPotential
import Definitions.Def_HybridXorLift_revealed

namespace HybridXorLift

/-- The weighted potential along an outer string, `F_z(h) = F_{J(h), z_{J(h)}}(h)` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §4.2,
p.16 (PDF p.18)).

**Formalization Note** The partial assignment `z_{J(h)}` is `z` itself, of which only the values
on `J(h)` are read. -/
noncomputable def potentialAt {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α)
    (q : ℕ) (z : Fin n → Bool) (h : List (Step (Fin n × Fin r))) : ℝ :=
  weightedPotential A q (revealed A h) z h

end HybridXorLift



-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_firstSegment
-- name    : KawasakiSOS_Threshold_firstSegment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:10.102906+00:00
-- url     : https://prove2.me/theorems/eb0d1bdf-ee17-4193-8ce0-7b8c4c43e2df
-- title:
--   The segment of the first occurrence of a transition
-- statement:
--   A transition can occur more than once on a canonical path. This definition returns the segment containing its first occurrence.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Segment

namespace KawasakiSOS.Threshold

/-- The segment containing the first occurrence of the transition `e`: "at its first occurrence, if it occurs more than once".

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15). -/
def firstSegment {n k : ℕ} [NeZero k] (segs : List (Segment k × List (Config n k)))
    (e : Config n k × Config n k) : Option (Segment k) :=
  (segs.find? fun p => decide (e ∈ DiaconisStroock.Poincare.pathEdges p.2)).map Prod.fst

end KawasakiSOS.Threshold



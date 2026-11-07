-- Prove2me | Definitions.Def_CutwidthCircuitLB_IsOpenAt
-- name    : CutwidthCircuitLB_IsOpenAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:36.005195+00:00
-- url     : https://prove2.me/theorems/4971b70f-a021-4c3e-bc92-917638ddf029
-- title:
--   A vertex is open at a threshold
-- statement:
--   A vertex with three edge scores $a, b, c$ is **open at the threshold** $t$ if $t$ lies strictly inside the range of its three scores: $\min(a, b, c) < t < \max(a, b, c)$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Appendix A, p.21

import Mathlib

namespace CutwidthCircuitLB

/-- A vertex with edge scores `a, b, c` is **open at the threshold `t`** if `t` lies strictly inside
the range of its three scores (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Appendix A, p.21): `min(a, b, c) < t < max(a, b, c)`. -/
def IsOpenAt (t a b c : ℝ) : Prop :=
  min a (min b c) < t ∧ t < max a (max b c)

end CutwidthCircuitLB



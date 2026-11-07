-- Prove2me | Definitions.Def_TreeCoverLB_padMetric
-- name    : TreeCoverLB_padMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:01.795211+00:00
-- url     : https://prove2.me/theorems/40c269fe-ffc8-4ef7-8c10-1d2c57a67f6b
-- title:
--   The padded metric on $X$ plus $m$ new points
-- statement:
--   Given a metric $d$ on $X$, a number $Q$ and $m$ new points, the **padded metric** on $X\sqcup\{1,\dots,m\}$ agrees with $d$ on $X$, is $0$ from a point to itself, and equals $Q$ between any two distinct points at least one of which is new.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), proof of Theorem 4.3, p.17 (PDF p.19): add the remaining n − N_r terminals at common distance Q

import Mathlib

open Classical

namespace TreeCoverLB

/-- The **padded metric** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), proof of Theorem 4.3, p.17 (PDF p.19)): add `m` new points to `X`
"so that the distance between every two distinct points, at least one of which is a new point, is a
common value `Q`". On `X ⊕ Fin m` (old points `inl x`, new points `inr j`): `d` between two old
points, `0` from a point to itself, and `Q` between any other two distinct points. -/
noncomputable def padMetric {X : Type*} {m : ℕ} (d : X → X → ℝ) (Q : ℝ) : X ⊕ Fin m → X ⊕ Fin m → ℝ
  | .inl x, .inl y => d x y
  | a, b => if a = b then 0 else Q

end TreeCoverLB



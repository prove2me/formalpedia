-- Prove2me | Definitions.Def_DelaunayStretch_GateState
-- name    : DelaunayStretch_GateState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:49:30.999661+00:00
-- url     : https://prove2.me/theorems/d8251af6-d2eb-4616-87e9-43008c992707
-- title:
--   Gate states $s=(O,G,\delta)$
-- statement:
--   A **gate state** is a triple $s=(O,G,\delta)$, where $O$ is a closed disk with center $o$ and radius $r>0$, $G=[a_G,b_G]$ is a chord of $\partial O$ with $y(a_G)>0>y(b_G)$, and
--
--   $$
--   \delta\in[-|G|,|G|],\qquad |G|=\|a_G-b_G\| .
--   $$
--
--   We denote by $c(s)$ the point where the $x$-axis crosses $G$.
--
--   A gate state records what the rest of a disk chain needs to know after a gate: the next disk, the gate, and the difference of the shortest distances to its two ends.
--
--   **Formalization Note** A gate state is a record (disk, upper end, lower end, $\delta$) with the conditions as a separate predicate.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition 3.4, p.17

import Mathlib
import Definitions.Def_DelaunayStretch_Disk

namespace DelaunayStretch

/-- The data of a **gate state** `s = (O, G, δ)` (Definition 3.4, p.17): a closed disk `O`, the
ends `aG` (upper) and `bG` (lower) of the gate `G = [aG, bG]`, and the difference `δ`. The
conditions are `GateState.IsGateState`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition 3.4, p.17.

**Formalization Note** Points of `ℝ²` are complex numbers (`x = re`, `y = im`). -/
structure GateState where
  /-- the disk `O` -/
  O : Disk
  /-- the upper end `aG` of the gate -/
  aG : ℂ
  /-- the lower end `bG` of the gate -/
  bG : ℂ
  /-- the difference `δ` -/
  δ : ℝ

namespace GateState

/-- **Gate state** (Definition 3.4, p.17): `O` is a closed disk with center `o` and radius
`r > 0`, `G = [aG, bG]` is a chord of `∂O` with `y(aG) > 0 > y(bG)`, and `δ ∈ [−|G|, |G|]`,
where `|G| = ‖aG − bG‖`. -/
def IsGateState (s : GateState) : Prop :=
  0 < s.O.radius ∧ s.aG ∈ s.O.boundary ∧ s.bG ∈ s.O.boundary ∧
    0 < s.aG.im ∧ s.bG.im < 0 ∧ |s.δ| ≤ dist s.aG s.bG

/-- `c(s)`: the point where the `x`-axis crosses the gate `G` (Definition 3.4, p.17). -/
noncomputable def crossing (s : GateState) : ℂ := axisCrossing s.aG s.bG

end GateState

end DelaunayStretch



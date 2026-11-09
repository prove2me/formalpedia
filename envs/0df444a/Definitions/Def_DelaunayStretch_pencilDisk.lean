-- Prove2me | Definitions.Def_DelaunayStretch_pencilDisk
-- name    : DelaunayStretch_pencilDisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:52:03.973591+00:00
-- url     : https://prove2.me/theorems/8b7f3c76-dcea-4c77-a9fa-9c438989beaf
-- title:
--   The pencil $O(X)$ of a segment
-- statement:
--   Let $G=[a_G,b_G]$ be a segment with $y(a_G)>0>y(b_G)$, midpoint $M$ and unit normal $\nu=-i(a_G-b_G)/\|a_G-b_G\|$, which has positive $x$-component. For $X\in\mathbb R$, $O(X)$ is the closed disk with
--
--   $$
--   o(X)=M+X\nu,\qquad r(X)=\sqrt{X^2+|G|^2/4},
--   $$
--
--   and $s(X)=(O(X),G,\delta)$ is the corresponding triple for a given $\delta$.
--
--   These are the disks whose circles pass through $a_G$ and $b_G$; sliding the disk along this pencil is the second stage of a step in the proof of Theorem 4.7.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma 4.4, p.25

import Mathlib
import Definitions.Def_DelaunayStretch_GateState

namespace DelaunayStretch

open Complex

/-- The unit normal vector `ν = −i(aG − bG)/‖aG − bG‖` of the segment `[aG, bG]`; it has
positive `x`-component when `y(aG) > y(bG)` (Lemma 4.4, p.25). -/
noncomputable def segNormal (aG bG : ℂ) : ℂ := (-I) * (aG - bG) / ((dist aG bG : ℝ) : ℂ)

/-- **The pencil of a segment** (Lemma 4.4, p.25): for the segment `G = [aG, bG]` with midpoint
`M` and unit normal `ν` with positive `x`-component, and `X ∈ ℝ`, the closed disk `O(X)` with
center `o(X) = M + Xν` and radius `r(X) = √(X² + |G|²/4)`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Lemma 4.4, p.25. -/
noncomputable def pencilDisk (aG bG : ℂ) (X : ℝ) : Disk :=
  ⟨(aG + bG) / 2 + (X : ℂ) * segNormal aG bG, Real.sqrt (X ^ 2 + dist aG bG ^ 2 / 4)⟩

/-- The triple `s(X) = (O(X), G, δ)` along the pencil of `G = [aG, bG]` (Lemma 4.4(2), p.25). -/
noncomputable def pencilState (aG bG : ℂ) (δ X : ℝ) : GateState :=
  ⟨pencilDisk aG bG X, aG, bG, δ⟩

end DelaunayStretch



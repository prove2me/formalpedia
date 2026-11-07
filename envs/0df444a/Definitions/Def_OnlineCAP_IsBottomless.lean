-- Prove2me | Definitions.Def_OnlineCAP_IsBottomless
-- name    : OnlineCAP_IsBottomless
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:40.85325+00:00
-- url     : https://prove2.me/theorems/db968c3b-edd2-48c3-8081-3ddd68cb8478
-- title:
--   Bottomless rectangle
-- statement:
--   A **bottomless rectangle** is a region $[a,b]\times(-\infty,c]\subseteq\mathbb R^2$ for some $a,b,c\in\mathbb R$. Bottomless rectangles are the requests of the online rounding algorithm of §4.1; topless and leftless rectangles are their rotations.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1, p.15; Algorithm 2, p.18

import Mathlib

namespace OnlineCAP

/-- **Bottomless rectangle.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1, p.15 and Algorithm 2, p.18 (PDF p.18): "foreach arrival
of bottomless rectangle Rt = [at, bt] × (−∞, ct]".

A bottomless rectangle is `[a, b] × (−∞, c]` for some `a, b, c ∈ ℝ`. -/
def IsBottomless (S : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c : ℝ, S = Set.Icc a b ×ˢ Set.Iic c

end OnlineCAP



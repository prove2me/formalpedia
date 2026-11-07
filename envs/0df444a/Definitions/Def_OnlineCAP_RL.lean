-- Prove2me | Definitions.Def_OnlineCAP_RL
-- name    : OnlineCAP_RL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:34.161445+00:00
-- url     : https://prove2.me/theorems/989ac713-5a00-48ad-a18d-bd2122025d87
-- title:
--   The leftless rectangle R_L(a, b) of a cycle cut
-- statement:
--   For the arc $C=[a,b]=\{v_a,\dots,v_b\}$ of the cycle,
--   $$R_L(a,b)=(-\infty,a-1]\times[a,b]\subseteq\mathbb R^2 .$$
--   A link $\{v_i,v_j\}$, $i<j$, entering $C$ through its left boundary ($i<a\le j\le b$) has its point $(i,j)$ in $R_L(a,b)$.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §3.1, p.11; p.5

import Mathlib

namespace OnlineCAP

/-- **The leftless rectangle of a cycle cut.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §3.1, p.11 (PDF p.11) (also p.5): "For each
arriving cut C = [a, b], we create two rectangles which are subsets of R2: RL(a, b) =
(−∞, a − 1] × [a, b] and RT (a, b) = [a, b] × [b + 1, ∞)."

`RL a b = (−∞, a − 1] × [a, b]` for natural numbers `a, b`. -/
def RL (a b : ℕ) : Set (ℝ × ℝ) :=
  Set.Iic ((a : ℝ) - 1) ×ˢ Set.Icc (a : ℝ) (b : ℝ)

end OnlineCAP



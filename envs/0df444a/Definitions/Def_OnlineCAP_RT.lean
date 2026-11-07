-- Prove2me | Definitions.Def_OnlineCAP_RT
-- name    : OnlineCAP_RT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:36.121204+00:00
-- url     : https://prove2.me/theorems/75fce005-52c6-41e9-9eec-7c0a6f87d8af
-- title:
--   The topless rectangle R_T(a, b) of a cycle cut
-- statement:
--   For the arc $C=[a,b]=\{v_a,\dots,v_b\}$ of the cycle,
--   $$R_T(a,b)=[a,b]\times[b+1,\infty)\subseteq\mathbb R^2 .$$
--   A link $\{v_i,v_j\}$, $i<j$, leaving $C$ through its right boundary ($a\le i\le b<j$) has its point $(i,j)$ in $R_T(a,b)$.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §3.1, p.11; p.5

import Mathlib

namespace OnlineCAP

/-- **The topless rectangle of a cycle cut.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §3.1, p.11 (PDF p.11): "RT (a, b) =
[a, b] × [b + 1, ∞)".

`RT a b = [a, b] × [b + 1, ∞)` for natural numbers `a, b`. -/
def RT (a b : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc (a : ℝ) (b : ℝ) ×ˢ Set.Ici ((b : ℝ) + 1)

end OnlineCAP



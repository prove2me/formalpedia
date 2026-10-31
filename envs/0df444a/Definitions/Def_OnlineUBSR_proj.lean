-- Prove2me | Definitions.Def_OnlineUBSR_proj
-- name    : OnlineUBSR_proj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:14.277582+00:00
-- url     : https://prove2.me/theorems/eba88baa-b2d6-4dd1-89cf-8868d467e894
-- title:
--   Projection $\Gamma(x)=\min(\max(t_l,x),t_u)$
-- statement:
--   For reals $t_l$ and $t_u$, the projection operator is
--
--   $$
--   \Gamma(x)=\min\big(\max(t_l,x),\,t_u\big),\qquad x\in\mathbb R .
--   $$
--
--   When $t_l\le t_u$ it maps every real number to the nearest point of $[t_l,t_u]$; the estimator clips each iterate to this interval, inside which $SR_\lambda(X)$ lies.
--
--   **Formalization Note** The formula is taken literally; every theorem of the mission assumes $t_l<t_u$.
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §4, below eq. (5), p.4

import Mathlib

namespace OnlineUBSR

/-- **The projection `Γ` onto `[t_l, t_u]`.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §4, p.4: "Γ is a projection operator
defined by Γ(x) = min(max(t_l, x), t_u)."

`proj tl tu x = min (max tl x) tu`.

**Formalization Note.** The formula is taken literally; it is the Euclidean projection onto
`[t_l, t_u]` whenever `t_l ≤ t_u`, which every theorem of the mission assumes (`t_l < t_u`). -/
def proj (tl tu x : ℝ) : ℝ :=
  min (max tl x) tu

end OnlineUBSR



-- Prove2me | Definitions.Def_RollingProbeQN_Convex_colProj
-- name    : RollingProbeQN_Convex_colProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:01.328726+00:00
-- url     : https://prove2.me/theorems/8a12253c-be19-4474-a3f1-f1f5b1f6702d
-- title:
--   Coordinate projection $P_j$ onto the column support $\mathcal S_j$
-- statement:
--   For a pattern $\mathcal S$ and a column $j$, $P_j$ is the coordinate projection onto $\mathcal S_j=\{i:(i,j)\in\mathcal S\}$:
--
--   $$(P_jw)_i=\begin{cases}w_i,& i\in\mathcal S_j,\\ 0,&\text{otherwise.}\end{cases}$$
--
--   Algorithm 1 reads column $j$ of its curvature model off a gradient difference $w$ as $P_jw$.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Definition 2.2, p. 7

import Mathlib

namespace RollingProbeQN.Convex

/-- **The coordinate projection `P_j` onto `S_j`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Definition 2.2, p. 7: "`P_j` denotes the coordinate projection onto `S_j`, that is,
`(P_j w)_i = w_i` for `i ∈ S_j` and `(P_j w)_i = 0` otherwise."

**Formalization Note.** `S_j = {i | (i, j) ∈ S}`. -/
noncomputable def colProj {d : ℕ} (S : Set (Fin d × Fin d)) (j : Fin d)
    (w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  open Classical in
  WithLp.toLp 2 (fun i => if (i, j) ∈ S then w i else 0)

end RollingProbeQN.Convex



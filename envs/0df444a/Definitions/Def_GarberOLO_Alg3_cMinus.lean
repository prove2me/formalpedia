-- Prove2me | Definitions.Def_GarberOLO_Alg3_cMinus
-- name    : GarberOLO_Alg3_cMinus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:49:52.051164+00:00
-- url     : https://prove2.me/theorems/23773643-1235-48c6-8442-58aec9f9f9ea
-- title:
--   Negative part $c^-$ of a vector
-- statement:
--   For $c \in \mathbb R^d$, $c^-$ is the vector equal to $c$ on the coordinates where $c_i < 0$ and zero elsewhere: $(c^-)_i = \min\{c_i, 0\}$.
--
--   Thus $c = c^+ + c^-$ and $c^- \le 0$ coordinate-wise.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 1, p. 6

import Mathlib

namespace GarberOLO.Alg3

/-- **The negative part c⁻ of a vector** (Lemma 1).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 1, p. 6: "c⁻ equals c on all negative coordinates and zero everywhere else".

`cMinus c` has coordinates `min (c i) 0` (so `c = cPlus c + cMinus c` and `cMinus c ≤ 0`). -/
noncomputable def cMinus {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => min (c i) 0)

end GarberOLO.Alg3



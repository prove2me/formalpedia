-- Prove2me | Definitions.Def_GarberOLO_Alg3_cPlus
-- name    : GarberOLO_Alg3_cPlus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:49:33.686553+00:00
-- url     : https://prove2.me/theorems/635423d7-873d-4468-94d6-3e26c4b537f9
-- title:
--   Nonnegative part $c^+$ of a vector
-- statement:
--   For $c \in \mathbb R^d$, $c^+$ is the vector equal to $c$ on the coordinates where $c_i \ge 0$ and zero elsewhere: $(c^+)_i = \max\{c_i, 0\}$.
--
--   Together with $c^-$ it splits $c = c^+ + c^-$, which the extended oracle uses to query $\mathcal O_K$ only at vectors of $\mathbb R^d_+$.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 1, p. 6

import Mathlib

namespace GarberOLO.Alg3

/-- **The nonnegative part c⁺ of a vector** (Lemma 1).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 1, p. 6: "Given c ∈ ℝᵈ write c = c⁺ + c⁻ where c⁺ equals to c on all non-negative
coordinates of c and zero everywhere else".

`cPlus c` has coordinates `max (c i) 0`. -/
noncomputable def cPlus {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => max (c i) 0)

end GarberOLO.Alg3



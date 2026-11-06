-- Prove2me | Definitions.Def_GeomDRSub_gHat
-- name    : GeomDRSub_gHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:10.032355+00:00
-- url     : https://prove2.me/theorems/0447e5b1-9cca-4aa6-97e4-5979d1dca57e
-- title:
--   Field estimate $\hat g=d\,[V]_I\,e_I$
-- statement:
--   For a coordinate $i$ and a vector $v\in\mathbb R^d$,
--   $$
--   \hat g=d\,v_i\,e_i,
--   $$
--   the vector with $i$-th coordinate $d\,v_i$ and all other coordinates $0$. With $i=I$ and $v=V(Y)$ the gradient response at the query point, it is the field estimate of (49).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 5.1, p.17, Eq. (49)

import Mathlib

namespace GeomDRSub

/-- **The field estimate `ĝ = d [V(Y)]_I e_I`** of Eq. (49). Aggarwal–Lu, arXiv:2610.00545,
Section 5.1, p.17. `gHat i v` is the vector whose `i`-th coordinate is `d · vᵢ` and whose other
coordinates are `0`; with `i = I` and `v = V(Y)` the gradient response, it is `ĝ`. -/
noncomputable def gHat {d : ℕ} (i : Fin d) (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  ((d : ℝ) * v i) • EuclideanSpace.single i (1 : ℝ)

end GeomDRSub



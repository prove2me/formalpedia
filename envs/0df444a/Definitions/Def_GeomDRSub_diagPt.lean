-- Prove2me | Definitions.Def_GeomDRSub_diagPt
-- name    : GeomDRSub_diagPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:06.158198+00:00
-- url     : https://prove2.me/theorems/1f40ba36-e7b2-42d8-84e2-4e4f597166c7
-- title:
--   The diagonal point $s\mathbf 1$
-- statement:
--   For a real number $s$, the **diagonal point** $s\mathbf 1\in\mathbb R^d$ is the vector all of whose coordinates equal $s$. In particular $0\cdot\mathbf 1=\mathbf 0$ and $1\cdot\mathbf 1=\mathbf 1$ are the all-zeros and all-ones vectors, and $\zeta\mathbf 1$ is the diagonal point of level $\zeta$ in condition (4).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.1, p.8, Eq. (4)

import Mathlib

namespace GeomDRSub

/-- **The diagonal point `s·1`.** Aggarwal–Lu, arXiv:2610.00545, Section 3.1, p.8: `1` is the
all-ones vector, and `ζ1` is the diagonal point of level `ζ` in (4). `diagPt d s` is the vector of
`ℝ^d` all of whose coordinates equal `s`; `diagPt d 0 = 0` and `diagPt d 1 = 1`. -/
noncomputable def diagPt (d : ℕ) (s : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ => s)

end GeomDRSub



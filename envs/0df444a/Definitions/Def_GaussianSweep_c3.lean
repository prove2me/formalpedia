-- Prove2me | Definitions.Def_GaussianSweep_c3
-- name    : GaussianSweep_c3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:02.143485+00:00
-- url     : https://prove2.me/theorems/73e14857-d6f8-4e66-baaf-83e33811e2c0
-- title:
--   The constant $c_3 = \frac{3}{4\pi}\arccos\frac56$
-- statement:
--   The constant of the main theorem,
--   $$
--   c_3 = \frac{3}{4\pi}\arccos\frac{5}{6} \approx 0.13982 .
--   $$
--   It is $\kappa(r^*)$ for the edge-correlation level $r^* = 2\sqrt2/3$ of the geometric labels, and it improves the previous constant $1/6$ for the pathwidth of graphs of maximum degree $3$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 1.1(a), p.1 (PDF p.3); Section 8, p.45 (PDF p.47)

import Mathlib

namespace GaussianSweep

/-- The constant `c₃ = (3/(4π)) arccos(5/6) ≈ 0.13982` of Theorem 8.1 (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 1.1(a),
p.1 (PDF p.3); Section 8, p.45 (PDF p.47)). -/
noncomputable def c3 : ℝ := 3 / (4 * Real.pi) * Real.arccos (5 / 6)

end GaussianSweep



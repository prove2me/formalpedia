-- Prove2me | Definitions.Def_GaussianSweep_Supplement_cStar
-- name    : GaussianSweep_Supplement_cStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:34:20.443049+00:00
-- url     : https://prove2.me/theorems/733afbb0-97a1-44f8-abba-56ce876b3336
-- title:
--   The cut-sweep constant $c^* = \frac{3}{2\pi}\arcsin\frac13$
-- statement:
--   The constant of the cut sweep for maximum degree $3$,
--   $$
--   c^* = \frac{3}{2\pi}\arcsin\frac13 = \frac{3}{2\pi}\arccos\frac{2\sqrt2}{3} \approx 0.16226 ,
--   $$
--   which lies below $1/6$. It is defined by the arcsine form.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14)

import Mathlib

namespace GaussianSweep.Supplement

/-- The cut-sweep constant `c* = (3/(2π)) arcsin(1/3) = (3/(2π)) arccos(2√2/3) ≈ 0.16226`
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14)). Defined by the arcsin form. -/
noncomputable def cStar : ℝ := 3 / (2 * Real.pi) * Real.arcsin (1 / 3)

end GaussianSweep.Supplement



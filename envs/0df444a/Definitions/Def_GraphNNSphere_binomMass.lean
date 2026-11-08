-- Prove2me | Definitions.Def_GraphNNSphere_binomMass
-- name    : GraphNNSphere_binomMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:28.252247+00:00
-- url     : https://prove2.me/theorems/74ef4acf-0638-4ecb-910d-3f6bf021030c
-- title:
--   Binomial mass
-- statement:
--   The mass at $m$ of the binomial law $\mathrm{Bin}(N,p)$:
--   $$\binom Nm p^m(1-p)^{N-m}.$$
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.4, p.18

import Mathlib

namespace GraphNNSphere

/-- The probability mass `C(N, m) p^m (1 - p)^{N-m}` of the law `Bin(N, p)` at `m` (Lu, *Sharp
Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript
sha256 93565bc5…), §2.4, p.18). -/
noncomputable def binomMass (N : ℕ) (p : ℝ) (m : ℕ) : ℝ :=
  (N.choose m : ℝ) * p ^ m * (1 - p) ^ (N - m)

end GraphNNSphere



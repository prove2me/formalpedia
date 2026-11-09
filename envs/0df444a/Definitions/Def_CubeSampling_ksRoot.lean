-- Prove2me | Definitions.Def_CubeSampling_ksRoot
-- name    : CubeSampling_ksRoot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:17.378527+00:00
-- url     : https://prove2.me/theorems/a2cbbcbb-f46b-452e-b950-314fca905444
-- title:
--   Defining equation of the Kirshner–Samorodnitsky root $z$
-- statement:
--   For $p \ge 2$ and $0 < q < 1/2$, a number $z$ is a **Kirshner–Samorodnitsky root** if $z \in (0,1)$ and
--   $$
--   q = \frac{z\bigl((1+z)^{p-1} - (1-z)^{p-1}\bigr)}{(1+z)^p + (1-z)^p} .
--   $$
--   The paper states that this solution is unique.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), (6), p.12

import Mathlib

namespace CubeSampling

/-- `z` solves the defining equation of the Kirshner–Samorodnitsky rate (6) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), (6), p.12):
`z ∈ (0, 1)` and `q = z((1 + z)^{p−1} − (1 − z)^{p−1}) / ((1 + z)^p + (1 − z)^p)`. -/
def ksRoot (p q z : ℝ) : Prop :=
  0 < z ∧ z < 1 ∧ q = z * ((1 + z) ^ (p - 1) - (1 - z) ^ (p - 1)) / ((1 + z) ^ p + (1 - z) ^ p)

end CubeSampling



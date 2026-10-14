-- Prove2me | Definitions.Def_LocalDistanceNetwork_Tension
-- name    : LocalDistanceNetwork_Tension
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T20:23:14.482721+00:00
-- url     : https://prove2.me/theorems/872e84ae-20a3-4dda-975d-593a400fa56f
-- title:
--   Tension between two independent measurements, $|x-y|/\sqrt{\sigma_x^2+\sigma_y^2}$
-- statement:
--   The **tension** between two independent measurements $x\pm\sigma_x$ and $y\pm\sigma_y$ of the same quantity, expressed in units of the combined standard deviation:
--   $$
--   T(x,\sigma_x;\,y,\sigma_y)=\frac{|x-y|}{\sqrt{\sigma_x^{2}+\sigma_y^{2}}}.
--   $$
--
--   This is the conventional significance of a difference between two independent Gaussian measurements; it is the quantity behind statements such as "$H_0=73.50\pm0.81$ is $7.1\sigma$ from $67.24\pm0.35$" in the abstract of the paper.
--
--   **Formalization Note** The paper does not write the formula out; this is the standard convention, and it reproduces every "$n\sigma$ from" figure quoted in the abstract and in Sect. 5.2.4 (to the stated rounding). The function is total: if $\sigma_x=\sigma_y=0$ the denominator is $0$ and Lean's division returns $0$; all uses in the mission have positive uncertainties.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Abstract (p. 1), Results items (2) and (6)

import Mathlib

namespace LocalDistanceNetwork

/-- The significance (in units of `σ`) of the difference between two independent Gaussian
measurements `x ± σx` and `y ± σy`: `|x - y| / √(σx² + σy²)`. -/
noncomputable def tensionSigma (x σx y σy : ℝ) : ℝ :=
  |x - y| / Real.sqrt (σx ^ 2 + σy ^ 2)

end LocalDistanceNetwork



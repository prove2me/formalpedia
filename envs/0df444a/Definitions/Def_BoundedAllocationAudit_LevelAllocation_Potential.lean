-- Prove2me | Definitions.Def_BoundedAllocationAudit_LevelAllocation_Potential
-- name    : BoundedAllocationAudit_LevelAllocation_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:53:05.168453+00:00
-- url     : https://prove2.me/theorems/f2cdc744-5cc3-487a-a5f9-7f7f94cc19f6
-- title:
--   §13.1 — correctly normalized real-domain trade-off potential
-- statement:
--   For $d\ge2$, put $Q=1+1/(d-1)$ and
--
--   $$a_1=\frac1{dQ^{d-1}-(d-1)},\qquad a_r=a_1Q^{r-1}\ (r\ge1).$$
--
--   The potential is the piecewise affine interpolation of $f_d(k/d)=\sum_{r=1}^k a_r$. Equivalently, on every real input,
--
--   $$f_d(u)=\sum_{k=0}^{d-1}a_{k+1}\min\{1,\max\{0,du-k\}\}.$$
--
--   It is constant outside $[0,1]$. At $d\le1$ the explicit extension is $f_d(u)=\min\{1,\max\{0,u\}\}$, and the ratio wrapper is $C(0)=C(1)=1$; for $d\ge2$ it imports the published exact ratio formula. The auxiliary value $a_0=a_1/Q$ serializes the lower-level display at level zero and changes no source coefficient.
--
--   This provides the real-domain function required by the source's derivative analysis. In particular $f_2(1/2)=1/3$, $f_3(1/3)=4/19$, $f_3(2/3)=10/19$, and $f_d(1)=1$; the incorrect published geometric sequence is deliberately not imported.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, Foundations and Trends in Theoretical Computer Science 3(2–3), 93–263, 2009, https://doi.org/10.1561/0400000024; §13.1 sequence, interpolation and Fig. 13.2, printed pp. 239–240 / PDF pp. 150–151; Theorem 13.1, printed p. 240 / PDF p. 151

import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_competitiveRatio

namespace BoundedAllocationAudit.LevelAllocation

/-- Exact Theorem 13.1 ratio for d≥2, explicit optimal endpoints for d=0,1. -/
noncomputable def ratio (d : ℕ) : ℝ :=
  if d ≤ 1 then 1 else OnlinePrimalDual.BoundedAllocation.competitiveRatio d

noncomputable def geometricBase (d : ℕ) : ℝ := 1 + 1 / ((d : ℝ) - 1)

/-- PDF 151 / printed 240. The reciprocal covers the entire denominator.
a₀=a₁/Q is a geometric extension only for serializing (13.2) at t=0. -/
noncomputable def coefficient (d r : ℕ) : ℝ :=
  if d ≤ 1 then (if r = 1 then 1 else 0) else
    let a := 1 / ((d : ℝ) * geometricBase d ^ (d - 1) - ((d : ℝ) - 1))
    if r = 0 then a / geometricBase d else a * geometricBase d ^ (r - 1)

/-- Linear interpolation on every real argument using clipped affine ramps.
On [0,1] this has grid values Σ_{r=1}^k a_r. Outside [0,1] it is constant. -/
noncomputable def potential (d : ℕ) (u : ℝ) : ℝ :=
  if d ≤ 1 then min 1 (max 0 u) else
    ∑ k ∈ Finset.range d,
      coefficient d (k + 1) * min 1 (max 0 ((d : ℝ) * u - (k : ℝ)))

end BoundedAllocationAudit.LevelAllocation



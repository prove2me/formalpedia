-- Prove2me | Definitions.Def_VertexSampleCSP_Cr
-- name    : VertexSampleCSP_Cr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:32.863889+00:00
-- url     : https://prove2.me/theorems/f55e18e4-a5e6-4360-b141-eb7131c97062
-- title:
--   The constants $C_r$, $C_{r,q}$ and $C'_{r,q}$
-- statement:
--   The explicit constants of the sampling theorem and its corollaries are
--
--   $$C_r=\frac{8(1+\sqrt2)(2^r-1)}{\sqrt{r\cdot r!}},\qquad C_{r,q}=C_r\sqrt{rq^r},\qquad C'_{r,q}=\frac{C_{r,q}}{\sqrt{r!}}.$$
--
--   Equivalently $C_{r,q}=8(1+\sqrt2)(2^r-1)q^{r/2}/\sqrt{r!}$.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), §C.3, p.17 (PDF p.19); §D.1, p.18 (PDF p.20)

import Mathlib

namespace VertexSampleCSP

/-- **The constant `C_r`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*,
STOC 2027 submission (manuscript sha256 1e0edd23…), §C.3, p.17 (PDF p.19): "Let
Cr = 8(1 + √2)(2^r − 1)/√(r · r!); for example, C2 < 29 and C3 < 32." -/
noncomputable def Cr (r : ℕ) : ℝ :=
  8 * (1 + Real.sqrt 2) * (2 ^ r - 1) / Real.sqrt (r * (r.factorial : ℝ))

/-- **The constant `C_{r,q}`.** Chang, STOC 2027 submission (manuscript sha256 1e0edd23…), §D.1,
p.18 (PDF p.20): "Let C_{r,q} = C_r √(r q^r) = 8(1 + √2)(2^r − 1) q^{r/2}/√(r!)". -/
noncomputable def Crq (r q : ℕ) : ℝ :=
  Cr r * Real.sqrt (r * (q : ℝ) ^ r)

/-- **The constant `C′_{r,q}`.** Chang, STOC 2027 submission (manuscript sha256 1e0edd23…), §D.1,
p.18 (PDF p.20): "C′_{r,q} = C_{r,q}/√(r!)". -/
noncomputable def Crq' (r q : ℕ) : ℝ :=
  Crq r q / Real.sqrt (r.factorial : ℝ)

end VertexSampleCSP



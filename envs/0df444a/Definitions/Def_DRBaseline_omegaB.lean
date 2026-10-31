-- Prove2me | Definitions.Def_DRBaseline_omegaB
-- name    : DRBaseline_omegaB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:49.561233+00:00
-- url     : https://prove2.me/theorems/5bc30cdd-ab5c-44dc-9139-1834320377de
-- title:
--   Threshold $\omega_B(b,r)=(r+2bc_s)/(2c_s)$
-- statement:
--   The demand level at which shifting the interior amount $r/c_s$ and shifting nothing give the customer the same benefit:
--
--   $$\omega_B(b,r)=\frac{r+2bc_s}{2c_s},$$
--
--   since $C_c(r/c_s)-C_c(0)=r\bigl(\frac{r+2bc_s}{2c_s}-\omega\bigr)$.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1

import Mathlib

namespace DRBaseline

/-- **Threshold `ω_B(b, r) = (r + 2bc_s)/(2c_s)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1:
"C_c(r/c_s) − C_c(0) = r((r+2bc_s)/(2c_s) − ω) ≥ 0 if and only if ω ≤ ω_B(b,r) .= (r+2bc_s)/(2c_s)". -/
noncomputable def omegaB (cs b r : ℝ) : ℝ :=
  (r + 2 * b * cs) / (2 * cs)

end DRBaseline



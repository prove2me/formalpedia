-- Prove2me | Definitions.Def_DRBaseline_omegaA
-- name    : DRBaseline_omegaA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:49.444233+00:00
-- url     : https://prove2.me/theorems/220a6f7c-0a0b-4d99-b37d-780c14f2736a
-- title:
--   Threshold $\omega_A(b,r)=\sqrt{2br/c_s}$
-- statement:
--   The demand level at which shifting all demand and shifting nothing give the customer the same benefit:
--
--   $$\omega_A(b,r)=\sqrt{\frac{2br}{c_s}},$$
--
--   since $C_c(\omega)-C_c(0)=br-\frac{c_s}{2}\omega^2$ when the customer is below the baseline after shifting everything.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1

import Mathlib

namespace DRBaseline

/-- **Threshold `ω_A(b, r) = √(2br/c_s)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1:
"C_c(ω) − C_c(0) = br − ω²c_s/2 ≥ 0 if and only if ω ≤ ω_A(b,r) .= √(2br/c_s)".

**Formalization Note** `Real.sqrt`; its argument is nonnegative whenever `b, r ≥ 0`, `c_s > 0`. -/
noncomputable def omegaA (cs b r : ℝ) : ℝ :=
  Real.sqrt (2 * b * r / cs)

end DRBaseline



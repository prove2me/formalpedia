-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_welfare
-- name    : HRRPIncentives_SchemeI_welfare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:20.521359+00:00
-- url     : https://prove2.me/theorems/80d33d86-23e3-475e-8f6b-8f509c6a3271
-- title:
--   Social welfare $S(r,c)=V(\lambda)-c(1+r)\lambda-R(r,c)$
-- statement:
--   The regulator's objective, total social welfare (display (2)):
--
--   $$S(r,c)=V(\lambda)-c(1+r)\lambda-R(r,c).$$
--
--   Here $V(\lambda)$ is the total utility patients derive from treatment, a constant; $c(1+r)\lambda$ is the treatment cost of the $(1+r)\lambda$ visits (index admissions plus readmissions) at marginal cost $c$; and $R(r,c)$ is the investment cost. A maximizer $(r^*,c^*)$ of $S$ over the action box is the first best.
--
--   **Formalization Note** $V(\lambda)$ is a real parameter $V$; it does not affect the maximizer.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, display (2), p. 10

import Mathlib

namespace HRRPIncentives.SchemeI

/-- Total social welfare (2): `S(r, c) = V(λ) − c(1 + r)λ − R(r, c)`, the regulator's
objective.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, display (2), p. 10.

**Formalization Note.** `V` is the constant `V(λ)` (total patient utility), a real parameter;
`x = (r, c)`. -/
def welfare (lam V : ℝ) (R : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun x => V - x.2 * (1 + x.1) * lam - R x

end HRRPIncentives.SchemeI



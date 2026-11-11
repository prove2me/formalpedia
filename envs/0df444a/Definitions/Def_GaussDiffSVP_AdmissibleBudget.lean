-- Prove2me | Definitions.Def_GaussDiffSVP_AdmissibleBudget
-- name    : GaussDiffSVP_AdmissibleBudget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:02:24.181625+00:00
-- url     : https://prove2.me/theorems/f5dc9d16-00dd-4315-995a-7241d780fd6a
-- title:
--   Either schedule of Appendices C.1.2 and C.3.2
-- statement:
--   A schedule is **admissible** if it is the default schedule (163) or the single-sample schedule (166) for some rational $0 < \delta \le 1$. This is the paper's "either schedule in Appendices C.1.2 and C.3.2" (Theorem 5.2), with the rational $0<\delta\le\min\{1,\xi\}$ of App. C.3.2 and $\xi>0$ arbitrary.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 5.2, p.30; (163), p.80; (166), p.86

import Mathlib
import Definitions.Def_GaussDiffSVP_svpBudget
import Definitions.Def_GaussDiffSVP_singleBudget

namespace GaussDiffSVP

/-- "Either schedule in Appendices C.1.2 and C.3.2" (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 5.2, p.30): the schedule is the
default SVP schedule (163) (p.80) or the single-sample schedule (166) (p.86) for some rational
`0 < δ ≤ 1` (the page's "rational 0 < δ ≤ min{1, ξ}" with `ξ > 0` arbitrary). -/
def AdmissibleBudget (β : Budget) : Prop :=
  β = svpBudget ∨ ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧ β = singleBudget δ

end GaussDiffSVP



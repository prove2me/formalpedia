-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqDiskEulerTrace
-- name    : GrothendieckLB_Supplement_cqDiskEulerTrace
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T20:16:16.184883+00:00
-- url     : https://prove2.me/theorems/563a5a54-28e2-4e79-bd50-60725aef56f7
-- title:
--   Diagonal Hermite trace of the third cubic–quintic Euler kernel on the complex disk
-- statement:
--   For a complex parameter z the trace sums the equal-degree Gaussian Hermite coefficients of the third Euler kernel, weighted by the powers of minus z. Its unit-circle restriction agrees definitionally with the cubic–quintic boundary trace.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.2, equations (47)–(52).

import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel

open MeasureTheory ProbabilityTheory
namespace GrothendieckLB.Supplement.CQBoundary

/-- Diagonal Hermite trace of the third Euler kernel at a complex correlation parameter. -/
noncomputable def diskTrace (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-z)^n * (∫ x : ℝ, ∫ y : ℝ,
    phiThree z x y * Complex.ofReal (QuadSDE.hermiteN n x * QuadSDE.hermiteN n y)
    ∂gaussianReal 0 1 ∂gaussianReal 0 1)

end GrothendieckLB.Supplement.CQBoundary



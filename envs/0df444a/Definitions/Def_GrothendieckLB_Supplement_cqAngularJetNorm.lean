-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqAngularJetNorm
-- name    : GrothendieckLB_Supplement_cqAngularJetNorm
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T21:40:26.884816+00:00
-- url     : https://prove2.me/theorems/f603f65d-a1ab-4554-b2ef-9947df954b5e
-- title:
--   Gaussian norms of the angular derivatives in the cubic–quintic energy
-- statement:
--   For an angle θ, the two functions are the third-Euler boundary kernel and its mixed spatial derivative. The quantity angularJetNorm is the Gaussian L² norm of their j-th angular derivative. The sum jetMajorant is the binomial convolution of two arrays of upper bounds appearing when a squared norm is differentiated eight times.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.3–C.4. The published numerical certificate gkcore/crossmoment.py, CrossS.panel_S8.

import Definitions.Def_GrothendieckLB_Supplement_cqGaussFourPanel

namespace GrothendieckLB.Supplement.CQBoundary
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Gaussian L² norm of the angular derivative of the trace kernel or its mixed spatial derivative. -/
def angularJetNorm (spatial : Bool) (j : ℕ) (θ : ℝ) : ℝ :=
  Real.sqrt (∫ t : ℝ×ℝ, ‖iteratedDeriv j (fun a : ℝ =>
    if spatial then mixed (phiThree (unitPoint a)) t.1 t.2
    else phiThree (unitPoint a) t.1 t.2) θ‖^2
    ∂(gaussianReal 0 1).prod (gaussianReal 0 1))

/-- Binomial sum of products of angular-derivative bounds for the two squared norms in the energy. -/
def jetMajorant (V : Bool → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 9, ((8:ℕ).choose j:ℝ) *
    (V false j*V false (8-j)+4*(V true j*V true (8-j)))

end
end GrothendieckLB.Supplement.CQBoundary



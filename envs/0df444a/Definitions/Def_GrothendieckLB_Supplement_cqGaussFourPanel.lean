-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqGaussFourPanel
-- name    : GrothendieckLB_Supplement_cqGaussFourPanel
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T20:49:01.610043+00:00
-- url     : https://prove2.me/theorems/7b8113e5-f161-44b7-a064-33d2450e2555
-- title:
--   Four-point Gauss–Legendre mean and the rescaled cubic–quintic energy panels
-- statement:
--   The two normalized pairs of Gauss–Legendre nodes and weights specify the four-node rule on [0,1]. The panel function evaluates the combined cubic–quintic Gaussian energy along the affine parametrization of one of the 1024 angular subintervals.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix C.3–C.4; upper-bounds/theorem-cubic-quintic/certify_d3h.py.

import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel

namespace GrothendieckLB.Supplement.CQBoundary
noncomputable section
namespace GaussFour

def outer := Real.sqrt ((15+2*Real.sqrt 30)/35)
def inner := Real.sqrt ((15-2*Real.sqrt 30)/35)

def mean (f : ℝ → ℝ) : ℝ :=
  ((18-Real.sqrt 30)/72)*(f ((1-outer)/2)+f ((1+outer)/2))+
  ((18+Real.sqrt 30)/72)*(f ((1-inner)/2)+f ((1+inner)/2))

def panel (i : ℕ) (x : ℝ) : ℝ :=
  energy ((i:ℝ)*(Real.pi/1024)+(Real.pi/1024)*x)

end GaussFour
end
end GrothendieckLB.Supplement.CQBoundary



-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
-- name    : OAI_Analysis_TriangularHilbert_PlaneDom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:30:27.780444+00:00
-- url     : https://prove2.me/theorems/8d193a79-1c81-4919-b580-d2e91d314cc8
-- title:
--   Root coefficients for dominating heat weights
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$.
--
--   For real parameters $h,a,b,u$ the root coefficient is
--   $$
--   \mathrm{rootCoefficient}(h,a,b,u)=\sqrt{\frac{h}{\sqrt{2\pi a}}\,e^{u^2/(2b)}} .
--   $$
--   It arises when the square root of a heat weight $h\,\phi_\sigma(u-p)$ is bounded, uniformly for $\sigma$ in a compact range, by a constant depending on $u$ times a Gaussian in the centre $p$. Such domination makes heat energies integrable over the plane of centres.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneDom.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneDom.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def rootCoefficient (h a b u : ℝ) : ℝ :=
  Real.sqrt (h * (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b)))

end
end TriangularHilbert.Heat
end

end OAI



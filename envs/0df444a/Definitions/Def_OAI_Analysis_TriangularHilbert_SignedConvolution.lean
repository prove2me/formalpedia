-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
-- name    : OAI_Analysis_TriangularHilbert_SignedConvolution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:51:49.327705+00:00
-- url     : https://prove2.me/theorems/220b23d3-1b32-477d-87cf-ea8d32e473db
-- title:
--   The signed cubic Gaussian kernel
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$.
--
--   For a scale $s>0$ and $t\in\mathbb R$, the signed kernel is
--   $$
--   \mathrm{signedKernel}(s,t)=\frac{t^3/27-ts/3}{s\sqrt s}\,\phi_{3s}(t) .
--   $$
--   It is odd in $t$ and arises as the threefold convolution of odd Gaussian windows at the three vertices of the triangle. Integrating $\mathrm{signedKernel}(s,t)/s$ over a range of scales produces a smooth approximation of the truncated Hilbert kernel $1/t$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SignedConvolution.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SignedConvolution.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def signedKernel (s t : ℝ) : ℝ :=
  (t^3/27-t*s/3)/(s*Real.sqrt s)*density (3*s) t

end
end TriangularHilbert.Heat
end

end OAI



-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
-- name    : OAI_Analysis_TriangularHilbert_RankJump
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:54:31.090197+00:00
-- url     : https://prove2.me/theorems/04e13e75-35f5-4e9c-b7fe-977948536a68
-- title:
--   Line segments between matrices
-- statement:
--   For complex square matrices $A,B$ and a parameter $t\in\mathbb R$, the segment matrix is
--   $$
--   \mathrm{segmentMatrix}(A,B,t)=(1-t)A+tB .
--   $$
--   It interpolates linearly from $A$ (at $t=0$) to $B$ (at $t=1$). Energies such as $E(P)=\operatorname{tr}P^{3/2}$ are compared along such segments, for instance when a single edge of a triangle array is switched on or off and the jump of the energy is bounded through derivatives along the segment.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/RankJump.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/RankJump.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def segmentMatrix (A B : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  (1-t) • A + t • B

end
end TriangularHilbert.MatrixEnergy
end

end OAI



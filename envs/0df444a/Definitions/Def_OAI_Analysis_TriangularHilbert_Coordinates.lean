-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_Coordinates
-- name    : OAI_Analysis_TriangularHilbert_Coordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T01:31:46.404028+00:00
-- url     : https://prove2.me/theorems/7e40076c-e1e3-4e28-8a80-9ce2ad59d9f9
-- title:
--   Cyclic coordinates for the triangular Hilbert transform
-- statement:
--   The triangular Hilbert transform pairs $F(x+t,y)$ and $G(x,y+t)$. In cyclic coordinates both functions are read along the same line as in $\int B(z_2,c)C(c,z_1)K(z_1+z_2+c)\,dc$.
--
--   1. **Charts.** $\mathrm{chartB}(z)=(z_1+z_2,\,-z_1)$ and $\mathrm{chartC}(z)=(-z_2,\,z_1+z_2)$, linear maps of the plane with determinant $1$.
--   2. **Transported functions.** $\mathrm{cyclicB}(F)=F\circ\mathrm{chartB}$ and $\mathrm{cyclicC}(G)=G\circ\mathrm{chartC}$.
--
--   Since both charts preserve Lebesgue measure, $\|\mathrm{cyclicB}(F)\|_{L^3}=\|F\|_{L^3}$ and $\|\mathrm{cyclicC}(G)\|_{L^3}=\|G\|_{L^3}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Coordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Coordinates.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicSlice
import Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteDual
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscreteMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicMaxMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicHomogeneity
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicNorm

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat
open scoped ENNReal
noncomputable section

def chartB (z : Plane) : Plane := (z.1+z.2,-z.1)
def chartC (z : Plane) : Plane := (-z.2,z.1+z.2)
def cyclicB (F : Plane → ℂ) : Plane → ℂ := F ∘ chartB
def cyclicC (G : Plane → ℂ) : Plane → ℂ := G ∘ chartC

end
end TriangularHilbert
end

end OAI



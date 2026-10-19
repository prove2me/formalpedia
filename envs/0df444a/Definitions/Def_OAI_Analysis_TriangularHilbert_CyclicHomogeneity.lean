-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicHomogeneity
-- name    : OAI_Analysis_TriangularHilbert_CyclicHomogeneity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T01:26:11.003851+00:00
-- url     : https://prove2.me/theorems/62db580c-69f8-43af-8504-695be3781893
-- title:
--   The $L^{3/2}$ norm of the cyclic maximal function
-- statement:
--   For functions $B,C$ on the plane, let $\mathrm{cyclicMax}(B,C)(z)$ be the supremum over rational truncations $0<q_1<q_2$ of $\bigl|\int B(z_2,c)C(c,z_1)\frac{\mathbf 1_{q_1<|t|\le q_2}}t\,dc\bigr|$ with $t=z_1+z_2+c$.
--
--   The cyclic norm is
--   $$
--   \mathrm{cyclicNorm}(B,C)=\Bigl(\int_{\mathbb R^2}\mathrm{cyclicMax}(B,C)(z)^{3/2}\,dz\Bigr)^{2/3}\in[0,\infty],
--   $$
--   computed as a lower Lebesgue integral. It vanishes when $B=0$ or $C=0$, and it is the quantity bounded in the main estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/CyclicHomogeneity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/CyclicHomogeneity.lean by skeleton subtraction
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

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat Filter
open scoped ENNReal
noncomputable section

def cyclicNorm (B C : Plane → ℂ) : ℝ≥0∞ :=
  (∫⁻ z : Plane, cyclicMax B C z ^ ((3:ℝ)/2)) ^ ((2:ℝ)/3)

@[simp] lemma cyclicNorm_zero_left (C : Plane → ℂ) : cyclicNorm 0 C = 0 := by
  simp [cyclicNorm,cyclicMax,cyclicKernelOutput]
@[simp] lemma cyclicNorm_zero_right (B : Plane → ℂ) : cyclicNorm B 0 = 0 := by
  simp [cyclicNorm,cyclicMax,cyclicKernelOutput]

end
end TriangularHilbert
end

end OAI



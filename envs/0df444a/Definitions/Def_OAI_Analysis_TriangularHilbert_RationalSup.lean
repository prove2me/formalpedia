-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup
-- name    : OAI_Analysis_TriangularHilbert_RationalSup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T01:09:26.598285+00:00
-- url     : https://prove2.me/theorems/e573ff2a-e9de-4ba2-908c-3627b268d1d3
-- title:
--   Rational truncation endpoints and the cyclic maximal function
-- statement:
--   Truncation endpoints are pairs $0<r<R$. The rational endpoints are the pairs $(q_1,q_2)\in\mathbb Q^2$ with $0<q_1<q_2$, viewed as endpoints.
--
--   1. **Cyclic maximal function.** For $B,C$ on the plane,
--   $$
--   \mathrm{cyclicMax}(B,C)(z)=\sup_{0<q_1<q_2,\ q_i\in\mathbb Q}\Bigl|\int B(z_2,c)\,C(c,z_1)\,\frac{\mathbf 1_{q_1<|z_1+z_2+c|\le q_2}}{z_1+z_2+c}\,dc\Bigr| ,
--   $$
--   valued in $[0,\infty]$.
--   2. **Enumeration.** The rational endpoints are countable, and $\mathrm{RatEndpoints.sequence}$ enumerates them, with a default value for unused codes. This turns the supremum into a countable increasing limit of finite maxima.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/RationalSup.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/RationalSup.lean by skeleton subtraction
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

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal
noncomputable section

abbrev RatEndpoints := {p : ℚ×ℚ // 0 < p.1 ∧ p.1 < p.2}
instance : Inhabited RatEndpoints := ⟨⟨(1,2),by norm_num⟩⟩

def RatEndpoints.toEndpoints (q : RatEndpoints) : Endpoints where
  lower := q.1.1
  upper := q.1.2
  lower_pos := by exact_mod_cast q.2.1
  lower_lt_upper := by exact_mod_cast q.2.2

def cyclicMax (B C : Plane → ℂ) (z : Plane) : ℝ≥0∞ :=
  ⨆ q : RatEndpoints, ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel (q.1.1:ℝ) (q.1.2:ℝ)) z‖

def RatEndpoints.sequence (n : ℕ) : RatEndpoints := (Encodable.decode (α := RatEndpoints) n).getD default
end
end TriangularHilbert
end

end OAI



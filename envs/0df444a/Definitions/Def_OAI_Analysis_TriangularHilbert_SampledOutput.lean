-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
-- name    : OAI_Analysis_TriangularHilbert_SampledOutput
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T01:02:48.272337+00:00
-- url     : https://prove2.me/theorems/4ffce781-c88a-40a5-a319-dfa35a706986
-- title:
--   Continuous and sampled cyclic kernel outputs
-- statement:
--   For functions $B,C$ on the plane and a real kernel $K$:
--
--   1. **Cyclic kernel output.**
--   $$
--   \mathrm{cyclicKernelOutput}(B,C,K)(z)=\int_{\mathbb R}B(z_2,c)\,C(c,z_1)\,K(z_1+z_2+c)\,dc .
--   $$
--   With $K$ the truncated Hilbert kernel this is the triangular Hilbert transform written in cyclic coordinates.
--   2. **Sampled version.** The sampled integrand replaces every coordinate $x\in\{z_1,z_2,c\}$ by its grid point $h\lfloor x/h\rfloor$, and $\mathrm{sampledKernelOutput}$ integrates it over $c$. This is the continuum form of the discrete kernel output on the grid of mesh $h$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SampledOutput.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SampledOutput.lean by skeleton subtraction
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

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

def cyclicKernelOutput (B C : ℝ×ℝ → ℂ) (K : ℝ → ℝ) (z : ℝ×ℝ) : ℂ :=
  ∫ c : ℝ, B (z.2,c)*C (c,z.1)*(K (z.1+z.2+c):ℂ)

def sampledIntegrand (B C : ℝ×ℝ → ℂ) (h : ℝ) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ) : ℂ :=
  B (gridPoint h z.2,gridPoint h c)*C (gridPoint h c,gridPoint h z.1)*
    (K (gridPoint h z.1+gridPoint h z.2+gridPoint h c):ℂ)

def sampledKernelOutput (B C : ℝ×ℝ → ℂ) (h : ℝ) (K : ℝ → ℝ) (z : ℝ×ℝ) : ℂ :=
  ∫ c : ℝ, sampledIntegrand B C h K z c

end
end TriangularHilbert.Heat
end

end OAI



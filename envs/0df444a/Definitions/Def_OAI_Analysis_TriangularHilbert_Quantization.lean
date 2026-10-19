-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
-- name    : OAI_Analysis_TriangularHilbert_Quantization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:54:27.504917+00:00
-- url     : https://prove2.me/theorems/161fc1fa-4c55-4fd0-9f4d-d14a54e7684a
-- title:
--   Rounding to the grid and sampling on a box
-- statement:
--   For a mesh $h>0$ and a box radius $M$:
--
--   1. **Rounding in the plane.** $\mathrm{gridSquare}(h,z)=(h\lfloor z_1/h\rfloor,\ h\lfloor z_2/h\rfloor)$.
--   2. **Sample indices.** $\mathrm{sampleIndices}(h,M)=\{i\in\mathbb Z:\lceil-M/h\rceil\le i\le\lfloor M/h\rfloor\}$, the grid indices whose points lie in $[-M,M]$.
--   3. **Sampled matrix.** For $f$ on the plane,
--   $$
--   \mathrm{sampledMatrix}(f,h,M)(i,j)=f(hi,hj),
--   $$
--   the matrix of values of $f$ on the grid inside the box. Continuous functions supported in the box are recovered by their sampled matrices as $h\to0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Quantization.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Quantization.lean by skeleton subtraction
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

namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

def gridSquare (h : ℝ) (z : ℝ×ℝ) : ℝ×ℝ := (gridPoint h z.1,gridPoint h z.2)

def sampleIndices (h M : ℝ) : Finset ℤ := Finset.Icc ⌈-M/h⌉ ⌊M/h⌋

def sampledMatrix {E : Type uE} (f : ℝ×ℝ → E) (h M : ℝ) :
    sampleIndices h M → sampleIndices h M → E := fun i j => f (h*(i:ℤ),h*(j:ℤ))

end
end TriangularHilbert
end

end OAI



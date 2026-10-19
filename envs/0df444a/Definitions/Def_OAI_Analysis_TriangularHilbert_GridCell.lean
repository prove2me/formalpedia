-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
-- name    : OAI_Analysis_TriangularHilbert_GridCell
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:53:07.149848+00:00
-- url     : https://prove2.me/theorems/4664fa07-bfde-4ed1-8a37-5563219fe917
-- title:
--   Grid cells, grid points and piecewise constant lifts
-- statement:
--   For a mesh $h>0$:
--
--   1. **Cells.** $\mathrm{gridCell}(h,i)=[hi,h(i+1))$ for $i\in\mathbb Z$, and $\mathrm{gridRect}(h,i,j)=\mathrm{gridCell}(h,i)\times\mathrm{gridCell}(h,j)$.
--   2. **Rounding.** $\mathrm{gridIndex}(h,x)=\lfloor x/h\rfloor$ and $\mathrm{gridPoint}(h,x)=h\lfloor x/h\rfloor$, the left endpoint of the cell containing $x$.
--   3. **Lift.** For a finite set $D\subset\mathbb Z$ and $f:D\times D\to E$,
--   $$
--   \mathrm{gridLift}(D,h,f)(z)=\sum_{i,j\in D}\mathbf 1_{\mathrm{gridRect}(h,i,j)}(z)\,f(i,j),
--   $$
--   the piecewise constant function on the plane equal to $f(i,j)$ on the cell $(i,j)$ and $0$ outside the grid.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GridCell.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GridCell.lean by skeleton subtraction
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

namespace OAI

universe uE uF

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def gridCell (h : ℝ) (i : ℤ) : Set ℝ := Set.Ico (h*i) (h*(i+1))
def gridIndex (h x : ℝ) : ℤ := ⌊x/h⌋
def gridPoint (h x : ℝ) : ℝ := h*gridIndex h x

def gridRect (h : ℝ) (i j : ℤ) : Set (ℝ×ℝ) := gridCell h i ×ˢ gridCell h j

def gridLift (D : Finset ℤ) (h : ℝ) {E : Type uE} [AddCommMonoid E] (f : D → D → E) (z : ℝ×ℝ) : E :=
  ∑ i : D, ∑ j : D, (gridRect h i j).indicator (fun _ => f i j) z

end
end TriangularHilbert
end

end OAI



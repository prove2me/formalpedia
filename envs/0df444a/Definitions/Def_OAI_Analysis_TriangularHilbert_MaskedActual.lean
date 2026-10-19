-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
-- name    : OAI_Analysis_TriangularHilbert_MaskedActual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:31:37.278989+00:00
-- url     : https://prove2.me/theorems/dcead2eb-3975-48c6-b11b-821b99fb7716
-- title:
--   Masked arrays and their Hessian dissipation cost
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Each entry $(i,j)$ of edge $0$ has a scale window $[a_{ij},b_{ij})$.
--
--   1. **Masked array.** $\mathrm{maskedArray}(A,a,b,s)$ replaces edge $0$ by its entries that are active at time $s$, i.e. $A_0(i,j)$ if $a_{ij}\le s<b_{ij}$ and $0$ otherwise.
--   2. **Masked cost.** For a distinguished vertex $r$,
--   $$
--   \mathrm{maskedCost}(s)=\sum_v\mathrm{planeIntegral}\Bigl(p\mapsto\mathrm{heatCost}\bigl(\mathrm{maskedArray}(s),p,\ \sigma_z=\mathrm{strictRate}(r,z)\,s\bigr)(v,v),\ 0\Bigr),
--   $$
--   the Hessian dissipation of the masked array integrated over centres with $p_0+p_1+p_2=0$, using variance $s$ at vertex $r$ and $\frac{11}{10}s$ elsewhere.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MaskedActual.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MaskedActual.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def maskedArray (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ) (s : ℝ) : Three → Matrix ι ι ℂ :=
  replaceZero A (fun i j => windowMask (a i j) (b i j) s (A 0 i j))

def maskedCost (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (h : ℝ) (u : ι → ℝ) (r : Three) (s : ℝ) : ℝ :=
  ∑ v, planeIntegral (fun p => heatCost (maskedArray A a b s) h u p (fun z => strictRate r z*s) v v) 0

end
end TriangularHilbert.Heat
end

end OAI



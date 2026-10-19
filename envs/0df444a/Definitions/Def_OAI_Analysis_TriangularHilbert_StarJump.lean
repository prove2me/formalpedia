-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
-- name    : OAI_Analysis_TriangularHilbert_StarJump
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:58:07.395313+00:00
-- url     : https://prove2.me/theorems/dc55c698-8046-4839-8d64-227a7dce0a54
-- title:
--   Slicing weights controlling energy jumps of a single entry
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Let $g_v(m)\ge0$ be weights on the grid at each vertex.
--
--   For an array $A$ and indices $i,j$, the jump slicing weight is
--   $$
--   \mathrm{jumpSlicing}(i,j)=2\sum_m|A_0(i,m)|^2g_1(m)+2\sum_m|A_0(m,j)|^2g_0(m)+\sum_m|A_2(m,i)|^2g_2(m)+\sum_m|A_1(j,m)|^2g_2(m).
--   $$
--   It collects the weighted squared norms of the rows and columns of the array that meet the entry $(i,j)$ of edge $0$. It bounds how much the star energies can change when that single entry is switched.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/StarJump.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/StarJump.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def jumpSlicing (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (i j : ι) : ℝ :=
  2*(∑ m, ‖A 0 i m‖^2*g 1 m)+2*(∑ m, ‖A 0 m j‖^2*g 0 m)+
    (∑ m, ‖A 2 m i‖^2*g 2 m)+(∑ m, ‖A 1 j m‖^2*g 2 m)

end
end TriangularHilbert.MatrixEnergy
end

end OAI



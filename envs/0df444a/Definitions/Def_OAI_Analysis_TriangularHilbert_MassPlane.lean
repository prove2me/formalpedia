-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
-- name    : OAI_Analysis_TriangularHilbert_MassPlane
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:46:42.498529+00:00
-- url     : https://prove2.me/theorems/6b8301da-e122-44f1-bf44-6e6a97ade418
-- title:
--   Heat-weighted cubic edge mass
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For an edge $v$ of the triangle (from vertex $v$ to vertex $v+1$), heat weights $g_v(i)=h\,\phi_{\sigma_v}(u_i-p_v)$ attach a Gaussian mass to each grid point.
--
--   The heat-weighted cubic edge mass is
--   $$
--   \mathrm{edgeCubic}(v)=\sum_{i,j}\bigl|A_v(i,j)\bigr|^3\,g_v(i)\,g_{v+1}(j).
--   $$
--   Integrated over the plane of centres, it recovers the unweighted cubic mass $\sum_{i,j}h^2|A_v(i,j)|^3$ of the edge. It is the quantity that controls the matrix energies of the stars.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MassPlane.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MassPlane.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

variable {ι : Type uι} [Fintype ι]

def edgeCubic (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v : Three) : ℝ :=
  ∑ i, ∑ j, ‖A v i j‖^3 * (heatWeights h u p σ v i*heatWeights h u p σ (v+1) j)

end
end TriangularHilbert.Heat
end

end OAI



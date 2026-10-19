-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
-- name    : OAI_Analysis_TriangularHilbert_TotalJump
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:06:46.418932+00:00
-- url     : https://prove2.me/theorems/aa58bbd8-fe42-4656-81d7-0332cc9b436f
-- title:
--   Expected slicing weight under the heat flow
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$.
--
--   For variances $\sigma_0,\sigma_1,\sigma_2$, the jump expectation of the entry $(i,j)$ of edge $0$ is
--   $$
--   \begin{aligned}
--   &2\sum_m|A_0(i,m)|^2h\phi_{2\sigma_1}(u_j-u_m)+2\sum_m|A_0(m,j)|^2h\phi_{2\sigma_0}(u_i-u_m)\\
--   &\quad+\sum_m\bigl(|A_2(m,i)|^2+|A_1(j,m)|^2\bigr)h\,\phi_{\sigma_0+\sigma_1+\sigma_2}(u_i+u_j+u_m).
--   \end{aligned}
--   $$
--   It arises from the slicing weight when the heat weights are averaged over the centres, with Gaussian convolutions combining the variances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/TotalJump.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/TotalJump.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def jumpExpectation (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (σ : Three → ℝ) (i j : ι) : ℝ :=
  2*(∑ m, ‖A 0 i m‖^2*(h*density (2*σ 1) (u j-u m)))+
  2*(∑ m, ‖A 0 m j‖^2*(h*density (2*σ 0) (u i-u m)))+
  (∑ m, ‖A 2 m i‖^2*(h*density (σ 0+σ 1+σ 2) (u i+u j+u m)))+
  (∑ m, ‖A 1 j m‖^2*(h*density (σ 0+σ 1+σ 2) (u i+u j+u m)))

end
end TriangularHilbert.Heat
end

end OAI



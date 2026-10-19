-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
-- name    : OAI_Analysis_TriangularHilbert_MeshJump
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:17:34.569753+00:00
-- url     : https://prove2.me/theorems/6f9bb262-6601-4482-8434-0463c49b46a8
-- title:
--   Maximal slicing weight of a grid entry
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The grid is a finite set $D\subset\mathbb Z$, and $\mathrm{lineMax}$ is the discrete centred maximal function on $D$.
--
--   For a triangle array $A$ on $D$ and $i,j\in D$, the maximal jump weight is
--   $$
--   \begin{aligned}
--   \mathrm{jumpMax}(i,j)={}&2\,\mathrm{lineMax}\bigl(|A_0(i,\cdot)|^2\bigr)(j)+2\,\mathrm{lineMax}\bigl(|A_0(\cdot,j)|^2\bigr)(i)\\
--   &+\mathrm{lineMax}\bigl(|A_2(\cdot,i)|^2\bigr)(-i-j)+\mathrm{lineMax}\bigl(|A_1(j,\cdot)|^2\bigr)(-i-j).
--   \end{aligned}
--   $$
--   It dominates the heat jump expectations uniformly in the variances, because Gaussian averages are controlled by the maximal function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MeshJump.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MeshJump.lean by skeleton subtraction
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

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

def jumpMax (D : Finset ℤ) (A : Three → Matrix D D ℂ) (i j : D) : ℝ :=
  2*lineMax D (fun m => ‖A 0 i m‖^2) j+
  2*lineMax D (fun m => ‖A 0 m j‖^2) i+
  lineMax D (fun m => ‖A 2 m i‖^2) (-(i:ℤ)-(j:ℤ))+
  lineMax D (fun m => ‖A 1 j m‖^2) (-(i:ℤ)-(j:ℤ))

end
end TriangularHilbert.Heat
end

end OAI



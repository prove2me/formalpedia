-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
-- name    : OAI_Analysis_TriangularHilbert_DiscretePairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:44:03.415599+00:00
-- url     : https://prove2.me/theorems/6716086b-f295-41a9-af84-4527ad50f856
-- title:
--   Kernel outputs and the discrete cyclic pairing
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Let $u_i$ be grid positions with mesh $h$, and let $K_{ij}$ be a family of kernels indexed by pairs of grid points.
--
--   1. **Kernel output.** For matrices $B,C$,
--   $$
--   \mathrm{kernelOutput}(B,C)(i,j)=\sum_k h\,B_{jk}\,C_{ki}\,K_{ij}(u_i+u_j+u_k),
--   $$
--   a discretized version of $\int B(z_2,c)\,C(c,z_1)\,K(z_1+z_2+c)\,dc$.
--   2. **Pairing.** For a triangle array $A$,
--   $$
--   \mathrm{kernelPairing}(A)=\sum_{i,j}h^2A_0(i,j)\,\mathrm{kernelOutput}(A_1,A_2)(i,j),
--   $$
--   the cyclic trilinear form with entry-dependent kernels.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/DiscretePairing.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/DiscretePairing.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

def kernelOutput (B C : Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) (i j : ι) : ℂ :=
  ∑ k, (h:ℂ)*B j k*C k i*(K i j (u i+u j+u k):ℂ)

def kernelPairing (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) : ℂ :=
  ∑ i, ∑ j, (h^2:ℝ)*A 0 i j*kernelOutput (A 1) (A 2) h u K i j

end
end TriangularHilbert.Heat
end

end OAI



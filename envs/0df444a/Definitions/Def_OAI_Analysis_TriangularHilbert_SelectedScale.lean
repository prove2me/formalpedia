-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
-- name    : OAI_Analysis_TriangularHilbert_SelectedScale
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:42:32.640993+00:00
-- url     : https://prove2.me/theorems/1f62b9a8-2974-4f41-8865-904b1835f2a3
-- title:
--   Smooth truncated kernels and the selected cyclic sum
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The signed kernel at scale $s$ is $\kappa_s(t)=\frac{t^3/27-ts/3}{s\sqrt s}\phi_{3s}(t)$, where $\phi_\sigma$ is the centred Gaussian density of variance $\sigma$.
--
--   1. **Smooth kernel.** For scales $0<a\le b$, $\mathrm{smoothKernel}(a,b,t)=\int_a^b\kappa_s(t)\,\frac{ds}s$.
--   2. **Selected sum.** With an entry-dependent scale window $[a_{ij},b_{ij}]$,
--   $$
--   \mathrm{selectedSum}=\sum_{i,j,k}h^3A_0(i,j)A_1(j,k)A_2(k,i)\,\mathrm{smoothKernel}(a_{ij},b_{ij},u_i+u_j+u_k).
--   $$
--   3. **Masked signed form.** $\mathrm{maskedSigned}(s)=\mathrm{signedCenter}(\mathrm{maskedArray}(s))/s$, the single-scale form restricted to entries active at time $s$.
--   4. **Constant.** $C_{\mathrm{sel}}=\frac{440}3\cdot3\cdot C_{\mathrm{mask}}/c_\ast>0$, with $c_\ast$ the strict dissipation constant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SelectedScale.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SelectedScale.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def smoothKernel (a b t : ℝ) : ℝ := ∫ s in a..b, signedKernel s t / s

def selectedSum (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*(smoothKernel (a i j) (b i j) (u i+u j+u k):ℂ)

def maskedSigned (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) (s : ℝ) : ℂ :=
  signedCenter (maskedArray A a b s) h u s / (s:ℂ)

def selectedConstant : ℝ := (440/3)*3*maskedConstant/strictConstant
lemma selectedConstant_pos : 0 < selectedConstant := by
  unfold selectedConstant
  exact div_pos (mul_pos (by norm_num) maskedConstant_pos) strictConstant_pos

end
end TriangularHilbert.Heat
end

end OAI



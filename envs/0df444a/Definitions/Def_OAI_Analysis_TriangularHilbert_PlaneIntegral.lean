-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
-- name    : OAI_Analysis_TriangularHilbert_PlaneIntegral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:38:05.525235+00:00
-- url     : https://prove2.me/theorems/c46a06ed-d0f8-47b8-8975-7ac1fd09ca7f
-- title:
--   Integrals over the plane of centres and their integrability
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The three heat centres are constrained by $p_0+p_1+p_2=d$.
--
--   1. **Plane integral.** For $f:\mathbb R^3\to\mathbb R$,
--   $$
--   \mathrm{planeIntegral}(f,d)=\int_{\mathbb R^2}f\bigl(z_1,z_2,d-z_1-z_2\bigr)\,dz ,
--   $$
--   computed in chart $2$.
--   2. **Integrability package.** $\mathrm{HeatPlaneIntegrable}(A,h,u,d,\sigma)$ asserts that for every chart $i$ and all vertices, the heat energies, first variations, second variations, variance terms, Hessian costs and mixed terms (for three distinct vertices) are integrable as functions of $z$ in that chart.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneIntegral.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneIntegral.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

def planeIntegral (f : (Three → ℝ) → ℝ) (d : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, f (chart 2 d z)

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

structure HeatPlaneIntegrable (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) : Prop where
  energy : ∀ i v, Integrable (fun z => heatEnergy A h u (chart i d z) σ v)
  first : ∀ i v w, Integrable (fun z => heatFirst A h u (chart i d z) σ v w)
  pure : ∀ i v w, Integrable (fun z => heatPure A h u (chart i d z) σ v w)
  variance : ∀ i v w, Integrable (fun z => heatVariance A h u (chart i d z) σ v w)
  cost : ∀ i v w, Integrable (fun z => heatCost A h u (chart i d z) σ v w)
  mixed : ∀ i v w z, w ≠ v → z ≠ v → w ≠ z → Integrable (fun x => heatMixed A h u (chart i d x) σ v w z)

end
end TriangularHilbert.Heat
end

end OAI



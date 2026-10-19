-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
-- name    : OAI_Analysis_TriangularHilbert_HeatBound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:32:22.5795+00:00
-- url     : https://prove2.me/theorems/a004060f-ea9c-4aaf-b7ce-7b600f4a167f
-- title:
--   Uniform bounds on heat energies and their variations
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For a fixed array $A$, mesh $h$, positions $u$, centres $p$ and variances $\sigma$, the heat-weighted star energies have first variations, second variations, Hessian costs and mixed Hessian terms at every vertex.
--
--   The structure $\mathrm{HeatAtBounds}(A,h,u,p,\sigma,M)$ records that all of these are bounded by $M$ in absolute value:
--   $$
--   |\mathrm{heatEnergy}(v)|,\ |\mathrm{heatFirst}(v,w)|,\ |\mathrm{heatPure}(v,w)|,\ |\mathrm{heatVariance}(v,w)|,\ |\mathrm{heatCost}(v,w)|\le M ,
--   $$
--   and $|\mathrm{heatMixed}(v,w,z)|\le M$ whenever $w\ne v$ and $z\ne v$. Such bounds, made uniform on compact sets of parameters, justify differentiation under the integral.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HeatBound.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HeatBound.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

structure HeatAtBounds (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (M : ℝ) : Prop where
  energy : ∀ v, ‖heatEnergy A h u p σ v‖ ≤ M
  first : ∀ v w, ‖heatFirst A h u p σ v w‖ ≤ M
  pure : ∀ v w, ‖heatPure A h u p σ v w‖ ≤ M
  variance : ∀ v w, ‖heatVariance A h u p σ v w‖ ≤ M
  cost : ∀ v w, ‖heatCost A h u p σ v w‖ ≤ M
  mixed : ∀ v w z, w ≠ v → z ≠ v → ‖heatMixed A h u p σ v w z‖ ≤ M

end
end TriangularHilbert.Heat
end

end OAI



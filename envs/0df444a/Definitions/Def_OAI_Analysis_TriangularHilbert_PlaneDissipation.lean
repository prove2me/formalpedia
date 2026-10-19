-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
-- name    : OAI_Analysis_TriangularHilbert_PlaneDissipation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:40:52.187858+00:00
-- url     : https://prove2.me/theorems/511ccbe1-185d-47ef-afb6-aaa42d5e68a4
-- title:
--   Total plane energy, time derivative and strict dissipation constants
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Heat energies are integrated over the plane of centres $p_0+p_1+p_2=d$.
--
--   1. **Total energy.** $\mathrm{totalPlaneEnergy}=\sum_v\mathrm{planeIntegral}(\mathrm{heatEnergy}(\cdot,v),d)$.
--   2. **Time derivative.** With variances $\sigma_w=\alpha_ws$ growing linearly in the time $s$,
--   $$
--   \mathrm{totalPlaneTime}(s)=\sum_v\sum_w\alpha_w\,\mathrm{planeIntegral}\bigl(\mathrm{heatVariance}(\cdot,v,w),d\bigr),
--   $$
--   which is the derivative of the total energy in $s$.
--   3. **Strict rates.** $\mathrm{strictRate}(i,w)=1$ if $w=i$ and $\frac{11}{10}$ otherwise, and the dissipation constant is
--   $$
--   c_\ast=\tfrac12\min\bigl(1-\tfrac35\sqrt2,\ \tfrac{11}{10}-\tfrac12\sqrt2\bigr)>0 .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneDissipation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneDissipation.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def totalPlaneEnergy (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) : ℝ :=
  ∑ v, planeIntegral (fun p => heatEnergy A h u p σ v) d

def totalPlaneTime (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (α : Three → ℝ) (s : ℝ) : ℝ :=
  ∑ v, ∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d

def strictRate (i w : Three) : ℝ := if w = i then 1 else 11/10

def strictConstant : ℝ := (1/2) * min (1 - (3/5)*Real.sqrt 2) (11/10 - (1/2)*Real.sqrt 2)

lemma strictConstant_pos : 0 < strictConstant := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg (2:ℝ)
  have h1 : 0 < 1 - (3/5)*Real.sqrt 2 := by nlinarith
  have h2 : 0 < 11/10 - (1/2)*Real.sqrt 2 := by nlinarith
  exact mul_pos (by norm_num) (lt_min h1 h2)

end
end TriangularHilbert.Heat
end

end OAI



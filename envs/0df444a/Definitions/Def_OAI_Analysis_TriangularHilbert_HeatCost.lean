-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
-- name    : OAI_Analysis_TriangularHilbert_HeatCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:19:32.189005+00:00
-- url     : https://prove2.me/theorems/fcf47609-27a4-47f4-ad8c-e7ca442eb7dc
-- title:
--   Hessian costs, mixed Hessian terms and score matrices of the heat flow
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For the heat-weighted star at vertex $v$, $\mathrm{localGram}(v,w)$ is the weighted Gram matrix of its bare row or column, and $\mathrm{localFirst}(v,w)$ is its derivative in the centre $p_w$.
--
--   1. **Heat cost.** $\mathrm{heatCost}(v,w)=\mathrm{hessianCost}\bigl(\mathrm{localGram}(v,w),\mathrm{localFirst}(v,w)\bigr)$, the Hessian part of the second centre derivative.
--   2. **Mixed term.** For two directions $w,z$,
--   $$
--   \mathrm{heatMixed}(v,w,z)=\mathrm{hessianPair}\bigl(\mathrm{localGram}(v,w),\mathrm{localFirst}(v,w),\mathrm{localFirst}(v,z)\bigr).
--   $$
--   3. **Scores.** $\mathrm{heatScores}(w)$ is the diagonal matrix of scores $(u_i-p_w)/\sigma_w$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HeatCost.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HeatCost.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def heatCost (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) : ℝ :=
  hessianCost (localGram A h u p σ v w) (localFirst A h u p σ v w)

def heatMixed (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w z : Three) : ℝ :=
  hessianPair (localGram A h u p σ v w) (localFirst A h u p σ v w)
    (localFirst A h u p σ v z)

def heatScores (u : ι → ℝ) (p σ : Three → ℝ) : Three → Matrix ι ι ℂ :=
  fun w => Matrix.diagonal (fun i => (score (u i) (p w) (σ w) : ℂ))

end
end TriangularHilbert.Heat
end

end OAI



-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
-- name    : OAI_Analysis_TriangularHilbert_SignedTraceOrder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:41:46.881649+00:00
-- url     : https://prove2.me/theorems/6fe3373b-cf4b-45a8-b85b-0bbbc231dec6
-- title:
--   Window diagonals and the cyclic window trace
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$.
--
--   1. **Window diagonals.** For a vertex $v$ with centre $p_v$ and scale $s$, $\mathrm{windowDiags}(v)$ is the diagonal matrix with entries $\mathrm{windowRatio}(s,u_i-p_v)$, the odd Gaussian window divided by the Gaussian of variance $\frac{11}{10}s$.
--   2. **Window trace.** With heat arrays $\tilde A$ of variance $\frac{11}{10}s$ at all three vertices,
--   $$
--   \mathrm{windowTrace}=\operatorname{tr}\bigl(W_0\tilde A_0\,W_1\tilde A_1\,W_2\tilde A_2\bigr),
--   $$
--   where $W_v$ are the window diagonals. It is a cyclic trilinear expression with odd windows at the three vertices, written as a trace of a product of matrices around the triangle.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SignedTraceOrder.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SignedTraceOrder.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def windowDiags (u : ι → ℝ) (p : Three → ℝ) (s : ℝ) : Three → Matrix ι ι ℂ :=
  fun v => Matrix.diagonal (fun i => (windowRatio s (u i-p v):ℂ))

def windowTrace (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p : Three → ℝ) (s : ℝ) : ℂ :=
  Matrix.trace (windowDiags u p s 0 * heatArray A h u p (fun _ => (11/10)*s) 0 *
    windowDiags u p s 1 * heatArray A h u p (fun _ => (11/10)*s) 1 *
    windowDiags u p s 2 * heatArray A h u p (fun _ => (11/10)*s) 2)

end
end TriangularHilbert.Heat
end

end OAI



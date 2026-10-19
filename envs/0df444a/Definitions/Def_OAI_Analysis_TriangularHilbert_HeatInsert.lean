-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
-- name    : OAI_Analysis_TriangularHilbert_HeatInsert
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:21:32.070188+00:00
-- url     : https://prove2.me/theorems/fa50cb62-23f6-45f6-a5a7-f8d4eb7e1928
-- title:
--   Carriers and diagonal masks for inserted heat derivatives
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Indices are pairs $(w,i)$ of a vertex $w\in\{0,1,2\}$ and a grid index $i$.
--
--   1. **Carrier.** For the heat array at vertex $v$, $\mathrm{heatCarrier}(v,w)$ is the star row $\mathrm{rowStar}(\mathrm{heatArray},v)$ if $w=v$ and its adjoint otherwise.
--   2. **Mask.** For real numbers $d_w(i)$,
--   $$
--   \mathrm{heatMask}(d)=\operatorname{diag}\bigl(d_w(i)\bigr)_{(w,i)},
--   $$
--   the block-diagonal matrix with one diagonal block per vertex. Inserting such a mask between a carrier and its adjoint expresses derivatives of the star Gram matrix along the heat flow.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HeatInsert.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HeatInsert.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def heatCarrier (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) :=
  if w = v then rowStar (heatArray A h u p σ) v else (rowStar (heatArray A h u p σ) v)ᴴ

def heatMask (d : Three → ι → ℝ) : Matrix (BlockSpace ι) (BlockSpace ι) ℂ :=
  blockD (fun w => Matrix.diagonal (fun i => (d w i : ℂ)))

end
end TriangularHilbert.Heat
end

end OAI



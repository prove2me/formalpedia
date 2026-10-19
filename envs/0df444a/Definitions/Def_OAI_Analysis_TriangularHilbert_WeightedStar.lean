-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
-- name    : OAI_Analysis_TriangularHilbert_WeightedStar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:14:36.344689+00:00
-- url     : https://prove2.me/theorems/eec8bc64-e505-4162-a97e-dbaea7562293
-- title:
--   Vertex-weighted triangle arrays and bare rows
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Indices are pairs $(v,i)$ of a vertex $v\in\{0,1,2\}$ of the triangle and a grid index $i$.
--
--   1. **Vertex root.** For weights $g_v(i)\ge0$, $\mathrm{vertexRoot}(g)$ is the diagonal matrix with entries $\sqrt{g_v(i)}$.
--   2. **Weighted array.** The edge $v$ (from vertex $v$ to vertex $v+1$) of an array $A$ is reweighted by
--   $$
--   \mathrm{weightedArray}(A,g)_v(i,j)=\sqrt{g_v(i)}\,A_v(i,j)\,\sqrt{g_{v+1}(j)} .
--   $$
--   3. **Bare rows.** $\mathrm{rowBare}(A,g,v)=\mathrm{rowStar}(A,v)\cdot\mathrm{vertexRoot}(g)$ and $\mathrm{colBare}(A,g,v)=\mathrm{rowStar}(A,v)^*\cdot\mathrm{vertexRoot}(g)$ factor the weighted rows so that weights can later be moved into a Gram matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/WeightedStar.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/WeightedStar.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def vertexRoot (g : Three → ι → ℝ) : Matrix (BlockSpace ι) (BlockSpace ι) ℂ :=
  Matrix.diagonal (fun a => (Real.sqrt (g a.1 a.2) : ℂ))

def weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) : Three → Matrix ι ι ℂ :=
  fun v i j => (Real.sqrt (g v i) : ℂ) * A v i j * (Real.sqrt (g (v+1) j) : ℂ)

def rowBare (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :=
  rowStar A v * vertexRoot g

def colBare (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :=
  (rowStar A v)ᴴ * vertexRoot g

end
end TriangularHilbert.MatrixEnergy
end

end OAI



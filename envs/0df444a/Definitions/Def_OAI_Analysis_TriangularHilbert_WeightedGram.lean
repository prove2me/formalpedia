-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
-- name    : OAI_Analysis_TriangularHilbert_WeightedGram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:13:02.71834+00:00
-- url     : https://prove2.me/theorems/91b78810-abc7-442c-ab75-8e7009658aff
-- title:
--   Weighted Gram matrices
-- statement:
--   For a complex square matrix $B$ indexed by a finite set and a real weight vector $w$, the weighted Gram matrix is
--   $$
--   \mathrm{weightedGram}(B,w)=B^*\,\operatorname{diag}(w)\,B .
--   $$
--   When $w\ge0$ it is positive semidefinite, and it is linear in $w$. In the heat-flow analysis of the triangular Hilbert transform, the weights $w$ are Gaussian heat weights or their first and second derivatives in the centre. So derivatives of Gram matrices along the heat flow are again weighted Gram matrices with the same base $B$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/WeightedGram.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/WeightedGram.lean by skeleton subtraction
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

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def weightedGram (B : Matrix ι ι ℂ) (w : ι → ℝ) : Matrix ι ι ℂ :=
  Bᴴ * Matrix.diagonal (fun i => (w i : ℂ)) * B

end
end TriangularHilbert.MatrixEnergy
end

end OAI



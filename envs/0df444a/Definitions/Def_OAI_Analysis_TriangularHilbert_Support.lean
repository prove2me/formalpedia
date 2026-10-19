-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_Support
-- name    : OAI_Analysis_TriangularHilbert_Support
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:11:28.45045+00:00
-- url     : https://prove2.me/theorems/11d8d2ef-d6e5-4739-8ac9-6f06e5dcd7f2
-- title:
--   Polarized Hessian pairing of the matrix energy
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. The Hessian cost $\mathrm{hessianCost}(P,K)$ is $\frac32\sup_X\bigl(2\langle K,X\rangle-\langle X,\sqrt PX+X\sqrt P\rangle\bigr)$, the quadratic form of the second derivative of $E$ at $P$ in direction $K$.
--
--   The Hessian pairing of two directions $K,L$ is obtained by polarization:
--   $$
--   \mathrm{hessianPair}(P,K,L)=\frac{\mathrm{hessianCost}(P,K+L)-\mathrm{hessianCost}(P,K-L)}4 .
--   $$
--   For positive definite $P$ it is the symmetric bilinear form $\frac32\langle K,\mathrm{sylv}_{\sqrt P}^{-1}L\rangle$ associated with the Hessian cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Support.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Support.lean by skeleton subtraction
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

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

noncomputable def hessianPair (P K L : Matrix ι ι ℂ) : ℝ :=
  (hessianCost P (K + L) - hessianCost P (K - L)) / 4

end TriangularHilbert.MatrixEnergy
end

end OAI



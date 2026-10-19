-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
-- name    : OAI_Analysis_TriangularHilbert_InitialAlgebra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:02:04.07307+00:00
-- url     : https://prove2.me/theorems/bcd8e1c1-afab-44b1-8e05-16f7269e6189
-- title:
--   Hilbert–Schmidt square and cube of a matrix
-- statement:
--   For a complex square matrix $R$ indexed by a finite set:
--
--   1. **Hilbert–Schmidt square.** $\mathrm{hsSquare}(R)=\sum_{i,j}|R_{ij}|^2=\|R\|_{\mathrm{HS}}^2$.
--   2. **Hilbert–Schmidt cube.**
--   $$
--   \mathrm{hsCube}(R)=\mathrm{hsSquare}(R)\sqrt{\mathrm{hsSquare}(R)}=\|R\|_{\mathrm{HS}}^3 .
--   $$
--
--   The matrix energy $\operatorname{tr}(R^*R)^{3/2}$ is at most $\|R\|_{\mathrm{HS}}^3$, since the Schatten $3$-norm is dominated by the Schatten $2$-norm. This gives the initial bound on star energies at the start of the heat flow.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/InitialAlgebra.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/InitialAlgebra.lean by skeleton subtraction
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

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

def hsSquare (R : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖R i j‖^2

def hsCube (R : Matrix ι ι ℂ) : ℝ := hsSquare R * Real.sqrt (hsSquare R)

end
end TriangularHilbert.MatrixEnergy
end

end OAI



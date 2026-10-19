-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
-- name    : OAI_Analysis_TriangularHilbert_NormBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:20:33.713705+00:00
-- url     : https://prove2.me/theorems/500a9a44-5300-4536-aace-f4ea6ad967d0
-- title:
--   Entrywise norm constant for complex matrices
-- statement:
--   For a finite index set $\iota$, the entry norm constant is
--   $$
--   C_\iota=\sum_{i\in\iota}\sum_{j\in\iota}\bigl\|E_{ij}\bigr\| ,
--   $$
--   where $E_{ij}$ is the matrix unit with a single entry $1$ at position $(i,j)$ and the norm is the $\ell^2$ operator norm.
--
--   Writing $M=\sum_{i,j}M_{ij}E_{ij}$ and using the triangle inequality gives $\|M\|\le C_\iota\max_{i,j}|M_{ij}|$. So bounds on matrix entries yield bounds on operator norms with a constant depending only on the size of the index set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/NormBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/NormBounds.lean by skeleton subtraction
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

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def entryNormConstant (ι : Type uι) [Fintype ι] [DecidableEq ι] : ℝ :=
  ∑ i : ι, ∑ j : ι, ‖(Matrix.single i j (1 : ℂ))‖

end
end TriangularHilbert.MatrixEnergy
end

end OAI



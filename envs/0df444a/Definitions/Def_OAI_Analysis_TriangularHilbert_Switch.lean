-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
-- name    : OAI_Analysis_TriangularHilbert_Switch
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:22:31.787967+00:00
-- url     : https://prove2.me/theorems/b22b0b39-2fdd-43a3-b146-33f4eae932c0
-- title:
--   Opening and window switches for matrix entries
-- statement:
--   For real thresholds $a,b$, a time $s$ and a complex entry $A$:
--
--   1. **Opening.** $\mathrm{opening}(a,s,A)=A$ if $a\le s$, and $0$ otherwise.
--   2. **Window.**
--   $$
--   \mathrm{windowMask}(a,b,s,A)=\begin{cases}A,&a\le s<b,\\0,&\text{otherwise.}\end{cases}
--   $$
--
--   Applied entrywise with thresholds $a_{ij}<b_{ij}$, the window keeps an entry only during its own scale window $[a_{ij},b_{ij})$. This encodes truncation endpoints that vary from entry to entry.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Switch.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Switch.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar

namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def opening (a s : ℝ) (A : ℂ) : ℂ := if a ≤ s then A else 0

def windowMask (a b s : ℝ) (A : ℂ) : ℂ := if a ≤ s ∧ s < b then A else 0

end
end TriangularHilbert
end

end OAI



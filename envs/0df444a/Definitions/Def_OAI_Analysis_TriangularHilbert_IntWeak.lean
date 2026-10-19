-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
-- name    : OAI_Analysis_TriangularHilbert_IntWeak
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:08:24.329466+00:00
-- url     : https://prove2.me/theorems/e18b99ae-00bc-4241-afea-8ab7d22978ec
-- title:
--   Integer intervals
-- statement:
--   For an integer $n$ and a radius $r\in\mathbb N$, the integer interval is
--   $$
--   \mathrm{intInterval}(n,r)=\{m\in\mathbb Z:n-r\le m\le n+r\},
--   $$
--   a finite set of $2r+1$ consecutive integers centred at $n$. These intervals are the discrete balls on $\mathbb Z$ used to define the discrete Hardy–Littlewood maximal function. They also enter a Vitali-type covering argument that gives its weak-type and strong-type bounds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/IntWeak.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/IntWeak.lean by skeleton subtraction
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

namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def intInterval (n : ℤ) (r : ℕ) : Finset ℤ := Finset.Icc (n-r) (n+r)

end
end TriangularHilbert
end

end OAI



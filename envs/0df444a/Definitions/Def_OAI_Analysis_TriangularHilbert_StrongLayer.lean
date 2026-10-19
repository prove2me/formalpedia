-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
-- name    : OAI_Analysis_TriangularHilbert_StrongLayer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:10:41.80366+00:00
-- url     : https://prove2.me/theorems/00b51674-41af-45b0-92ca-76f255978045
-- title:
--   Layer functions for the strong maximal inequality
-- statement:
--   For $a>0$ and $t\in\mathbb R$:
--
--   1. $\mathrm{squareLayer}(a,t)=t^2$ if $0<t<\sqrt a$, and $0$ otherwise.
--   2. $\mathrm{oneLayer}(a,t)=1$ if $0<t<\sqrt a$, and $0$ otherwise.
--
--   They appear in a layer-cake decomposition: for $a>0$,
--   $$
--   a=\int_0^\infty\mathrm{oneLayer}(a,t)\,2t\,dt ,
--   $$
--   and similar identities express powers of $a$ as integrals over levels. This is how the weak-type bound for the discrete maximal function is upgraded to an $L^p$ bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/StrongLayer.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/StrongLayer.lean by skeleton subtraction
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

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def squareLayer (a t : ℝ) : ℝ := (Set.Ioo 0 (Real.sqrt a)).indicator (fun t => t^2) t

def oneLayer (a t : ℝ) : ℝ := (Set.Ioo 0 (Real.sqrt a)).indicator (fun _ => (1:ℝ)) t

end
end TriangularHilbert
end

end OAI



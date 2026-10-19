-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
-- name    : OAI_Analysis_TriangularHilbert_SortedWindows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:28:23.447685+00:00
-- url     : https://prove2.me/theorems/9d0aa7fa-0f5d-42bb-82ef-c062154502d9
-- title:
--   Sorted switching times
-- statement:
--   For a nonempty finite set $S\subset\mathbb R$ of times and $k\in\mathbb N$, $\mathrm{sortedTimes}(S,k)$ is the $k$-th smallest element of $S$ (counting from $0$), capped at the largest element:
--   $$
--   \mathrm{sortedTimes}(S,k)=t_{\min(k,|S|-1)},\qquad t_0<t_1<\dots<t_{|S|-1}\ \text{the elements of }S .
--   $$
--   The switching times of all entry windows are sorted this way. Between consecutive times the set of active entries is constant, and the heat flow energy argument is applied on each such interval.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SortedWindows.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SortedWindows.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def sortedTimes (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) : ℝ :=
  S.orderEmbOfFin rfl ⟨min k (S.card-1),lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (Finset.card_pos.mpr hS) (by omega))⟩

end
end TriangularHilbert
end

end OAI



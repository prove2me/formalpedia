-- Prove2me | Definitions.Def_OAIQ034H007
-- name    : OAIQ034H007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:41:41.500246+00:00
-- url     : https://prove2.me/theorems/886b31de-3233-4dfc-bb50-b69a4cf679e6
-- title:
--   Definitions bundle OAIQ034H007 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 298 declarations of OpenAI's Lean: 63 definitions, 4 instances and 231 theorems. The definitions and types are `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.allTurnDart`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.boundaryTransition`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.faceOccurrence`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.mappedMacroPolygon`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.partSelect`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.topSlot`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.triangleFace`, `OAI.HyperbolicObstruction.ConeSkeleton.SixChain`, `OAI.HyperbolicObstruction.ConeSkeleton.collapsedBoundary`, `OAI.HyperbolicObstruction.ConeSkeleton.fanCollapsedWalk`, `OAI.HyperbolicObstruction.ConeSkeleton.macroRoute`, `OAI.HyperbolicObstruction.ConeSkeleton.normalWordPicture`, `OAI.HyperbolicObstruction.ConeSkeleton.occurrenceTrial`, `OAI.HyperbolicObstruction.ConeSkeleton.topCollapsedWalk`, `OAI.HyperbolicObstruction.CoreWordGraph.inclusion`, `OAI.HyperbolicObstruction.FanLink.FanData.boundary`, `OAI.HyperbolicObstruction.FanLink.FanData.colored`, `OAI.HyperbolicObstruction.FanLink.FanData.payments`, `OAI.HyperbolicObstruction.FanLink.FanData.state`, `OAI.HyperbolicObstruction.FanLink.FanData.triangles`, `OAI.HyperbolicObstruction.FanLink.FanData.turns`, `OAI.HyperbolicObstruction.FanLink.IndexedFanData.boundary`, `OAI.HyperbolicObstruction.FanLink.IndexedFanData.decode`, `OAI.HyperbolicObstruction.FanLink.IndexedFanData.linkEquiv`, `OAI.HyperbolicObstruction.FanLink.IndexedFanData.markFin`, `OAI.HyperbolicObstruction.FanLink.IndexedFanData.nextFin`, `OAI.HyperbolicObstruction.FanLink.IndexedFanData.numberLink`, `OAI.HyperbolicObstruction.FanLink.IndexedFanData.toFin`, `OAI.HyperbolicObstruction.FanLink.IndexedFanData.triangles`, `OAI.HyperbolicObstruction.FanLink.IndexedFanData.turns`, `OAI.HyperbolicObstruction.FanLink.Mark.color`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape.Good`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape.fans`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape.shape`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape.sixes`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape.squares`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape.tops`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.GoodUpTo`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.Shape.Good` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_ActualLabel`, `HyperbolicGroups_ActualOccurrenceShape`, `HyperbolicGroups_BoundaryRotation`, `HyperbolicGroups_ConeCellCollapse`, `HyperbolicGroups_ConeLetterCollapse`, `HyperbolicGroups_ConeTopCollapse`, `HyperbolicGroups_ContactCapacity`, `HyperbolicGroups_CoreWordGraph`, `HyperbolicGroups_ExteriorTarget`, `HyperbolicGroups_FanActivation`, `HyperbolicGroups_FanApex`, `HyperbolicGroups_FanRoute`, `HyperbolicGroups_FiniteFanData`, `HyperbolicGroups_Graph`, `HyperbolicGroups_GraphSubstitution`, `HyperbolicGroups_GraphWordFilling`, `HyperbolicGroups_IndexedBoundaryPullback`, `HyperbolicGroups_IndexedFanCards`, `HyperbolicGroups_IndexedFanCounts`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_IndexedPayment`, `HyperbolicGroups_LocalWeightedRank`, `HyperbolicGroups_MacroCertificate`, `HyperbolicGroups_MacroCycle`, `HyperbolicGroups_MacroFaceFilling`, `HyperbolicGroups_NormalDiskArea`, `HyperbolicGroups_NormalFaceFilling`, `HyperbolicGroups_OneFaceFilling`, `HyperbolicGroups_OutsideComponentFilling`, `HyperbolicGroups_PictureFillingAlgebra`, `HyperbolicGroups_PolygonBoundaryList`, `HyperbolicGroups_PolygonFilling`, `HyperbolicGroups_RankCollection`, `HyperbolicGroups_RelativeApexAggregate`, `HyperbolicGroups_RelativeContact`, `HyperbolicGroups_RelativeDegree`, `HyperbolicGroups_RelativeFaceCounts`, `HyperbolicGroups_RelativeFragment`, `HyperbolicGroups_RelativeGlobalStep`, `HyperbolicGroups_RelativeInteriorCount`, `HyperbolicGroups_RelativeLayers`, `HyperbolicGroups_RelativeMacroPolygon`, `HyperbolicGroups_RelativePartition`, `HyperbolicGroups_RelativePartitionEstimate`, `HyperbolicGroups_RelativePayment`, `HyperbolicGroups_RelativeRadialBoundary`, `HyperbolicGroups_RelativeRawAccount`, `HyperbolicGroups_RelativeRawCount`, `HyperbolicGroups_RelativeRawPosition`, `HyperbolicGroups_RelativeSlots`, `HyperbolicGroups_RelativeTopTurns`, `HyperbolicGroups_RelativeTriangleTransport`, `HyperbolicGroups_RelativeTurnTransport`, `HyperbolicGroups_RestrictOccurrence`, `HyperbolicGroups_Shape`, `HyperbolicGroups_WalkRawPosition`, `HyperbolicGroups_WeightedRank`, `HyperbolicGroups_WordDisk`, `HyperbolicGroups_WordSubstitution`.
--
--   **Imports.** It imports the bundles `OAIQ034H003` and `OAIQ034H004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ034H011`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ034H003
import Definitions.Def_OAIQ034H004

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Graph
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

/-- The unoriented field of a core adjacency. -/
def coreEdge {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) : Edge := by
  cases a with
  | inl r =>
    cases b with
    | inl _ => exact h.elim
    | inr l => exact ⟨(r,l), h⟩
  | inr l =>
    cases b with
    | inl r => exact ⟨(r,l), h⟩
    | inr _ => exact h.elim

lemma coreStep_field {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) :
    (coreStep h).field = .inl (coreEdge h) := by
  cases a <;> cases b <;> first | exact h.elim | rfl

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroCertificate
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.MacroGraph
open IncidenceTemplate

instance instDecidableCertificate (p q : Fin 7) : Decidable (Certificate p q) := by
  unfold Certificate
  infer_instance

lemma certificate_0_0 : Certificate 0 0 := by decide
lemma certificate_0_1 : Certificate 0 1 := by decide
lemma certificate_0_2 : Certificate 0 2 := by decide
lemma certificate_0_3 : Certificate 0 3 := by decide
lemma certificate_0_4 : Certificate 0 4 := by decide
lemma certificate_0_5 : Certificate 0 5 := by decide
lemma certificate_0_6 : Certificate 0 6 := by decide
lemma certificate_1_0 : Certificate 1 0 := by decide
lemma certificate_1_1 : Certificate 1 1 := by decide
lemma certificate_1_2 : Certificate 1 2 := by decide
lemma certificate_1_3 : Certificate 1 3 := by decide
lemma certificate_1_4 : Certificate 1 4 := by decide
lemma certificate_1_5 : Certificate 1 5 := by decide
lemma certificate_1_6 : Certificate 1 6 := by decide
lemma certificate_2_0 : Certificate 2 0 := by decide
lemma certificate_2_1 : Certificate 2 1 := by decide
lemma certificate_2_2 : Certificate 2 2 := by decide
lemma certificate_2_3 : Certificate 2 3 := by decide
lemma certificate_2_4 : Certificate 2 4 := by decide
lemma certificate_2_5 : Certificate 2 5 := by decide
lemma certificate_2_6 : Certificate 2 6 := by decide
lemma certificate_3_0 : Certificate 3 0 := by decide
lemma certificate_3_1 : Certificate 3 1 := by decide
lemma certificate_3_2 : Certificate 3 2 := by decide
lemma certificate_3_3 : Certificate 3 3 := by decide
lemma certificate_3_4 : Certificate 3 4 := by decide
lemma certificate_3_5 : Certificate 3 5 := by decide
lemma certificate_3_6 : Certificate 3 6 := by decide
lemma certificate_4_0 : Certificate 4 0 := by decide
lemma certificate_4_1 : Certificate 4 1 := by decide
lemma certificate_4_2 : Certificate 4 2 := by decide
lemma certificate_4_3 : Certificate 4 3 := by decide
lemma certificate_4_4 : Certificate 4 4 := by decide
lemma certificate_4_5 : Certificate 4 5 := by decide
lemma certificate_4_6 : Certificate 4 6 := by decide
lemma certificate_5_0 : Certificate 5 0 := by decide
lemma certificate_5_1 : Certificate 5 1 := by decide
lemma certificate_5_2 : Certificate 5 2 := by decide
lemma certificate_5_3 : Certificate 5 3 := by decide
lemma certificate_5_4 : Certificate 5 4 := by decide
lemma certificate_5_5 : Certificate 5 5 := by decide
lemma certificate_5_6 : Certificate 5 6 := by decide
lemma certificate_6_0 : Certificate 6 0 := by decide
lemma certificate_6_1 : Certificate 6 1 := by decide
lemma certificate_6_2 : Certificate 6 2 := by decide
lemma certificate_6_3 : Certificate 6 3 := by decide
lemma certificate_6_4 : Certificate 6 4 := by decide
lemma certificate_6_5 : Certificate 6 5 := by decide
lemma certificate_6_6 : Certificate 6 6 := by decide

lemma certificate (p q : Fin 7) : Certificate p q := by
  fin_cases p <;> fin_cases q
  · exact certificate_0_0
  · exact certificate_0_1
  · exact certificate_0_2
  · exact certificate_0_3
  · exact certificate_0_4
  · exact certificate_0_5
  · exact certificate_0_6
  · exact certificate_1_0
  · exact certificate_1_1
  · exact certificate_1_2
  · exact certificate_1_3
  · exact certificate_1_4
  · exact certificate_1_5
  · exact certificate_1_6
  · exact certificate_2_0
  · exact certificate_2_1
  · exact certificate_2_2
  · exact certificate_2_3
  · exact certificate_2_4
  · exact certificate_2_5
  · exact certificate_2_6
  · exact certificate_3_0
  · exact certificate_3_1
  · exact certificate_3_2
  · exact certificate_3_3
  · exact certificate_3_4
  · exact certificate_3_5
  · exact certificate_3_6
  · exact certificate_4_0
  · exact certificate_4_1
  · exact certificate_4_2
  · exact certificate_4_3
  · exact certificate_4_4
  · exact certificate_4_5
  · exact certificate_4_6
  · exact certificate_5_0
  · exact certificate_5_1
  · exact certificate_5_2
  · exact certificate_5_3
  · exact certificate_5_4
  · exact certificate_5_5
  · exact certificate_5_6
  · exact certificate_6_0
  · exact certificate_6_1
  · exact certificate_6_2
  · exact certificate_6_3
  · exact certificate_6_4
  · exact certificate_6_5
  · exact certificate_6_6


end HyperbolicObstruction.MacroGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroCycle
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.MacroGraph
open IncidenceTemplate

/-- Every nonempty vertex subset all of whose vertices have two distinct
neighbors in the subset contains at least three point vertices. -/
theorem three_points (S : Finset Vertex) (hne : S.Nonempty)
    (hn : ∀ v ∈ S, ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Adjacent v a ∧ Adjacent v b) :
    3 ≤ (Finset.univ.filter (fun i => point i ∈ S)).card := by
  classical
  by_contra! hc
  let P := Finset.univ.filter (fun i => point i ∈ S)
  have hP : P.card ≤ 2 := by dsimp [P]; omega
  obtain ⟨p,q,hpq⟩ : ∃ p q : Fin 7, ∀ i ∈ P, i = p ∨ i = q := by
    rcases Nat.lt_or_eq_of_le hP with h | h
    · have h' : P.card ≤ 1 := by omega
      by_cases hp : P.Nonempty
      · obtain ⟨p,hp⟩ := hp
        exact ⟨p,p,fun i hi => Or.inl ((Finset.card_le_one.mp h') i hi p hp)⟩
      · exact ⟨0,0,fun i hi => False.elim (hp ⟨i,hi⟩)⟩
    · obtain ⟨p,q,_,hpq⟩ := Finset.card_eq_two.mp h
      refine ⟨p,q,?_⟩
      intro i hi
      simpa only [hpq,Finset.mem_insert,Finset.mem_singleton] using hi
  have ha : ∀ v ∈ S, Allowed p q v := by
    intro v hv
    rcases v with ((i|l)|⟨⟩)
    · apply hpq i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    · trivial
    · trivial
  obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image S (rank p q) hne
  obtain ⟨a,haS,b,hbS,hab,hva,hvb⟩ := hn v hv
  exact hab (certificate p q v a b ⟨ha v hv, ha a haS, ha b hbS, hva, hvb,
    hmin a haS, hmin b hbS⟩)

namespace Polygon
variable (P : Polygon)

def points : Finset (Fin 7) := Finset.univ.filter (fun i => point i ∈ P.vertices)

lemma points_ge (h : 0 < P.n) : 3 ≤ P.points.card := by
  apply three_points P.vertices _ P.two_neighbors
  exact ⟨P.vertex ⟨0,h⟩,Finset.mem_image.mpr ⟨⟨0,h⟩,Finset.mem_univ _,rfl⟩⟩

end Polygon
end HyperbolicObstruction.MacroGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


/-! Algebraic van Kampen existence, with actual words and area-counted local
moves (not a finiteness or isoperimetric assumption). Free cancellation has
zero cost; each orientation of a listed relator disk has cost one. -/
noncomputable section
namespace HyperbolicObstruction.WordPictures

variable {A : Type*}

namespace Move
variable {R : Set (Word A)} {u v : Word A} {n : ℕ}
lemma contextual (h : Move R u v n) (l r : Word A) :
    Move R (l ++ u ++ r) (l ++ v ++ r) n := by
  cases h with
  | free h => exact free (h.append_left.append_right)
  | face l' r' w h => simpa only [List.append_assoc] using face (l++l') (r'++r) w h
  | reverseFace l' r' w h =>
      simpa only [List.append_assoc] using reverseFace (l++l') (r'++r) w h

lemma reverse (h : Move R u v n) : Move R (FreeGroup.invRev u) (FreeGroup.invRev v) n := by
  cases h with
  | free h => exact free h.invRev
  | face l r w h =>
    simpa only [FreeGroup.invRev_append,List.append_assoc] using
      reverseFace (FreeGroup.invRev r) (FreeGroup.invRev l) w h
  | reverseFace l r w h =>
    simpa only [FreeGroup.invRev_append,FreeGroup.invRev_invRev,List.append_assoc] using
      face (FreeGroup.invRev r) (FreeGroup.invRev l) w h
end Move

namespace Homotopy
variable {R : Set (Word A)} {u v w : Word A} {n : ℕ}
lemma contextual (h : Homotopy R u v n) (l r : Word A) :
    Homotopy R (l ++ u ++ r) (l ++ v ++ r) n := by
  induction h with
  | refl => exact refl _
  | move h => exact move (h.contextual l r)
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
lemma reverse (h : Homotopy R u v n) :
    Homotopy R (FreeGroup.invRev u) (FreeGroup.invRev v) n := by
  induction h with
  | refl => exact refl _
  | move h => exact move h.reverse
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'

lemma of_reduction (h : FreeGroup.Red u v) : Homotopy R u v 0 := by
  induction h with
  | refl => exact refl _
  | tail h h' ih => simpa using ih.trans (move (.free h'))

/-- Equality in the free group uses only free folds, not a face relator. -/
lemma free (h : FreeGroup.mk u = FreeGroup.mk v) : Homotopy R u v 0 := by
  obtain ⟨z,hz,hz'⟩ := FreeGroup.Red.exact.mp h
  simpa using (of_reduction hz).trans (of_reduction hz').symm

lemma conjugate (h : Homotopy R u [] n) (q : Word A) :
    Homotopy R (q++u++FreeGroup.invRev q) [] n := by
  have h1 : Homotopy R (q++u++FreeGroup.invRev q) (q++FreeGroup.invRev q) n := by
    simpa using h.contextual q (FreeGroup.invRev q)
  have h2 : Homotopy R (q++FreeGroup.invRev q) [] 0 := free (by
    rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,← FreeGroup.one_eq_mk,mul_inv_cancel])
  simpa using h1.trans h2
end Homotopy

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Shape
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace Occurrences

namespace Shape
variable {s u q v : ℕ} (T : Shape s u q)

def coreCoord (a : Fin s) (e : Edge) : T.Pos v :=
  if he : isLoose e then .inl a else
    .inr (.inl ⟨(T.2.1 a (pointOfRepresentative e.val.1)).val,
      ⟨.inl e, by
        simp only [rowSupport,Finset.mem_map,Function.Embedding.inl_apply,
          Sum.inl.injEq]
        refine ⟨e,?_,rfl⟩
        simp only [fan,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨(T.2.1 a (pointOfRepresentative e.val.1)).property.symm,he⟩⟩⟩)

def topCoord (a : Fin s) (f : rowSupport (.inr (.inl ()))) : T.Pos v :=
  match f with
  | ⟨.inl e,_⟩ => T.coreCoord a e
  | ⟨.inr _,h⟩ => False.elim (by simp [rowSupport] at h)

/-- Every position refers to the original arrays. A top is its independent
mark, not a new independent copy of its correlated fan entries. -/
def row {A : Type*} (σ : T.Pos v → A) : Trial s u q v → Entry A
  | .inl a => .inl ⟨.inr (.inl ()),fun f => σ (T.topCoord a f)⟩
  | .inr (.inl b) => .inl ⟨.inl (T.1 b),fun f => σ (.inr (.inl ⟨b,f⟩))⟩
  | .inr (.inr (.inl e)) => .inl ⟨.inr (.inr (T.2.2 e)),fun f => σ (.inr (.inr (.inl ⟨e,f⟩)))⟩
  | .inr (.inr (.inr e)) => .inr (fun i => σ (.inr (.inr (.inr (e,i)))))

/-- The source good-rank condition for this literal collection shape. -/
def Good {n : ℕ} (α β δ : ℝ) (w : Entry (SymmetricAlphabet n) → Bool) : Prop :=
  ∀ σ : T.Pos v → SymmetricAlphabet n,
    Function.Injective (T.row σ) → BernoulliCandidates.Present T.row w σ →
      (Coincidence.unsignedRank σ : ℝ) ≤
        ((3-β)-7*(2-α))*s + (2-α)*u + (2-δ)*q + (3-δ)*v

end Shape
end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualOccurrenceShape
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma occurrence_core_value (a : Fin (Fintype.card (Top n w))) (e : IncidenceTemplate.Edge) :
    occurrenceValues n w d ((occurrenceShape n w).coreCoord a e) = ((enumTop n w).symm a).val e := by
  unfold Occurrences.Shape.coreCoord
  split_ifs with he
  · change ((enumTop n w).symm a).val loose = _
    rw [loose_unique e he]
  · apply fan_value_congr n w ((enumFan n w).symm_apply_apply
      (slot n w ((enumTop n w).symm a) (pointOfRepresentative e.val.1))) e
    simp [rowSupport, slot, fan]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, rfl, he⟩

def occurrenceTrial : OccurrenceTrial n w d → Occurrences.Entry (Alphabet n)
  | .inl a => .inl (TableModel.row rowSupport (extendCore n ((enumTop n w).symm a).val) (.inr (.inl ())))
  | .inr (.inl b) => .inl ⟨.inl ((enumFan n w).symm b).val.1, ((enumFan n w).symm b).val.2⟩
  | .inr (.inr (.inl e)) => .inl ⟨.inr (.inr ((enumSquare n w).symm e).1), ((enumSquare n w).symm e).2.val⟩
  | .inr (.inr (.inr e)) => .inr ((enumSix n d).symm e).val

lemma occurrence_row (r : OccurrenceTrial n w d) :
    (occurrenceShape n w).row (occurrenceValues n w d) r = occurrenceTrial n w d r := by
  rcases r with a | (b | (e | e))
  · apply congrArg Sum.inl
    change (⟨.inr (.inl ()),_⟩ : TableModel.Entry rowSupport) = ⟨.inr (.inl ()),_⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    funext f
    rcases f with ⟨f,hf⟩
    rcases f with e | g
    · exact occurrence_core_value n w d a e
    · simp [rowSupport] at hf
  · rfl
  · rfl
  · rfl

lemma occurrenceTrial_injective : Function.Injective (occurrenceTrial n w d) := by
  intro x y h
  rcases x with a | (b | (e | f)) <;> rcases y with a' | (b' | (e' | f'))
  · apply congrArg Sum.inl
    apply (enumTop n w).symm.injective
    apply Subtype.ext
    exact top_row_injective n (Sum.inl.inj h)
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · cases h
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · apply congrArg (Sum.inr ∘ Sum.inl)
    apply (enumFan n w).symm.injective
    apply Subtype.ext
    have hh := Sum.inl.inj h
    change (⟨.inl _,_⟩ : TableModel.Entry rowSupport) = ⟨.inl _,_⟩ at hh
    have hb := Sum.inl.inj (congrArg Sigma.fst hh)
    apply Sigma.ext hb
    exact (Sigma.mk.inj_iff.mp hh).2
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · cases h
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · cases (congrArg Sigma.fst (Sum.inl.inj h))
  · apply congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl)
    apply (enumSquare n w).symm.injective
    have hinj : Function.Injective (fun x : Square n w =>
        (⟨.inr (.inr x.1),x.2.val⟩ : TableModel.Entry rowSupport)) := by
      rintro ⟨e,⟨v,hv⟩⟩ ⟨e',⟨v',hv'⟩⟩ hh
      have he : e = e' := Sum.inr.inj (Sum.inr.inj (congrArg Sigma.fst hh))
      subst e'
      have hvv : v = v' := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
      subst v'
      rfl
    exact hinj (Sum.inl.inj h)
  · cases h
  · cases h
  · cases h
  · cases h
  · apply congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inr)
    apply (enumSix n d).symm.injective
    exact Subtype.ext (Sum.inr.inj h)

lemma occurrence_row_injective : Function.Injective ((occurrenceShape n w).row (occurrenceValues n w d)) := by
  intro x y h
  rw [occurrence_row,occurrence_row] at h
  exact occurrenceTrial_injective n w d h

lemma occurrence_present : BernoulliCandidates.Present (occurrenceShape n w).row
    (Sum.elim w d) (occurrenceValues n w d) := by
  intro r
  rw [occurrence_row]
  rcases r with a | (b | (e | e))
  · exact ((enumTop n w).symm a).property.1
  · exact ((enumFan n w).symm b).property
  · exact ((enumSquare n w).symm e).2.property
  · exact ((enumSix n d).symm e).property

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRawPosition
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Reversed label sides at the SAME indexed position are literally opposite
indexed steps. This excludes indexed loops in the coincidence-contact graph. -/
lemma raw_position_reverse {s t : WalkStep n w d}
    (hs : isLetter n w (walkLabel n w d s) = true)
    (ht : isLetter n w (walkLabel n w d t) = true)
    (hp : rawPosition n w d s = rawPosition n w d t)
    (he : walkLabel n w d t = rev n w (walkLabel n w d s)) :
    t = walkOpposite n w d s := by
  have hc := raw_step_cases n w d s hs
  have hd := raw_step_cases n w d t ht
  rw [← hp] at hd
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · rw [hc,hd] at he
    exact False.elim (rev_ne n w _ he.symm)
  · rw [hc,hd]
  · rw [hc,hd,walkOpposite_twice]
  · rw [hc,hd] at he
    exact False.elim (rev_ne n w _ he.symm)

universe u

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualLabel
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma squareSide_field (q : Square n w) (i : Fin 4) :
    (squareSide n w q i).1 = .inl ((q.2.val (squareField q.1 i)).1) := by
  fin_cases i <;>
    simp only [squareSide,letterDart,stepLetter,apply_ite,inverseLetter]
  all_goals simp [extendRow,squareField,rowSupport,squareSupport,MasterGraph.first,MasterGraph.second]
  all_goals split_ifs <;> rfl

lemma representative_value (p : RawPosition n w d) :
    (walkLabel n w d (rawRepresentative n w d p)).1 =
      .inl ((occurrenceValues n w d (rawToPosition n w d p)).1) := by
  rcases p with a | (⟨b,e⟩ | (⟨q,i⟩ | ⟨q,i⟩))
  · change Sum.inl (a.val loose).1 = _
    simp only [rawToPosition,occurrenceValues,Equiv.symm_apply_apply]
  · change Sum.inl ((fanLetter n w ⟨b,e⟩).1) = _
    simp only [rawToPosition,occurrenceValues]
    apply congrArg Sum.inl
    apply congrArg Prod.fst
    exact fan_value_congr n w (Equiv.symm_apply_apply (enumFan n w) b).symm e.val _ _
  · change (squareSide n w q i).1 = _
    rw [squareSide_field]
    simp only [rawToPosition,occurrenceValues]
    apply congrArg Sum.inl
    apply congrArg Prod.fst
    exact square_value_congr n w ((enumSquare n w).symm_apply_apply q).symm _ _ _
  · change Sum.inl (q.val i).1 = _
    simp only [rawToPosition,occurrenceValues,Equiv.symm_apply_apply]

/-- Contact labels are compared only after forgetting orientation. Equal
unsigned labels are not used to identify distinct indexed positions. -/
lemma raw_label_value (s : WalkStep n w d) (hr : isLetter n w (walkLabel n w d s) = true) :
    (walkLabel n w d s).1 =
      .inl ((occurrenceValues n w d (rawToPosition n w d (rawPosition n w d s))).1) := by
  rcases raw_step_cases n w d s hr with h | h
  · conv_lhs => rw [h]
    exact representative_value n w d _
  · conv_lhs => rw [h,walkOpposite_label]
    exact representative_value n w d _

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section

namespace HyperbolicObstruction.WordPictures
namespace Homotopy
variable {A : Type*} {R : Set (Word A)} {u v : Word A} {k : ℕ}
/-- Moving the boundary basepoint is area-free for a null word; it is not
asserted that a cyclic shift represents the same free-group element. -/
lemma rotate_null (h : Homotopy R (v++u) [] k) : Homotopy R (u++v) [] k := by
  have hf : FreeGroup.mk (u++v) = FreeGroup.mk (u++(v++u)++FreeGroup.invRev u) := by
    simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk]
    group
  simpa only [Nat.zero_add] using (Homotopy.free hf).trans (h.conjugate u)
lemma unrotate_null {w : Word A} (i : ℕ) (hi : i ≤ w.length)
    (h : Homotopy R (w.rotate i) [] k) : Homotopy R w [] k := by
  rw [List.rotate_eq_drop_append_take hi] at h
  simpa only [List.take_append_drop] using h.rotate_null
end Homotopy

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonBoundaryList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C L V : Type*} (B : PolygonTarget.Boundary C L V)

lemma positiveSides_label (c : C) : (B.positiveSides c).map B.sideLabel = B.attachingWord c := by
  simp only [positiveSides,List.map_map,sideLabel,Function.comp_def,ite_true]
  exact List.ofFn_eq_map.symm

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphWordFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.GraphWordFilling
open SimpleGraph WordPictures
variable {V A : Type*} {G : SimpleGraph V}

lemma short_filling (r : G.Dart → A × Bool)
    (hr : ∀ e, r e.symm = ((r e).1,!(r e).2)) (R : Set (Word A))
    {u v : V} (h : G.Adj u v) (p : G.Walk v u) (hp : p.length + 1 < 3) :
    Homotopy R (word r (.cons h p)) [] 0 := by
  apply Homotopy.free
  have hv : ∀ e : G.Dart, FreeGroup.mk [r e.symm] = (FreeGroup.mk [r e])⁻¹ := by
    intro e
    rw [hr]
    rfl
  have hh := GraphGroupWalk.short_loop_eval (fun e => FreeGroup.mk [r e]) hv h p hp
  have he {a b : V} (q : G.Walk a b) :
      FreeGroup.mk (word r q) = GraphGroupWalk.eval (fun e => FreeGroup.mk [r e]) q := by
    induction q with
    | nil => rfl
    | cons h q ih =>
      change FreeGroup.mk ([r ⟨_,h⟩] ++ word r q) = _
      rw [← FreeGroup.mul_mk,ih]
      rfl
  exact (he _).trans hh

/-- Quantitative noncommutative loop erasure. Each deleted elementary cycle
costs one, and each backtrack costs zero. The residual path pays for its own
length; no relator injection or distinct-letter assumption is needed. -/
theorem path_filling (r : G.Dart → A × Bool)
    (hr : ∀ e, r e.symm = ((r e).1,!(r e).2)) (R : Set (Word A))
    (hR : ∀ (u : V) (p : G.Walk u u), p.IsCycle → word r p ∈ R)
    {u v : V} (p : G.Walk u v) :
    ∃ (q : G.Walk u v) (a : ℕ), q.IsPath ∧
      Homotopy R (word r p) (word r q) a ∧ a + q.length ≤ p.length := by
  classical
  induction p with
  | nil => exact ⟨.nil,0,Walk.IsPath.nil,WordPictures.Homotopy.refl _,by simp⟩
  | @cons u v w h p ih =>
    obtain ⟨q,a,hq,he,ha⟩ := ih
    have he' : Homotopy R (word r (.cons h p)) (word r (.cons h q)) a := by
      simpa only [List.nil_append,List.append_nil,List.singleton_append,word_cons] using
        he.contextual [r ⟨(u,v),h⟩] []
    by_cases hu : u ∈ q.support
    · let s := q.takeUntil u hu
      let t := q.dropUntil u hu
      have hst : s.append t = q := q.take_spec hu
      have hs : s.IsPath := hq.takeUntil hu
      have ht : t.IsPath := hq.dropUntil hu
      have hlen : s.length + t.length = q.length := by rw [← Walk.length_append,hst]
      obtain ⟨k,hk,hklen⟩ : ∃ k, Homotopy R (word r (.cons h s)) [] k ∧ k ≤ s.length + 1 := by
        by_cases hl : 3 ≤ s.length + 1
        · have hc : (Walk.cons h s).IsCycle :=
            Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa using hs,hl⟩
          refine ⟨1,?_,by omega⟩
          simpa only [List.nil_append,List.append_nil] using
            (Homotopy.move (Move.face [] [] _ (hR _ _ hc)))
        · exact ⟨0,short_filling r hr R h s (by omega),by omega⟩
      have hkt : Homotopy R (word r (.cons h q)) (word r t) k := by
        have hh := hk.contextual [] (word r t)
        simpa only [List.nil_append,← word_append,Walk.cons_append,hst] using hh
      refine ⟨t,a+k,ht,he'.trans hkt,?_⟩
      simp only [Walk.length_cons]
      omega
    · refine ⟨.cons h q,a,hq.cons hu,he',?_⟩
      simp only [Walk.length_cons]
      omega

/-- A closed graph walk of length L
has a disk derivation over its simple cycles using at most L relator disks. -/
theorem closed_filling (r : G.Dart → A × Bool)
    (hr : ∀ e, r e.symm = ((r e).1,!(r e).2)) (R : Set (Word A))
    (hR : ∀ (u : V) (p : G.Walk u u), p.IsCycle → word r p ∈ R)
    {u : V} (p : G.Walk u u) :
    ∃ a ≤ p.length, Homotopy R (word r p) [] a := by
  obtain ⟨q,a,hq,hh,ha⟩ := path_filling r hr R hR p
  have hn := Walk.isPath_iff_nil.mp hq
  cases hn
  exact ⟨a,by simpa using ha,hh⟩

end HyperbolicObstruction.GraphWordFilling
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CoreWordGraph
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry MasterGraph LetterPresentation SimpleGraph
variable (S : Finset IncidenceTemplate.Edge)

lemma core_edge_mem {a b : CoreGeometry.Vertex} (h : (graph S).Adj a b) :
    MasterGraph.coreEdge (core_adj S h) ∈ S := by
  cases a <;> cases b <;> try exact h.elim
  all_goals
    have hold := h
    obtain ⟨e,he,hm⟩ := h
    have hh : MasterGraph.coreEdge (core_adj S hold) = e := Subtype.ext he.symm
    rwa [hh]

lemma label_rev (n : ℕ) (l : Field → Alphabet n) (e : (graph S).Dart) :
    label S n l e.symm = ((label S n l e).1,!(label S n l e).2) := by
  rcases e with ⟨⟨a,b⟩,h⟩
  cases a <;> cases b <;> try exact h.elim
  all_goals
    dsimp [label,SimpleGraph.Dart.symm,coreStep,stepLetter,Step.pos,Step.neg,inverseLetter] <;>
      simp only [Bool.not_not]

end HyperbolicObstruction.CoreWordGraph
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FanRoute
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry SimpleGraph

lemma fanRoute_length (i : Fin 7) (v : FanVertex i) : (fanRoute i v).length ≤ 2 := by
  rcases v with ⟨r|l,h⟩ <;> simp [fanRoute]

/-- Inclusion in the core does not alter the orientation or the literal
random field used by an edge. -/
def inclusion (S : Finset IncidenceTemplate.Edge) : graph S →g graph Finset.univ where
  toFun := id
  map_rel' := by
    intro a b h
    cases a <;> cases b <;> try exact h.elim
    all_goals obtain ⟨e,he,hm⟩ := h; exact ⟨e,he,Finset.mem_univ _⟩

lemma inclusion_word (S : Finset IncidenceTemplate.Edge) (n : ℕ)
    (l : Field → LetterPresentation.Alphabet n) {a b : CoreGeometry.Vertex} (p : (graph S).Walk a b) :
    GraphWordFilling.word (label Finset.univ n l) (p.map (inclusion S)) =
      GraphWordFilling.word (label S n l) p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [SimpleGraph.Walk.map_cons,GraphWordFilling.word_cons,ih]; rfl

end HyperbolicObstruction.CoreWordGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.GraphWordFilling
open SimpleGraph
variable {V W A : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma word_reverse (r : G.Dart → A × Bool)
    (hr : ∀ e, r e.symm = ((r e).1,!(r e).2)) {u v : V} (p : G.Walk u v) :
    word r p.reverse = FreeGroup.invRev (word r p) := by
  simp only [word,Walk.darts_reverse,List.map_reverse,List.map_map,FreeGroup.invRev]
  congr 1
  apply List.map_congr_left
  intro e he
  exact hr e

lemma expand_word (f : V → W) (r : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    (l : H.Dart → A × Bool) {u v : V} (p : G.Walk u v) :
    word l (expand f r p) = p.darts.flatMap (fun e => word l (r e.adj)) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [expand,word_append,ih,Walk.darts_cons,List.flatMap_cons]

end HyperbolicObstruction.GraphWordFilling
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeLetterCollapse
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma collapse_rev (e : Dart n w) : collapse n w (rev n w e) = FreeGroup.invRev (collapse n w e) := by
  rcases e with ⟨a|⟨f,v⟩,b⟩ <;> cases b <;>
    simp only [collapse,rev,Bool.not_false,Bool.not_true,FreeGroup.invRev_invRev] <;> rfl

lemma collapse_letter (a : Alphabet n) : collapse n w (letterDart n w a) = [a] := rfl

def collapsedBoundary (c : Cell n w d) : List (Alphabet n) :=
  (List.ofFn (side n w d c)).flatMap (collapse n w)

lemma fan_edge_adj (f : FanTriangle n w) :
    (CoreWordGraph.graph (fan f.1.val.1)).Adj (fanLeft n w f).val (fanRight n w f).val :=
  ⟨f.2.val,rfl,f.2.property⟩

lemma fan_edge_label (f : FanTriangle n w) :
    CoreWordGraph.label (fan f.1.val.1) n (extendRow n (.inl f.1.val.1) f.1.val.2)
      ⟨((fanLeft n w f).val,(fanRight n w f).val),fan_edge_adj n w f⟩ = fanLetter n w f := by
  change extendRow n (.inl f.1.val.1) f.1.val.2 (.inl f.2.val) = _
  simp [extendRow,fanLetter,show (.inl f.2.val : Field) ∈ rowSupport (.inl f.1.val.1) from
    by simp [rowSupport]]

def fanCollapsedWalk (f : FanTriangle n w) :
    (CoreWordGraph.graph (fan f.1.val.1)).Walk (.inl (CoreWordGraph.base f.1.val.1))
      (.inl (CoreWordGraph.base f.1.val.1)) :=
  (CoreWordGraph.fanRoute f.1.val.1 (fanLeft n w f)).append
    (.cons (fan_edge_adj n w f) (CoreWordGraph.fanRoute f.1.val.1 (fanRight n w f)).reverse)

lemma fanCollapsedWalk_length (f : FanTriangle n w) : (fanCollapsedWalk n w f).length ≤ 5 := by
  have hl := CoreWordGraph.fanRoute_length f.1.val.1 (fanLeft n w f)
  have hr := CoreWordGraph.fanRoute_length f.1.val.1 (fanRight n w f)
  simp only [fanCollapsedWalk,Walk.length_append,Walk.length_cons,Walk.length_reverse]
  omega

lemma fanCollapsedWalk_word (f : FanTriangle n w) :
    GraphWordFilling.word (CoreWordGraph.label (fan f.1.val.1) n (extendRow n (.inl f.1.val.1) f.1.val.2))
      (fanCollapsedWalk n w f) = collapsedBoundary n w d (.inl f) := by
  rw [fanCollapsedWalk,GraphWordFilling.word_append,GraphWordFilling.word_cons,
    GraphWordFilling.word_reverse _ (CoreWordGraph.label_rev _ _ _),fan_edge_label]
  change _ = radialWord n w f.1 (fanLeft n w f) ++
    ([fanLetter n w f] ++ (FreeGroup.invRev (radialWord n w f.1 (fanRight n w f)) ++ []))
  simp only [List.append_nil, List.singleton_append, radialWord]

/-- The actual source fan-triangle substitution, including backtracking fan
paths, needs no more than five faces of the finite simple-cycle presentation. -/
theorem fan_collapse_filling (f : FanTriangle n w) :
    ∃ a ≤ 5, WordPictures.Homotopy (SimpleWordRelator n w d)
      (collapsedBoundary n w d (.inl f)) [] a := by
  let l := extendRow n (.inl f.1.val.1) f.1.val.2
  have hp : w (TableModel.row rowSupport l (.inl f.1.val.1)) = true := by
    simpa only [l,row_extend] using f.1.property
  obtain ⟨a,ha,hh⟩ := GraphWordFilling.closed_filling
    (CoreWordGraph.label (fan f.1.val.1) n l) (CoreWordGraph.label_rev _ _ _)
    (SimpleWordRelator n w d) (fun v p h => SimpleWordRelator.fan l f.1.val.1 hp v p h)
    (fanCollapsedWalk n w f)
  refine ⟨a,ha.trans (fanCollapsedWalk_length n w f),?_⟩
  dsimp only [l] at hh
  rw [fanCollapsedWalk_word n w d f] at hh
  exact hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeTopCollapse
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction
namespace CoreWordGraph
open IncidenceTemplate CoreGeometry LetterPresentation SimpleGraph

lemma label_congr (S : Finset IncidenceTemplate.Edge) (n : ℕ)
    (l k : Field → Alphabet n) (h : ∀ e ∈ S, l (.inl e) = k (.inl e)) (e : (graph S).Dart) :
    label S n l e = label S n k e := by
  unfold label stepLetter
  rw [MasterGraph.coreStep_field,h _ (core_edge_mem S e.adj)]

lemma word_congr (S : Finset IncidenceTemplate.Edge) (n : ℕ)
    (l k : Field → Alphabet n) (h : ∀ e ∈ S, l (.inl e) = k (.inl e))
    {a b : CoreGeometry.Vertex} (p : (graph S).Walk a b) :
    GraphWordFilling.word (label S n l) p = GraphWordFilling.word (label S n k) p := by
  unfold GraphWordFilling.word
  apply List.map_congr_left
  intro e he
  exact label_congr S n l k h e

end CoreWordGraph
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma slot_radial_word (a : Top n w) (i : Fin 7) (v : FanVertex i) :
    GraphWordFilling.word (CoreWordGraph.label Finset.univ n (extendCore n a.val))
      ((CoreWordGraph.fanRoute i v).map (CoreWordGraph.inclusion (fan i))) =
      radialWord n w (slot n w a i) v := by
  rw [CoreWordGraph.inclusion_word]
  apply CoreWordGraph.word_congr
  intro e he
  simp [extendRow,slot,show (.inl e : Field) ∈ rowSupport (.inl i) from by simpa [rowSupport] using he]

/-- Send apex i to its fixed actual fan base and expand radial edges by
fixed fan paths. The exceptional two-step incidence uses the genuine loose
letter, not a fictitious eighth fan. -/
def macroRoute {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    (CoreWordGraph.graph Finset.univ).Walk (macroBase u) (macroBase v) := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · exact (CoreWordGraph.fanRoute i ⟨.inr m,h⟩).map (CoreWordGraph.inclusion (fan i))
  · have hi : i = 3 := h
    subst i
    exact (CoreWordGraph.fanRoute 3 ⟨.inl 3,by decide⟩).map (CoreWordGraph.inclusion (fan 3))
  · exact ((CoreWordGraph.fanRoute j ⟨.inr l,h⟩).map (CoreWordGraph.inclusion (fan j))).reverse
  · exact h.elim
  · have hl : l = 4 := h
    subst l
    exact .cons (show (CoreWordGraph.graph Finset.univ).Adj (.inr 4) (.inl 3) from
      ⟨loose,rfl,Finset.mem_univ _⟩) .nil
  · have hj : j = 3 := h
    subst j
    exact ((CoreWordGraph.fanRoute 3 ⟨.inl 3,by decide⟩).map (CoreWordGraph.inclusion (fan 3))).reverse
  · have hm : m = 4 := h
    subst m
    exact .cons (show (CoreWordGraph.graph Finset.univ).Adj (.inl 3) (.inr 4) from
      ⟨loose,rfl,Finset.mem_univ _⟩) .nil
  · exact h.elim

lemma macroRoute_length {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    (macroRoute h).length ≤ 2 := by
  have mapped_length (i : Fin 7) (v : FanVertex i) :
      ((CoreWordGraph.fanRoute i v).map (CoreWordGraph.inclusion (fan i))).length ≤ 2 :=
    (Walk.length_map (CoreWordGraph.inclusion (fan i)) (CoreWordGraph.fanRoute i v)).trans_le
      (CoreWordGraph.fanRoute_length i v)
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · exact mapped_length i ⟨.inr m, h⟩
  · have hi : i = 3 := h; subst i
    exact mapped_length 3 ⟨.inl 3, by decide⟩
  · exact (Walk.length_reverse _).trans_le (mapped_length j ⟨.inr l, h⟩)
  · exact h.elim
  · have hl : l = 4 := h; subst l
    change (1 : ℕ) ≤ 2
    decide
  · have hj : j = 3 := h; subst j
    exact (Walk.length_reverse _).trans_le (mapped_length 3 ⟨.inl 3, by decide⟩)
  · have hm : m = 4 := h; subst m
    change (1 : ℕ) ≤ 2
    decide
  · exact h.elim

lemma macroRoute_word (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    GraphWordFilling.word (CoreWordGraph.label Finset.univ n (extendCore n a.val)) (macroRoute h) =
      collapse n w (macroStep n w a h) := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · exact slot_radial_word n w a i ⟨.inr m,h⟩
  · have hi : i = 3 := h; subst i
    exact slot_radial_word n w a 3 ⟨.inl 3,by decide⟩
  · change GraphWordFilling.word _ ((CoreWordGraph.fanRoute j ⟨.inr l,h⟩).map _).reverse = _
    rw [GraphWordFilling.word_reverse _ (CoreWordGraph.label_rev _ _ _),slot_radial_word]
    rfl
  · exact h.elim
  · have hl : l = 4 := h; subst l
    change [inverseLetter n (a.val loose)] = _
    rfl
  · have hj : j = 3 := h; subst j
    change GraphWordFilling.word _ ((CoreWordGraph.fanRoute 3 ⟨.inl 3,by decide⟩).map _).reverse = _
    rw [GraphWordFilling.word_reverse _ (CoreWordGraph.label_rev _ _ _),slot_radial_word]
    rfl
  · have hm : m = 4 := h; subst m
    rfl
  · exact h.elim

def topCollapsedWalk (a : TopPolygon n w) :
    (CoreWordGraph.graph Finset.univ).Walk (macroBase a.2.1) (macroBase a.2.1) :=
  GraphWordFilling.expand macroBase (fun {_ _} h => macroRoute h) a.2.2.val

lemma topCollapsedWalk_length (a : TopPolygon n w) : (topCollapsedWalk n w a).length ≤ 30 := by
  have hl := GraphWordFilling.expand_length macroBase (fun {_ _} h => macroRoute h)
    2 (fun {_ _} h => macroRoute_length h) a.2.2.val
  have hp := MacroGraph.cycle_perimeter a.2.2.val a.2.2.property
  exact hl.trans (by omega)

lemma topCollapsedWalk_word (a : TopPolygon n w) :
    GraphWordFilling.word (CoreWordGraph.label Finset.univ n (extendCore n a.1.val))
      (topCollapsedWalk n w a) = collapsedBoundary n w d (.inr (.inl a)) := by
  rw [topCollapsedWalk,GraphWordFilling.expand_word]
  change _ = (List.ofFn (topSide n w a)).flatMap (collapse n w)
  rw [← macro_darts n w a.1 a.2.2.val a.2.2.property,List.flatMap_map]
  apply List.flatMap_congr
  intro e he
  exact macroRoute_word n w a.1 e.adj

/-- Every actual simple top polygon collapses to a core closed walk of length
at most thirty, and hence to at most thirty exact finite-presentation faces. -/
theorem top_collapse_filling (a : TopPolygon n w) :
    ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
      (collapsedBoundary n w d (.inr (.inl a))) [] k := by
  obtain ⟨k,hk,hh⟩ := GraphWordFilling.closed_filling
    (CoreWordGraph.label Finset.univ n (extendCore n a.1.val)) (CoreWordGraph.label_rev _ _ _)
    (SimpleWordRelator n w d)
    (fun v p h => SimpleWordRelator.top (extendCore n a.1.val) a.1.property.1 a.1.property.2 v p h)
    (topCollapsedWalk n w a)
  exact ⟨k,hk.trans (topCollapsedWalk_length n w a),by rw [topCollapsedWalk_word n w d a] at hh; exact hh⟩

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
variable {A B : Type*}
variable (c : A × Bool → Word B) (hc : ∀ e, c (e.1,!e.2) = FreeGroup.invRev (c e))

include hc

namespace Move
variable {R : Set (Word A)} {S : Set (Word B)} {C k : ℕ}
variable (hR : ∀ z ∈ R, ∃ a ≤ C, Homotopy S (z.flatMap c) [] a)
include hR

lemma substitute {z t : Word A} (h : Move R z t k) :
    ∃ a ≤ C * k, Homotopy S (z.flatMap c) (t.flatMap c) a := by
  cases h with
  | free h => exact ⟨0,by simp,Homotopy.free (substitute_free_step c hc h)⟩
  | face l r z hz =>
    obtain ⟨a,ha,hh⟩ := hR z hz
    refine ⟨a,by simpa using ha,?_⟩
    simpa only [List.flatMap_append,List.append_nil] using hh.contextual (l.flatMap c) (r.flatMap c)
  | reverseFace l r z hz =>
    obtain ⟨a,ha,hh⟩ := hR z hz
    refine ⟨a,by simpa using ha,?_⟩
    simpa only [List.flatMap_append,substitute_reverse c hc,FreeGroup.invRev_empty,List.append_nil] using
      hh.reverse.contextual (l.flatMap c) (r.flatMap c)
end Move

namespace Homotopy
variable {R : Set (Word A)} {S : Set (Word B)} {C k : ℕ}
variable (hR : ∀ z ∈ R, ∃ a ≤ C, Homotopy S (z.flatMap c) [] a)
include hR

/-- Quantitative substitution of proved literal relator disks. All contexts,
free folds, reverse relators and intermediate words are retained. -/
theorem substitute {z t : Word A} (h : Homotopy R z t k) :
    ∃ a ≤ C * k, Homotopy S (z.flatMap c) (t.flatMap c) a := by
  induction h with
  | refl => exact ⟨0,by simp,Homotopy.refl _⟩
  | move h => exact h.substitute c hc hR
  | symm h ih => obtain ⟨a,ha,hh⟩ := ih; exact ⟨a,ha,hh.symm⟩
  | trans h h' ih ih' =>
    obtain ⟨a,ha,hh⟩ := ih
    obtain ⟨b,hb,hh'⟩ := ih'
    exact ⟨a+b,by rw [Nat.mul_add]; exact Nat.add_le_add ha hb,hh.trans hh'⟩
end Homotopy
end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeCellCollapse
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma square_collapsedBoundary (s : Square n w) :
    collapsedBoundary n w d (.inr (.inr (.inl s))) =
      literalSquare n (extendRow n (.inr (.inr s.1)) s.2.val) s.1 := by
  rfl

lemma six_collapsedBoundary (s : Six n d) :
    collapsedBoundary n w d (.inr (.inr (.inr s))) = List.ofFn s.val := by
  rfl

/-- Uniform factor 30 for every actual bounded normal-form cell. The
fan paths, macro walk, exceptional loose edge and both decoration families
have all been expanded literally into the finite simple-cycle presentation. -/
theorem cell_collapse_filling (a : Cell n w d) :
    ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
      (collapsedBoundary n w d a) [] k := by
  rcases a with f | (a | (s | s))
  · obtain ⟨k,hk,hh⟩ := fan_collapse_filling n w d f
    exact ⟨k,by omega,hh⟩
  · exact top_collapse_filling n w d a
  · rw [square_collapsedBoundary]
    have hp : w (TableModel.row rowSupport (extendRow n (.inr (.inr s.1)) s.2.val)
        (.inr (.inr s.1))) = true := by
      simpa only [row_extend] using s.2.property
    refine ⟨1,by decide,?_⟩
    simpa only [List.nil_append,List.append_nil] using
      WordPictures.Homotopy.move (WordPictures.Move.face [] [] _
        (SimpleWordRelator.square _ s.1 hp))
  · rw [six_collapsedBoundary]
    refine ⟨1,by decide,?_⟩
    simpa only [List.nil_append,List.append_nil] using
      WordPictures.Homotopy.move (WordPictures.Move.face [] [] _
        (SimpleWordRelator.six s.val s.property))

lemma collapse_letter_word (z : List (Alphabet n)) :
    (z.map (letterDart n w)).flatMap (collapse n w) = z := by
  induction z with
  | nil => rfl
  | cons a z ih => simp only [List.map_cons,List.flatMap_cons,collapse_letter,List.singleton_append,ih]

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ContactCapacity
attribute [-instance] _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
attribute [local instance] Classical.propDecidable
variable {X Y : Type*} [Fintype X] (P : PictureMap X)
variable (selected raw : X → Prop) (hraw : ∀ x, raw (P.edge x) ↔ raw x)
variable (position : X → Y) (p : Y)

include hraw in
/-- Contacts charge actual side copies injectively, even if the contact graph
has cycles or parallel edges. This is not a forest assumption. -/
theorem contact_capacity : Fintype.card (P.IncidentContact selected raw position p) ≤
    Fintype.card (PositionSide selected raw position p) := by
  let g : P.IncidentContact selected raw position p → PositionSide selected raw position p := fun e =>
    ⟨⟨(P.contactSide selected raw hraw (P.contactEnd selected raw position p e)).val,
      (P.contactSide selected raw hraw (P.contactEnd selected raw position p e)).property.1,
      (P.contactSide selected raw hraw (P.contactEnd selected raw position p e)).property.2.1⟩,
      P.contactEnd_position selected raw hraw position p e⟩
  apply Fintype.card_le_of_injective g
  intro e f h
  apply P.contactEnd_injective selected raw position p
  apply P.contactSide_injective selected raw hraw
  apply Subtype.ext
  exact congrArg (fun x : PositionSide selected raw position p => x.val.val) h

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ExteriorTarget
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkCellTarget
variable (T : WalkCellTarget S C W L V A)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → L)
  (closed : ∀ i, T.start (word (finRotate ell i)) = T.start (T.rev (word i)))

variable (B : FrozenTarget T)

/-- Protect precisely the added exterior sides. -/
def isExterior : S ⊕ T.ExteriorSide ell hell word closed → Prop := Sum.elim (fun _ => False) (fun _ => True)

end WalkCellTarget
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FanApex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink
open State

namespace Mark
variable {F O : Type*}

def color [DecidableEq O] (occ : F → O) (a : O) : Mark F → State
  | absent => .absent
  | triangle => .triangle
  | top f => if occ f = a then .dominant else .other

lemma color_active [DecidableEq O] (occ : F → O) (a : O) (m : Mark F) :
    (m.color occ a).active = m.plain.active := by
  cases m with
  | absent => rfl
  | triangle => rfl
  | top f => by_cases h : occ f = a <;> simp [color,plain,State.active,h]
lemma color_f [DecidableEq O] (occ : F → O) (a : O) (m : Mark F) :
    (m.color occ a).f = m.plain.f := by
  cases m with
  | absent => rfl
  | triangle => rfl
  | top f => by_cases h : occ f = a <;> simp [color,plain,State.f,h]
lemma color_turn [DecidableEq O] (occ : F → O) (a : O) (m : Mark F) :
    (m.color occ a).turn = m.plain.turn := by
  cases m with
  | absent => rfl
  | triangle => rfl
  | top f => by_cases h : occ f = a <;> simp [color,plain,State.turn,h]
end Mark

namespace FanData
variable {r S o : ℕ} (L : FanData r S o)

def state (z : Fin r) := Mark.plain ∘ L.mark z
def colored (a : Fin o) (z : Fin r) := Mark.color L.occurrence a ∘ L.mark z

def triangles : ℕ := ∑ z, Q (L.state z)
def turns : ℕ := ∑ z, T (L.state z)
def payments : ℕ := ∑ z, P (L.next z) (L.state z) (L.line z)
def boundary : ℕ := ∑ z, B (L.next z) (L.state z)

lemma turns_le : L.turns ≤ S := by
  have h := L.count_le (fun _ => True)
  simp only [Fintype.card_subtype_true,Fintype.card_fin,ite_true] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  cases he : L.mark z i <;> simp [state,Mark.plain,State.turn,he]

lemma color_counts (a : Fin o) :
    (∑ z, D (L.colored a z)) + (∑ z, N (L.colored a z)) = L.turns := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [← T_eq]
  apply Finset.sum_congr rfl
  intro i _
  exact Mark.color_turn _ _ _

lemma other_count_le (a : Fin o) : (∑ z, N (L.colored a z)) ≤ S - L.multiplicity a := by
  have h := L.count_le (fun f => L.occurrence f ≠ a)
  rw [Fintype.card_subtype_compl,Fintype.card_fin] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    cases he : L.mark z i with
    | absent => simp [colored,Mark.color,State.n,he]
    | triangle => simp [colored,Mark.color,State.n,he]
    | top f => by_cases hf : L.occurrence f = a <;> simp [colored,Mark.color,State.n,he,hf]
  · rfl

lemma color_Q (a : Fin o) (z : Fin r) : Q (L.colored a z) = Q (L.state z) := by
  apply Finset.sum_congr rfl
  intro i _
  exact Mark.color_f _ _ _
lemma color_P (a : Fin o) (z : Fin r) :
    P (L.next z) (L.colored a z) (L.line z) = P (L.next z) (L.state z) (L.line z) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [colored,state,Function.comp_apply,Mark.color_turn]
lemma color_B (a : Fin o) (z : Fin r) :
    B (L.next z) (L.colored a z) = B (L.next z) (L.state z) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [State.boundary,colored,state,Function.comp_apply,Mark.color_active]
  rfl

lemma state_full (z : Fin r) (h : ¬ L.isPartial z) : ∀ i, (L.state z i).active = true := by
  intro i
  have hi : L.mark z i ≠ .absent := fun hi => h ⟨i,hi⟩
  cases he : L.mark z i <;> simp_all [state,Mark.plain,State.active]

lemma boundary_le (z : Fin r) :
    B (L.next z) (L.state z) ≤ 4 * (if L.isPartial z then 1 else 0) := by
  split_ifs with hp
  · simpa using boundary_le_four (L.next z) (L.state z) (by simpa using L.card_le z)
  · rw [boundary_full _ _ (L.state_full z hp)]

lemma partial_le_boundary : 2 * L.partialCount ≤ L.boundary := by
  have h : ∀ z, 2 * (if L.isPartial z then 1 else 0) ≤ B (L.next z) (L.state z) := by
    intro z
    split_ifs with hp
    · obtain ⟨j,hj⟩ := hp
      obtain ⟨i,hi⟩ := L.represented z
      apply partial_boundary (L.next z) (L.cyclic z) (L.state z)
      · refine ⟨i,?_⟩
        cases he : L.mark z i <;> simp_all [state,Mark.plain,State.active]
      · exact ⟨j,by simp [state,hj,Mark.plain,State.active]⟩
    · simp
  simpa only [partialCount,boundary,Finset.mul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun z _ => h z)

lemma one_instance_bound (z : Fin r) :
    (4:ℝ) - 2 * T (L.state z) ≤ (Q (L.state z):ℝ) + P (L.next z) (L.state z) (L.line z) +
      4 * (if L.isPartial z then 1 else 0) := by
  by_cases hp : L.isPartial z
  · simp only [hp,ite_true,mul_one]
    have ht : (0:ℝ) ≤ T (L.state z) := Nat.cast_nonneg _
    have hq : (0:ℝ) ≤ Q (L.state z) := Nat.cast_nonneg _
    have hp : (0:ℝ) ≤ P (L.next z) (L.state z) (L.line z) := Nat.cast_nonneg _
    linarith
  · simp only [hp,ite_false,mul_zero,add_zero]
    obtain ⟨i,_⟩ := L.represented z
    let : Nonempty (Fin (L.n z)) := ⟨i⟩
    apply full_instance_bound (L.next z) (L.state z) (L.line z) (L.state_full z hp) (L.no_fixed z)
    · intro i hi
      apply L.bipartite z i
      cases he : L.mark z i <;> simp_all [state,Mark.plain]
    · intro i hi hj
      apply L.no_backtrack z i
      · cases he : L.mark z i <;> simp_all [state,Mark.plain]
      · cases he : L.mark z (L.next z i) <;> simp_all [state,Mark.plain]

lemma r_case_bound :
    (4:ℝ) * r - 2 * L.turns ≤ (L.triangles:ℝ) + L.payments + 4 * L.partialCount := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun z _ => L.one_instance_bound z)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have hj : (∑ z : Fin r, if L.isPartial z then (1:ℝ) else 0) = (L.partialCount : ℝ) := by
    simp [partialCount]
  simp only [hj] at h
  simpa [turns,triangles,payments,Nat.cast_sum,mul_comm] using h

lemma dominant_bound (a : Fin o) :
    2 * (∑ z, D (L.colored a z)) ≤ 2 * (∑ z, N (L.colored a z)) +
      L.triangles + L.payments + 4 * L.partialCount := by
  have h : ∀ z, 2 * D (L.colored a z) ≤ 2 * N (L.colored a z) + Q (L.state z) +
      P (L.next z) (L.state z) (L.line z) + 4 * (if L.isPartial z then 1 else 0) := by
    intro z
    have hc : ∀ i, ¬ (L.colored a z i = dominant ∧ L.colored a z (L.next z i) = dominant) := by
      intro i ⟨hi,hj⟩
      obtain ⟨f,hf,hfa⟩ : ∃ f, L.mark z i = .top f ∧ L.occurrence f = a := by
        cases he : L.mark z i <;> simp_all [colored,Mark.color]
      obtain ⟨g,hg,hga⟩ : ∃ g, L.mark z (L.next z i) = .top g ∧ L.occurrence g = a := by
        cases he : L.mark z (L.next z i) <;> simp_all [colored,Mark.color]
      exact L.no_same_side z i f g hf hg (hfa.trans hga.symm)
    have hb : ∀ i, L.colored a z i = triangle → L.line z i ≠ L.line z (L.next z i) := by
      intro i hi
      apply L.bipartite z i
      cases he : L.mark z i with
      | absent => simp_all [colored,Mark.color]
      | triangle => rfl
      | top f => by_cases hf : L.occurrence f = a <;> simp_all [colored,Mark.color]
    have hh := dominant_endpoint_bound (L.next z) (L.colored a z) (L.line z) hc hb
    rw [L.color_Q a z,L.color_P a z,L.color_B a z] at hh
    exact hh.trans (Nat.add_le_add_left (L.boundary_le z) _)
  simpa only [triangles,payments,partialCount,Finset.sum_add_distrib,← Finset.mul_sum]
    using Finset.sum_le_sum (s := Finset.univ) (fun z _ => h z)

/-- Full source per-fan apex inequality, including omission of the fan by some
selected top faces and shared dominant occurrences. It follows from the actual
cyclic-link/side conditions and the simple-polygon injection above. -/
theorem apex_bound :
    (L.turns:ℝ) + 2 * ((L.weight:ℝ) - S) ≤
      ((L.triangles:ℝ) + L.payments) / 2 + 2 * L.partialCount := by
  by_cases hm : L.maxMultiplicity ≤ r
  · have hw : L.weight = r := max_eq_left hm
    rw [hw]
    have ht : (L.turns:ℝ) ≤ S := by exact_mod_cast L.turns_le
    have hh := L.r_case_bound
    linarith
  · have hm' : r < L.maxMultiplicity := lt_of_not_ge hm
    have ho : 0 < o := by
      by_contra! ho
      have ho' : o = 0 := Nat.eq_zero_of_le_zero ho
      subst o
      simp [maxMultiplicity] at hm'
    have hne : (Finset.univ : Finset (Fin o)).Nonempty := ⟨⟨0,ho⟩,Finset.mem_univ _⟩
    obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup Finset.univ hne L.multiplicity
    have hw : L.weight = L.multiplicity a := (max_eq_right (le_of_lt hm')).trans ha
    rw [hw]
    have hn := L.other_count_le a
    have hmS := L.multiplicity_le a
    have hn' : ((∑ z, N (L.colored a z)):ℝ) ≤ (S:ℝ) - L.multiplicity a := by
      have hh : (((∑ z, N (L.colored a z)) + L.multiplicity a : ℕ):ℝ) ≤ S := by
        exact_mod_cast (show (∑ z, N (L.colored a z)) + L.multiplicity a ≤ S by omega)
      push_cast at hh
      linarith
    have hc : ((∑ z, D (L.colored a z)):ℝ) + (∑ z, N (L.colored a z)) = L.turns := by
      exact_mod_cast L.color_counts a
    have hd : 2 * ((∑ z, D (L.colored a z)):ℝ) ≤ 2 * ((∑ z, N (L.colored a z)):ℝ) +
        L.triangles + L.payments + 4 * L.partialCount := by exact_mod_cast L.dominant_bound a
    push_cast at hn' hc hd ⊢
    linarith

lemma triangles_le : L.triangles ≤ 5 * L.weight := by
  have h : ∀ z, Q (L.state z) ≤ 5 := by
    intro z
    calc
      _ ≤ ∑ _ : Fin (L.n z), 1 := by
        apply Finset.sum_le_sum
        intro i _
        cases L.state z i <;> decide
      _ = L.n z := by simp
      _ ≤ 5 := L.card_le z
  have hh : L.triangles ≤ 5*r := by
    simpa [triangles,mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun z _ => h z)
  exact hh.trans (Nat.mul_le_mul_left 5 (le_max_left _ _))

end FanData
end HyperbolicObstruction.FanLink
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteFanData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.FanLink
open Equiv

namespace IndexedFanData
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

def numberLink (_D : IndexedFanData I F O L) (z : Fin (Fintype.card I)) : ℕ := Fintype.card (L ((Fintype.equivFin I).symm z))

def linkEquiv (z : Fin (Fintype.card I)) :
    L ((Fintype.equivFin I).symm z) ≃ Fin (D.numberLink z) := Fintype.equivFin _

def nextFin (z : Fin (Fintype.card I)) : Equiv.Perm (Fin (D.numberLink z)) :=
  (D.linkEquiv z).permCongr (D.next ((Fintype.equivFin I).symm z))

lemma nextFin_symm (z : Fin (Fintype.card I)) (i : Fin (D.numberLink z)) :
    (D.linkEquiv z).symm (D.nextFin z i) =
      D.next ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i) := by
  simp [nextFin,Equiv.permCongr_apply]

lemma nextFin_cyclic (z : Fin (Fintype.card I)) : IsCyclic (D.nextFin z) := by
  intro i j
  obtain ⟨k,hk⟩ := D.cyclic ((Fintype.equivFin I).symm z)
    ((D.linkEquiv z).symm i) ((D.linkEquiv z).symm j)
  refine ⟨k,?_⟩
  have he : D.nextFin z ^ k = (D.linkEquiv z).permCongr
      (D.next ((Fintype.equivFin I).symm z) ^ k) :=
    (map_pow (D.linkEquiv z).permCongrHom _ _).symm
  rw [he,Equiv.permCongr_apply,hk,Equiv.apply_symm_apply]

def markFin (z : Fin (Fintype.card I)) (i : Fin (D.numberLink z)) : Mark (Fin (Fintype.card F)) :=
  Mark.map (Fintype.equivFin F) (D.mark ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i))

def decode : (Σ z, Fin (D.numberLink z)) → Σ z, L z := fun p =>
  ⟨(Fintype.equivFin I).symm p.1,(D.linkEquiv p.1).symm p.2⟩

lemma decode_injective : Function.Injective D.decode := by
  intro p q h
  have hz : p.1 = q.1 := (Fintype.equivFin I).symm.injective (congrArg Sigma.fst h)
  rcases p with ⟨z,i⟩; rcases q with ⟨y,j⟩
  dsimp at hz
  subst y
  have h' := Sigma.mk.inj h
  have hij : i = j := (D.linkEquiv z).symm.injective (eq_of_heq h'.2)
  subst j
  rfl

/-- Transport to the already proved finite-coordinate fan inequality. -/
def toFin : FanData (Fintype.card I) (Fintype.card F) (Fintype.card O) where
  n := D.numberLink
  next := D.nextFin
  cyclic := D.nextFin_cyclic
  mark := D.markFin
  line := fun z i => D.line ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i)
  occurrence := fun f => Fintype.equivFin O (D.occurrence ((Fintype.equivFin F).symm f))
  represented := by
    intro z
    obtain ⟨x,hx⟩ := D.represented ((Fintype.equivFin I).symm z)
    refine ⟨D.linkEquiv z x,?_⟩
    simpa only [markFin,ne_eq,Mark.map_absent,Equiv.symm_apply_apply] using hx
  card_le := fun z => D.card_le _
  no_fixed := by
    intro z i h
    have hh := congrArg (D.linkEquiv z).symm h
    rw [D.nextFin_symm] at hh
    exact D.no_fixed _ _ hh
  bipartite := by
    intro z i h
    simp only [markFin,Mark.map_triangle] at h
    simpa only [D.nextFin_symm] using D.bipartite _ _ h
  no_backtrack := by
    intro z i hi hj he
    simp only [markFin,Mark.map_triangle,D.nextFin_symm] at hi hj
    have hh := congrArg (D.linkEquiv z).symm he
    simp only [D.nextFin_symm] at hh
    exact D.no_backtrack _ _ hi hj hh
  no_same_side := by
    intro z i f g hf hg he
    simp only [markFin,Mark.map_top,D.nextFin_symm] at hf hg
    exact D.no_same_side _ _ _ _ hf hg ((Fintype.equivFin O).injective he)
  unique_turn := by
    intro p q f hp hq
    simp only [markFin,Mark.map_top] at hp hq
    exact D.decode_injective (D.unique_turn (D.decode p) (D.decode q) _ hp hq)

end IndexedFanData
end HyperbolicObstruction.FanLink
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFanCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink
attribute [local instance] Classical.propDecidable
namespace IndexedFanData
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

def triangles : ℕ := ∑ z, Q (D.state z)
def turns : ℕ := ∑ z, T (D.state z)
def boundary : ℕ := ∑ z, B (D.next z) (D.state z)

lemma sum_transport (g : (z : I) → L z → ℕ) :
    (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z),
      g ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i)) = ∑ z, ∑ i, g z i := by
  calc
    _ = ∑ z : Fin (Fintype.card I), ∑ i, g ((Fintype.equivFin I).symm z) i :=
      Finset.sum_congr rfl (fun z _ => Equiv.sum_comp (D.linkEquiv z).symm _)
    _ = _ := Equiv.sum_comp (Fintype.equivFin I).symm (fun z : I => ∑ i : L z, g z i)

lemma triangles_toFin : D.toFin.triangles = D.triangles := by
  change (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z), (D.markFin z i).plain.f) = _
  simp only [markFin,Mark.plain_map]
  exact D.sum_transport (fun z i => (D.state z i).f)
lemma turns_toFin : D.toFin.turns = D.turns := by
  change (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z), (D.markFin z i).plain.turn) = _
  simp only [markFin,Mark.plain_map]
  exact D.sum_transport (fun z i => (D.state z i).turn)
lemma payments_toFin : D.toFin.payments = D.payments := by
  change (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z), (D.markFin z i).plain.turn *
    (State.bit (!(D.line ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i))) +
     State.bit (!(D.line ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm (D.nextFin z i)))))) = _
  simp only [markFin,Mark.plain_map,D.nextFin_symm]
  exact D.sum_transport (fun z i => (D.state z i).turn *
    (State.bit (!(D.line z i)) + State.bit (!(D.line z (D.next z i)))))
lemma boundary_toFin : D.toFin.boundary = D.boundary := by
  change (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z),
    State.boundary (D.markFin z i).plain (D.markFin z (D.nextFin z i)).plain) = _
  simp only [markFin,Mark.plain_map,D.nextFin_symm]
  exact D.sum_transport (fun z i => State.boundary (D.state z i) (D.state z (D.next z i)))

lemma partial_toFin (z : Fin (Fintype.card I)) :
    D.toFin.isPartial z ↔ D.isPartial ((Fintype.equivFin I).symm z) := by
  simp only [FanData.isPartial,toFin,markFin,Mark.map_absent,isPartial]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨(D.linkEquiv z).symm i,hi⟩
  · rintro ⟨i,hi⟩; exact ⟨D.linkEquiv z i,by simpa only [Equiv.symm_apply_apply] using hi⟩
lemma partialCount_toFin : D.toFin.partialCount = D.partialCount := by
  simp only [FanData.partialCount,D.partial_toFin,partialCount]
  exact Equiv.sum_comp (Fintype.equivFin I).symm (fun z : I => if D.isPartial z then (1 : ℕ) else 0)
lemma multiplicity_toFin (a : Fin (Fintype.card O)) :
    D.toFin.multiplicity a = D.multiplicity ((Fintype.equivFin O).symm a) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (Fintype.equivFin F).symm
  intro f
  change Fintype.equivFin O (D.occurrence ((Fintype.equivFin F).symm f)) = a ↔ _
  exact (Equiv.eq_symm_apply _).symm
lemma maxMultiplicity_toFin : D.toFin.maxMultiplicity = D.maxMultiplicity := by
  change Finset.univ.sup (fun a => D.toFin.multiplicity a) = Finset.univ.sup D.multiplicity
  simp_rw [D.multiplicity_toFin]
  apply le_antisymm
  · apply Finset.sup_le
    intro a _
    exact Finset.le_sup (f := D.multiplicity) (Finset.mem_univ _)
  · apply Finset.sup_le
    intro a _
    have hh := Finset.le_sup (s := Finset.univ) (f := fun a => D.multiplicity ((Fintype.equivFin O).symm a))
      (Finset.mem_univ (Fintype.equivFin O a))
    simpa only [Equiv.symm_apply_apply] using hh
lemma weight_toFin : D.toFin.weight = D.weight := by
  simp only [FanData.weight,weight,D.maxMultiplicity_toFin]

/-- Coordinate-free apex estimate. -/
theorem apex_bound :
    (D.turns : ℝ) + 2 * ((D.weight : ℝ) - Fintype.card F) ≤
      ((D.triangles : ℝ) + D.payments) / 2 + 2 * D.partialCount := by
  simpa only [D.turns_toFin,D.weight_toFin,D.triangles_toFin,D.payments_toFin,D.partialCount_toFin]
    using D.toFin.apex_bound
lemma triangles_le : D.triangles ≤ 5 * D.weight := by
  simpa only [D.triangles_toFin,D.weight_toFin] using D.toFin.triangles_le
lemma partial_le_boundary : 2 * D.partialCount ≤ D.boundary := by
  simpa only [D.partialCount_toFin,D.boundary_toFin] using D.toFin.partial_le_boundary

end IndexedFanData
end HyperbolicObstruction.FanLink
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFanCards
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink.IndexedFanData
attribute [local instance] Classical.propDecidable
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

lemma turnIndex_card : Fintype.card D.TurnIndex = D.turns := by
  rw [show Fintype.card D.TurnIndex = _ from Fintype.card_subtype _]
  have hh := Finset.sum_boole (R := ℕ)
    (fun p : Σ z,L z => ∃ f, D.mark p.1 p.2 = Mark.top f) Finset.univ
  simp only [Nat.cast_id] at hh
  rw [← hh,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  cases he : D.mark z i <;> simp [he,state,Mark.plain,State.turn]

lemma triangleIndex_card : Fintype.card D.TriangleIndex = D.triangles := by
  rw [show Fintype.card D.TriangleIndex = _ from Fintype.card_subtype _]
  have hh := Finset.sum_boole (R := ℕ)
    (fun p : Σ z,L z => D.mark p.1 p.2 = Mark.triangle) Finset.univ
  simp only [Nat.cast_id] at hh
  rw [← hh,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  cases he : D.mark z i <;> simp [he,state,Mark.plain,State.f]

lemma boundaryIndex_card : Fintype.card D.BoundaryIndex = D.boundary := by
  rw [show Fintype.card D.BoundaryIndex = _ from Fintype.card_subtype _]
  have hh := Finset.sum_boole (R := ℕ)
    (fun p : Σ z,L z => (D.state p.1 p.2).active ≠ (D.state p.1 (D.next p.1 p.2)).active) Finset.univ
  simp only [Nat.cast_id] at hh
  rw [← hh,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (D.state z i).active = (D.state z (D.next z i)).active <;>
    simp [State.boundary,h]

section Family
variable {J : Type*} [Fintype J] {I F : J → Type*} {O : Type*}
  {L : (j : J) → I j → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (F j)]
  [Fintype O] [∀ j z, Fintype (L j z)]
  (D : (j : J) → IndexedFanData (I j) (F j) O (L j))
lemma family_turnIndex_card : Fintype.card (Σ j, (D j).TurnIndex) = ∑ j, (D j).turns := by
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => (D j).turnIndex_card)
lemma family_natTurnIndex_card : Nat.card (Σ j, (D j).TurnIndex) = ∑ j, (D j).turns := by
  rw [Nat.card_eq_fintype_card]
  exact family_turnIndex_card D
lemma family_natBoundaryIndex_card : Nat.card (Σ j, (D j).BoundaryIndex) = ∑ j, (D j).boundary := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => (D j).boundaryIndex_card)
lemma family_natTriangleIndex_card : Nat.card (Σ j, (D j).TriangleIndex) = ∑ j, (D j).triangles := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => (D j).triangleIndex_card)
end Family
end HyperbolicObstruction.FanLink.IndexedFanData
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FanActivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink.IndexedFanData
attribute [local instance] Classical.propDecidable
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

lemma multiplicity_le_card (a : O) : D.multiplicity a ≤ Fintype.card F := by
  exact Fintype.card_subtype_le _
lemma maxMultiplicity_le_card : D.maxMultiplicity ≤ Fintype.card F := by
  apply Finset.sup_le
  intro a _
  exact D.multiplicity_le_card a

/-- A positive-weight nominal fan is supported either by a selected top slot
or by a selected fan triangle. This includes slots omitted by a top boundary. -/
lemma activation_bound (h : 0 < D.weight) : 1 ≤ Fintype.card F + D.triangles := by
  by_cases hf : 0 < Fintype.card F
  · omega
  have hf0 : Fintype.card F = 0 := by omega
  have hm := D.maxMultiplicity_le_card
  have hi : 0 < Fintype.card I := by
    unfold weight at h
    omega
  obtain ⟨z⟩ := Fintype.card_pos_iff.mp hi
  obtain ⟨x,hx⟩ := D.represented z
  have hx' : D.mark z x = .triangle := by
    cases he : D.mark z x with
    | absent => exact False.elim (hx he)
    | triangle => rfl
    | top f => exact False.elim ((Fintype.card_eq_zero_iff.mp hf0).false f)
  have ht : 0 < Fintype.card D.TriangleIndex := Fintype.card_pos_iff.mpr ⟨⟨⟨z,x⟩,hx'⟩⟩
  rw [D.triangleIndex_card] at ht
  omega

end HyperbolicObstruction.FanLink.IndexedFanData
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedBoundaryPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D S : Type*} [DecidableEq D] [DecidableEq S]

/-- An indexed face map pulls back a complete target polygon to exactly one
source face, without any injectivity assumption on target letter labels. -/
theorem IndexedFaceMap.pullback_boundary {f : Perm D} {t : Perm S} {j : D → S}
    (h : IndexedFaceMap f t j) (a : D) {ys : List S}
    (ht : IsBoundary t ys) (ha : j a ∈ ys) :
    ∃ xs : List D, IsBoundary f xs ∧ a ∈ xs ∧ xs.map j = ys := by
  let p : D → Prop := fun x => f.SameCycle a x
  have hp : ∀ x, p (f x) ↔ p x := by
    intro x
    exact ⟨fun h => h.trans SameCycle.rfl.apply_right.symm,
      fun h => h.trans SameCycle.rfl.apply_right⟩
  let q := f.subtypePerm hp
  let jj : {x // p x} → S := fun x => j x.val
  have hj : Function.Injective jj := by
    intro x y he
    apply Subtype.ext
    exact h.injective (x.property.symm.trans y.property) he
  obtain ⟨zs,hzs,hzm⟩ := ht.pullback_surviving jj hj (by
    intro s hs
    obtain ⟨x,hx,he⟩ := h.orbit_surjective a (ht.sameCycle ha hs)
    exact ⟨⟨x,hx⟩,he⟩) (q := q) (by intro x _; exact h.commute x.val)
  refine ⟨zs.map Subtype.val,?_,?_,?_⟩
  · exact hzs.map Subtype.val Subtype.val_injective (fun _ => rfl)
  · have hm : j a ∈ zs.map jj := hzm.symm ▸ ha
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
    have hxa : x.val = a := h.injective x.property.symm he
    exact hxa ▸ List.mem_map_of_mem (f := Subtype.val) hx
  · simpa only [List.map_map,jj,Function.comp_def] using hzm

end HyperbolicObstruction.PictureSwitch
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RankCollection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences

/-- Each count is bounded separately. Thus every collection of at most M
occurrences is included, with all its retained fan slots. This harmless stronger
finite family needs no union over diagram copies or equality guesses. -/
abbrev BoundedShape (M : ℕ) := Σ s : Fin (M+1), Σ u : Fin (M+1),
  Σ q : Fin (M+1), Σ _ : Fin (M+1), Shape s u q

namespace BoundedShape
variable {M : ℕ} (b : BoundedShape M)
abbrev tops := b.1.val
abbrev fans := b.2.1.val
abbrev squares := b.2.2.1.val
abbrev sixes := b.2.2.2.1.val
abbrev shape : Shape b.tops b.fans b.squares := b.2.2.2.2

def Good {n : ℕ} (α β δ : ℝ) (w : Entry (SymmetricAlphabet n) → Bool) :=
  b.shape.Good (v := b.sixes) α β δ w
end BoundedShape

/-- The exact source diagram:rank conclusion at any fixed finite size. -/
def GoodUpTo (M : ℕ) {n : ℕ} (α β δ : ℝ) (w : Entry (SymmetricAlphabet n) → Bool) :=
  ∀ b : BoundedShape M, b.Good α β δ w

lemma GoodUpTo.rank_bound {M n s u q v : ℕ} {α β δ : ℝ}
    {w : Entry (SymmetricAlphabet n) → Bool} (h : GoodUpTo M α β δ w)
    (T : Shape s u q) (hs : s ≤ M) (hu : u ≤ M) (hq : q ≤ M) (hv : v ≤ M) :
    T.Good (v := v) α β δ w :=
  h ⟨⟨s,Nat.lt_succ_of_le hs⟩,⟨u,Nat.lt_succ_of_le hu⟩,
    ⟨q,Nat.lt_succ_of_le hq⟩,⟨v,Nat.lt_succ_of_le hv⟩,T⟩

end IncidenceTemplate.Occurrences
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RestrictOccurrence
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences.Shape

variable {s u q v : ℕ} (T : Shape s u q)

namespace Weights
variable {T}
variable (W : T.Weights (v := v))
local instance instDecidableEqPos : DecidableEq (T.Pos v) := Classical.typeDecidableEq _

abbrev TopAt (j : ℕ) := {a : Fin s // j < W.top a}
abbrev FanAt (j : ℕ) := {b : Fin u // j < W.fan b}
abbrev SquareAt (j : ℕ) := {e : Fin q // j < W.square e}
abbrev SixAt (j : ℕ) := {e : Fin v // j < W.six e}

abbrev topEnum (j : ℕ) := Fintype.equivFin (W.TopAt j)
abbrev fanEnum (j : ℕ) := Fintype.equivFin (W.FanAt j)
abbrev squareEnum (j : ℕ) := Fintype.equivFin (W.SquareAt j)
abbrev sixEnum (j : ℕ) := Fintype.equivFin (W.SixAt j)

abbrev topIndex (j : ℕ) (a : Fin (Fintype.card (W.TopAt j))) : Fin s := ((W.topEnum j).symm a).val
abbrev fanIndex (j : ℕ) (b : Fin (Fintype.card (W.FanAt j))) : Fin u := ((W.fanEnum j).symm b).val
abbrev squareIndex (j : ℕ) (e : Fin (Fintype.card (W.SquareAt j))) : Fin q := ((W.squareEnum j).symm e).val
abbrev sixIndex (j : ℕ) (e : Fin (Fintype.card (W.SixAt j))) : Fin v := ((W.sixEnum j).symm e).val

/-- The literal collection at level j; a retained top keeps every fan slot. -/
def atLevel (j : ℕ) : Shape (Fintype.card (W.TopAt j)) (Fintype.card (W.FanAt j))
    (Fintype.card (W.SquareAt j)) :=
  ⟨fun b => T.1 (W.fanIndex j b),
    (fun a i => ⟨W.fanEnum j ⟨(T.2.1 (W.topIndex j a) i).val,
      lt_of_lt_of_le ((W.topEnum j).symm a).property (W.slot _ i)⟩, by
        simp only [fanIndex,Equiv.symm_apply_apply]
        exact (T.2.1 (W.topIndex j a) i).property⟩),
    fun e => T.2.2 (W.squareIndex j e)⟩

/-- Positions and trials embed in the unchanged original arrays. -/
def embedPosition (j : ℕ) : (W.atLevel j).Pos (Fintype.card (W.SixAt j)) → T.Pos v
  | .inl a => .inl (W.topIndex j a)
  | .inr (.inl ⟨b,f⟩) => .inr (.inl ⟨W.fanIndex j b,f⟩)
  | .inr (.inr (.inl ⟨e,f⟩)) => .inr (.inr (.inl ⟨W.squareIndex j e,f⟩))
  | .inr (.inr (.inr (e,i))) => .inr (.inr (.inr (W.sixIndex j e,i)))

def embedTrial (j : ℕ) : Trial (Fintype.card (W.TopAt j)) (Fintype.card (W.FanAt j))
    (Fintype.card (W.SquareAt j)) (Fintype.card (W.SixAt j)) → Trial s u q v
  | .inl a => .inl (W.topIndex j a)
  | .inr (.inl b) => .inr (.inl (W.fanIndex j b))
  | .inr (.inr (.inl e)) => .inr (.inr (.inl (W.squareIndex j e)))
  | .inr (.inr (.inr e)) => .inr (.inr (.inr (W.sixIndex j e)))

lemma embedPosition_injective (j : ℕ) : Function.Injective (W.embedPosition j) := by
  intro x y h
  rcases x with a | (⟨b,f⟩ | (⟨e,f⟩ | ⟨e,i⟩)) <;>
    rcases y with a' | (⟨b',f'⟩ | (⟨e',f'⟩ | ⟨e',i'⟩)) <;>
    simp only [embedPosition,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h ⊢
  · exact (W.topEnum j).symm.injective (Subtype.ext h)
  · have hb : b = b' := (W.fanEnum j).symm.injective (Subtype.ext (congrArg Sigma.fst h))
    subst b'
    cases h
    rfl
  · have he : e = e' := (W.squareEnum j).symm.injective (Subtype.ext (congrArg Sigma.fst h))
    subst e'
    cases h
    rfl
  · obtain ⟨he,hi⟩ := Prod.mk.inj h
    exact Prod.ext ((W.sixEnum j).symm.injective (Subtype.ext he)) hi

lemma embedTrial_injective (j : ℕ) : Function.Injective (W.embedTrial j) := by
  intro x y h
  rcases x with a | (b | (e | e)) <;>
    rcases y with a' | (b' | (e' | e')) <;>
    simp only [embedTrial,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h ⊢
  · exact (W.topEnum j).symm.injective (Subtype.ext h)
  · exact (W.fanEnum j).symm.injective (Subtype.ext h)
  · exact (W.squareEnum j).symm.injective (Subtype.ext h)
  · exact (W.sixEnum j).symm.injective (Subtype.ext h)

lemma image_embedPosition (j : ℕ) : Finset.univ.image (W.embedPosition j) =
    Finset.univ.filter (fun p => j < W.position p) := by
  ext p
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter]
  constructor
  · rintro ⟨x,rfl⟩
    rcases x with a | (⟨b,f⟩ | (⟨e,f⟩ | ⟨e,i⟩))
    · exact ((W.topEnum j).symm a).property
    · exact ((W.fanEnum j).symm b).property
    · exact ((W.squareEnum j).symm e).property
    · exact ((W.sixEnum j).symm e).property
  · intro hp
    rcases p with a | (⟨b,f⟩ | (⟨e,f⟩ | ⟨e,i⟩))
    · exact ⟨.inl (W.topEnum j ⟨a,hp⟩),by simp only [embedPosition,topIndex,Equiv.symm_apply_apply]⟩
    · refine ⟨.inr (.inl ⟨W.fanEnum j ⟨b,hp⟩,⟨f.val,?_⟩⟩),?_⟩
      · simpa only [atLevel,fanIndex,Equiv.symm_apply_apply] using f.property
      · simp only [embedPosition,Sum.inr.injEq,Sum.inl.injEq]
        refine Sigma.ext ?_ ?_
        · exact congrArg Subtype.val ((W.fanEnum j).symm_apply_apply ⟨b,hp⟩)
        · refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
          · intro x; simp only [fanIndex,Equiv.symm_apply_apply]
          · rfl
    · refine ⟨.inr (.inr (.inl ⟨W.squareEnum j ⟨e,hp⟩,⟨f.val,?_⟩⟩)),?_⟩
      · simpa only [atLevel,squareIndex,Equiv.symm_apply_apply] using f.property
      · simp only [embedPosition,Sum.inr.injEq,Sum.inl.injEq]
        refine Sigma.ext ?_ ?_
        · exact congrArg Subtype.val ((W.squareEnum j).symm_apply_apply ⟨e,hp⟩)
        · refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
          · intro x; simp only [squareIndex,Equiv.symm_apply_apply]
          · rfl
    · exact ⟨.inr (.inr (.inr (W.sixEnum j ⟨e,hp⟩,i))),by simp only [embedPosition,sixIndex,Equiv.symm_apply_apply]⟩

lemma coreCoord_embed (j : ℕ) (a : Fin (Fintype.card (W.TopAt j))) (e : Edge) :
    W.embedPosition j ((W.atLevel j).coreCoord (v := Fintype.card (W.SixAt j)) a e) =
      T.coreCoord (v := v) (W.topIndex j a) e := by
  simp only [coreCoord]
  split_ifs <;> simp [embedPosition,atLevel,fanIndex]
  refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
  · intro f; simp only [Equiv.symm_apply_apply]
  · rfl

lemma row_embed {A : Type*} (j : ℕ) (σ : T.Pos v → A)
    (r : Trial (Fintype.card (W.TopAt j)) (Fintype.card (W.FanAt j))
    (Fintype.card (W.SquareAt j)) (Fintype.card (W.SixAt j))) :
    (W.atLevel j).row (σ ∘ W.embedPosition j) r = T.row σ (W.embedTrial j r) := by
  rcases r with a | (b | (e | e))
  · simp only [row,embedTrial]
    apply congrArg Sum.inl
    refine Sigma.ext ?_ ?_
    · rfl
    apply heq_of_eq
    funext f
    rcases f with ⟨f,hf⟩
    rcases f with e | x
    · simp only [Function.comp_apply,topCoord,coreCoord_embed]
    · simp [rowSupport] at hf
  · rfl
  · rfl
  · rfl

lemma rank_embed {n : ℕ} (j : ℕ) (σ : T.Pos v → SymmetricAlphabet n) :
    Coincidence.unsignedRank (σ ∘ W.embedPosition j) =
      Coincidence.rankOn (fun p => (σ p).1) (Finset.univ.filter (fun p => j < W.position p)) := by
  rw [← image_embedPosition]
  simp only [Coincidence.unsignedRank,Coincidence.rankOn,Coincidence.unsignedValues,
    Finset.card_image_of_injective _ (W.embedPosition_injective j),Finset.card_univ,
    Finset.image_image,Function.comp_def]

end Weights
end IncidenceTemplate.Occurrences.Shape
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WeightedRank
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences.Shape.Weights

variable {s u q v : ℕ} {T : Shape s u q} (W : T.Weights (v := v))

lemma positions_le {K : ℕ} (ht : ∀ a, W.top a ≤ K) (hf : ∀ b, W.fan b ≤ K)
    (hq : ∀ e, W.square e ≤ K) (hd : ∀ e, W.six e ≤ K) (p : T.Pos v) : W.position p ≤ K := by
  rcases p with a | (⟨b,f⟩ | (⟨e,f⟩ | ⟨e,i⟩))
  · exact ht a
  · exact hf b
  · exact hq e
  · exact hd e

end IncidenceTemplate.Occurrences.Shape.Weights
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalWeightedRank
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.IncidenceTemplate.Occurrences.Shape.Weights
attribute [local instance] Classical.propDecidable
variable {s u q v : ℕ} {T : Shape s u q} (W : T.Weights (v := v))
local instance instDecidableEqPos_2 : DecidableEq (T.Pos v) := Classical.typeDecidableEq _

/-- Only the occurrence collections retained at each positive weight level
need be small; the complete alphabet's array is not bounded by the fragment.
This is the literal layer application of source diagram:weighted-rank. -/
theorem rank_level_bound_local {M n : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w) (j : ℕ)
    (hs : Fintype.card (W.TopAt j) ≤ M) (hu : Fintype.card (W.FanAt j) ≤ M)
    (hq : Fintype.card (W.SquareAt j) ≤ M) (hv : Fintype.card (W.SixAt j) ≤ M)
    (σ : T.Pos v → SymmetricAlphabet n) (hi : Function.Injective (T.row σ))
    (hp : BernoulliCandidates.Present T.row w σ) :
    (Coincidence.rankOn (fun p => (σ p).1) (Finset.univ.filter (fun p => j < W.position p)) : ℝ) ≤
      ((3-β)-7*(2-α)) * Fintype.card (W.TopAt j) + (2-α) * Fintype.card (W.FanAt j) +
        (2-δ) * Fintype.card (W.SquareAt j) + (3-δ) * Fintype.card (W.SixAt j) := by
  rw [← W.rank_embed j σ]
  apply h.rank_bound (v := Fintype.card (W.SixAt j)) (W.atLevel j) hs hu hq hv
  · intro a b hab
    simp only [W.row_embed] at hab
    exact W.embedTrial_injective j (hi hab)
  · intro r
    rw [W.row_embed]
    exact hp _

theorem weighted_rank_bound_local {M n K : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w)
    (hs : ∀ j, Fintype.card (W.TopAt j) ≤ M) (hu : ∀ j, Fintype.card (W.FanAt j) ≤ M)
    (hq : ∀ j, Fintype.card (W.SquareAt j) ≤ M) (hv : ∀ j, Fintype.card (W.SixAt j) ≤ M)
    (σ : T.Pos v → SymmetricAlphabet n) (hi : Function.Injective (T.row σ))
    (hp : BernoulliCandidates.Present T.row w σ)
    (htK : ∀ a, W.top a ≤ K) (hfK : ∀ b, W.fan b ≤ K)
    (hqK : ∀ e, W.square e ≤ K) (hdK : ∀ e, W.six e ≤ K) :
    ((∑ j ∈ Finset.range K, Coincidence.rankOn (fun p => (σ p).1)
      (Finset.univ.filter (fun p => j < W.position p)) : ℕ) : ℝ) ≤
      ((3-β)-7*(2-α)) * (∑ a, (W.top a : ℝ)) + (2-α) * (∑ b, (W.fan b : ℝ)) +
        (2-δ) * (∑ e, (W.square e : ℝ)) + (3-δ) * (∑ e, (W.six e : ℝ)) := by
  push_cast
  have hh := Finset.sum_le_sum (s := Finset.range K)
    (fun j _ => W.rank_level_bound_local h j (hs j) (hu j) (hq j) (hv j) σ hi hp)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hh
  simpa only [TopAt,FanAt,SquareAt,SixAt,layer_card W.top K htK,layer_card W.fan K hfK,
    layer_card W.square K hqK,layer_card W.six K hdK] using hh

theorem contact_bound_local {M n K : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w)
    (hs : ∀ j, Fintype.card (W.TopAt j) ≤ M) (hu : ∀ j, Fintype.card (W.FanAt j) ≤ M)
    (hq : ∀ j, Fintype.card (W.SquareAt j) ≤ M) (hv : ∀ j, Fintype.card (W.SixAt j) ≤ M)
    (σ : T.Pos v → SymmetricAlphabet n) (hi : Function.Injective (T.row σ))
    (hp : BernoulliCandidates.Present T.row w σ)
    (htK : ∀ a, W.top a ≤ K) (hfK : ∀ b, W.fan b ≤ K)
    (hqK : ∀ e, W.square e ≤ K) (hdK : ∀ e, W.six e ≤ K)
    {E : Type*} [Fintype E] [DecidableEq E] (l r : E → T.Pos v)
    (hne : ∀ e, l e ≠ r e) (hc : ∀ e, (σ (l e)).1 = (σ (r e)).1)
    (hcap : ∀ p, (Finset.univ.filter (fun e => l e = p ∨ r e = p)).card ≤ W.position p) :
    (Fintype.card E : ℝ) ≤ ((3-β)-7*(2-α)) * (∑ a, (W.top a : ℝ)) +
      (2-α) * (∑ b, (W.fan b : ℝ)) + (2-δ) * (∑ e, (W.square e : ℝ)) +
      (3-δ) * (∑ e, (W.six e : ℝ)) := by
  have hh := Coincidence.contacts_le_weighted_rank (fun p => (σ p).1) W.position l r hne hc hcap K
    (W.positions_le htK hfK hqK hdK)
  exact (Nat.cast_le.mpr hh).trans (W.weighted_rank_bound_local h hs hu hq hv σ hi hp htK hfK hqK hdK)
end HyperbolicObstruction.IncidenceTemplate.Occurrences.Shape.Weights
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPayment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink.IndexedFanData
attribute [local instance] Classical.propDecidable
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

lemma paymentIndex_card : Fintype.card D.PaymentIndex = D.payments := by
  rw [show Fintype.card D.PaymentIndex = _ from Fintype.card_subtype _]
  have hh := Finset.sum_boole (R := ℕ) (fun p : (Σ z,L z) × Bool =>
    (∃ f, D.mark p.1.1 p.1.2 = Mark.top f) ∧
      D.line p.1.1 (if p.2 then p.1.2 else D.next p.1.1 p.1.2) = false) Finset.univ
  simp only [Nat.cast_id] at hh
  rw [← hh,Fintype.sum_prod_type,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  cases he : D.mark z i <;> cases hx : D.line z i <;> cases hy : D.line z (D.next z i) <;>
    simp [he, hx, hy, state, Mark.plain, State.turn,State.bit]

section Family
variable {J : Type*} [Fintype J] {I F : J → Type*} {O : Type*}
  {L : (j : J) → I j → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (F j)]
  [Fintype O] [∀ j z, Fintype (L j z)]
  (D : (j : J) → IndexedFanData (I j) (F j) O (L j))
lemma family_natPaymentIndex_card : Nat.card (Σ j, (D j).PaymentIndex) = ∑ j, (D j).payments := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => (D j).paymentIndex_card)
end Family
end HyperbolicObstruction.FanLink.IndexedFanData
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
variable (P : PictureMap X) (active : X → Prop) (part : X → I)

omit [DecidableEq X] in
/-- Exact relative boundary accounting, retaining loops and parallel contacts:
outside contacts occur once, contacts cut between interior parts twice. -/
theorem sum_relative_part_boundary :
    (∑ i, Fintype.card (RelativePartBoundary P active part i)) =
      Fintype.card (OutsideContact P active) +
        2 * Fintype.card (RelativeCutContact P active part) := by
  let raw : X → Prop := fun x => ¬ active x ∨ ¬ active (P.edge x) ∨ part x ≠ part (P.edge x)
  have hr : ∀ x, raw (P.edge x) ↔ raw x := by
    intro x
    dsimp only [raw]
    rw [P.edge_edge]
    tauto
  have h := P.boundary_contacts_eq active raw hr
  have hS : (∑ i, Fintype.card (RelativePartBoundary P active part i)) =
      Fintype.card (PictureMap.SelectedSide active raw) := by
    rw [← Fintype.card_sigma]
    apply Fintype.card_congr
    exact {
      toFun := fun p => ⟨p.2.val,by
        have hx := p.2.property
        dsimp only [raw]
        refine ⟨Or.inr ?_,hx.1⟩
        by_cases he : active (P.edge p.2.val)
        · right
          intro hp
          exact hx.2.2 ⟨he,hp.symm.trans hx.2.1⟩
        · exact Or.inl he⟩
      invFun := fun x => ⟨part x.val,x.val,x.property.2,rfl,by
        have hx := x.property
        dsimp only [raw] at hx
        tauto⟩
      left_inv := by rintro ⟨i,x,hx,hi,he⟩; cases hi; rfl
      right_inv := fun _ => rfl }
  have hB : Fintype.card (P.BoundarySide active raw) =
      Fintype.card (OutsideContact P active) := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    dsimp only [raw]
    tauto
  have hC : Fintype.card (P.Contact active raw) =
      Fintype.card (RelativeCutContact P active part) := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    dsimp only [raw]
    tauto
  simp only [← Nat.card_eq_fintype_card] at hS hB hC h ⊢
  rw [hS,← hB,← hC]
  exact h.symm

/-- Contacts from the interior to an enumerated outside are bounded by its
literal length. Outside-to-outside free boundary folds are NOT counted. -/
theorem outside_contacts_le_length (xs : List X)
    (ha : ∀ x, active x ↔ x ∉ xs) :
    Fintype.card (OutsideContact P active) ≤ xs.length := by
  let j : OutsideContact P active → {x : X // x ∈ xs} := fun x =>
    ⟨P.edge x.val,by
      have hh := x.property.2
      rw [ha] at hh
      exact Classical.not_not.mp hh⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    exact P.edge.injective (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective j hj
  have hc : Fintype.card {x : X // x ∈ xs} = xs.toFinset.card :=
    Fintype.card_of_subtype xs.toFinset (by intro x; exact List.mem_toFinset)
  rw [hc] at hh
  exact hh.trans (List.toFinset_card_le xs)

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroFaceFilling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A literal bounded free macro face has a cost at most thirty in the exact
finite simple-cycle presentation, via genuine core-graph routes. -/
theorem macro_boundary_filling (a : Top n w) (p : Perm D) (j : D → MacroGraph.graph.Dart)
    (hc : ∀ x, (j (p x)).fst = (j x).snd)
    (hi : Function.Injective (fun x => (j x).fst))
    (hb : ∀ x, p (p x) ≠ x)
    (xs : List D) (hx : IsBoundary p xs) (hne : xs ≠ []) :
    ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
      ((xs.map (fun x => macroStep n w a (j x).adj)).flatMap (collapse n w)) [] k := by
  obtain ⟨v,q,hq⟩ := hx.graph_closed_walk j (fun x _ => hc x) hne
  have hl : q.length ≤ 15 := by
    rw [← SimpleGraph.Walk.length_darts,hq,List.length_map]
    exact (List.Nodup.length_le_card hx.nodup).trans (macro_parametrization_card p j hc hi hb)
  let q' := GraphWordFilling.expand macroBase (fun {_ _} h => macroRoute h) q
  have hlen : q'.length ≤ 30 := by
    have h := GraphWordFilling.expand_length macroBase (fun {_ _} h => macroRoute h)
      2 (fun {_ _} h => macroRoute_length h) q
    exact h.trans (by omega)
  obtain ⟨k,hk,hh⟩ := GraphWordFilling.closed_filling
    (CoreWordGraph.label Finset.univ n (extendCore n a.val)) (CoreWordGraph.label_rev _ _ _)
    (SimpleWordRelator n w d)
    (fun v p h => SimpleWordRelator.top (extendCore n a.val) a.property.1 a.property.2 v p h) q'
  refine ⟨k,hk.trans hlen,?_⟩
  have hword : GraphWordFilling.word (CoreWordGraph.label Finset.univ n (extendCore n a.val)) q' =
      ((xs.map (fun x => macroStep n w a (j x).adj)).flatMap (collapse n w)) := by
    simp only [q',GraphWordFilling.expand_word,hq,List.flatMap_map]
    apply List.flatMap_congr
    intro x hx
    exact macroRoute_word n w a (j x).adj
  rwa [hword] at hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_OneFaceFilling
attribute [-instance] _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)}

/-- Base case of planar extraction, proved from the combinatorial Euler
definition: a genus-zero picture with no interior darts has a zero-area
word filling. It is NOT postulated as a property of a picture. -/
theorem one_face_filling {w : Word A} (P : WordPicture R w) (hall : ∀ x, x ∈ P.outside) :
    Homotopy R w [] 0 := by
  by_cases he : P.outside = []
  · have hw : w = [] := by rw [← P.word,he]; rfl
    subst w
    exact .refl _
  obtain ⟨x,hx⟩ := P.pairing.single_face_leaf P.genusZero P.boundary hall he
  obtain ⟨i,hi,z,hz⟩ := P.boundary.adjacent_rotate (hall (P.pairing.edge x))
    (P.pairing.edge_ne x) hx
  let Q := P.rotate i
  have hq : Q.outside = []++P.pairing.edge x::x::z := hz
  have hc : Q.label (P.pairing.edge x) = invLetter (Q.label x) := P.paired x
  have H := one_face_filling (w := _) (Q.foldAt hq hc)
    (Q.all_outside_fold hq hc (P.all_outside_rotate hall i))
  have hword : w.rotate i = Q.label (P.pairing.edge x) :: Q.label x :: z.map Q.label :=
    Q.word.symm.trans (congrArg (List.map Q.label) hq)
  have hf : Homotopy R (w.rotate i) (z.map P.label) 0 := by
    rw [hword]
    apply Homotopy.free
    have hh : FreeGroup.mk [Q.label (P.pairing.edge x),Q.label x] = 1 := by
      rw [hc]
      change FreeGroup.mk (FreeGroup.invRev [Q.label x] ++ [Q.label x]) = 1
      rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,inv_mul_cancel]
    change FreeGroup.mk ([Q.label (P.pairing.edge x),Q.label x] ++ z.map Q.label) = _
    rw [← FreeGroup.mul_mk,hh,one_mul]
    rfl
  have hfill : Homotopy R (w.rotate i) [] 0 := by
    simpa only [List.nil_append,Nat.zero_add] using hf.trans H
  apply Homotopy.unrotate_null i _ hfill
  have heq : P.outside.length = w.length := by simpa using congrArg List.length P.word
  omega
termination_by Fintype.card P.Dart
decreasing_by
  have hc := card_offPair (P.pairing.edge_ne x)
  change Fintype.card {y : P.Dart // OffPair (P.pairing.edge x) x y} < Fintype.card P.Dart
  omega

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_OutsideComponentFilling
attribute [-instance] _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
variable (P : WordPicture R w)

/-- Components with no relator face are trees in genus zero even when the
whole picture has unrelated closed components. -/
theorem isolated_outside_filling
    (hclosed : ∀ x ∈ P.outside, P.pairing.edge x ∈ P.outside) :
    Homotopy R w [] 0 := by
  let p : P.Dart → Prop := fun x => x ∈ P.outside
  have hf : ∀ x, p (P.pairing.face x) ↔ p x := by
    intro x
    constructor
    · intro hx
      exact P.boundary.mem_of_sameCycle hx (SameCycle.rfl.apply_right.symm)
    · exact P.boundary.invariant
  have he : ∀ x, p (P.pairing.edge x) ↔ p x := by
    intro x
    constructor
    · intro hx
      simpa only [P.pairing.edge_edge] using hclosed _ hx
    · exact hclosed x
  let Q : WordPicture R w := {
    Dart := {x // p x}
    finite := @Subtype.fintype P.Dart p (fun x => Classical.propDecidable (p x)) P.finite
    pairing := P.pairing.restrict p hf he
    genusZero := P.pairing.restrict_genusZero p P.genusZero hf he
    label := fun x => P.label x.val
    paired := fun x => P.paired x.val
    outside := P.outside.attachWith p (fun _ hx => hx)
    boundary := P.boundary.lift (fun _ hx => hx) _ (fun _ _ => rfl)
    word := by
      rw [List.attachWith_map_val]
      exact P.word
    interior := fun x hx => False.elim (hx ((List.mem_attachWith _ x).mpr x.property)) }
  apply Q.one_face_filling
  intro x
  change x ∈ P.outside.attachWith p (fun _ hx => hx)
  exact (List.mem_attachWith _ x).mpr x.property

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureFillingAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
variable {A : Type*} {R : Set (Word A)}
namespace SymmetricRelator
lemma filling {w : Word A} (h : SymmetricRelator R w) : Homotopy R w [] 1 := by
  rcases h with h | h
  · simpa using Homotopy.move (Move.face [] [] w h)
  · simpa using Homotopy.move (Move.reverseFace [] [] (FreeGroup.invRev w) h)
end SymmetricRelator
namespace Homotopy

/-- The paid step for peeling an actual adjacent relator: its first side is
paired to the first outside side. All other new boundary letters stay literal. -/
lemma peel {a b : A × Bool} {l r : Word A} {n : ℕ}
    (hp : b = invLetter a) (hr : Homotopy R (b::r) [] 1)
    (h : Homotopy R (r++l) [] n) : Homotopy R (a::l) [] (1+n) := by
  have h₁ : Homotopy R (a::l) (a::b::(r++l)) 1 := by
    simpa only [List.singleton_append,List.cons_append,List.nil_append] using
      (hr.contextual [a] l).symm
  have hf : FreeGroup.mk [a,b] = 1 := by
    rw [hp]
    change FreeGroup.mk ([a] ++ FreeGroup.invRev [a]) = 1
    rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,mul_inv_cancel]
  have h₂ : Homotopy R (a::b::(r++l)) (r++l) 0 := Homotopy.free (by
    change FreeGroup.mk ([a,b]++(r++l)) = _
    rw [← FreeGroup.mul_mk,hf,one_mul])
  simpa only [Nat.add_zero] using (h₁.trans h₂).trans h
end Homotopy
end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open HyperbolicObstruction.PictureSwitch HyperbolicObstruction.WordPictures Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C A V : Type*} [Fintype C] (B : PolygonTarget.Boundary C (A × Bool) V)
variable (hinv : B.rev = invLetter)

omit [Fintype C] in
include hinv in
/-- Both literal orientations of every included polygon are available as
one relator face; indexed positions are retained even for repeated labels. -/
lemma relator_boundary {R : Set (Word A)} (c : C) (hc : B.attachingWord c ∈ R)
    (b : Bool) (i : Fin (B.size c)) :
    ∃ ys : List B.Side, IsBoundary B.next ys ∧ (⟨c,b,i⟩ : B.Side) ∈ ys ∧
      SymmetricRelator R (ys.map B.sideLabel) := by
  cases b with
  | true =>
    refine ⟨B.positiveSides c,B.positiveSides_boundary c,?_,Or.inl ?_⟩
    · exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    · rwa [B.positiveSides_label]
  | false =>
    have hp := B.positiveSides_boundary c
    have hh : IsBoundary B.next ((B.positiveSides c).reverse.map B.opposite) := by
      apply hp.reverse.map B.opposite B.opposite.injective
      intro s
      simpa only [Perm.inv_def,Equiv.apply_symm_apply] using
        (congrArg B.next (B.reverse_next (B.next⁻¹ s))).symm
    refine ⟨(B.positiveSides c).reverse.map B.opposite,hh,?_,?_⟩
    · apply List.mem_map.mpr
      refine ⟨⟨c,true,i⟩,List.mem_reverse.mpr ?_,rfl⟩
      exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    · have he : ((B.positiveSides c).reverse.map B.opposite).map B.sideLabel =
          FreeGroup.invRev ((B.positiveSides c).map B.sideLabel) := by
        simp only [List.map_map,List.map_reverse,FreeGroup.invRev,Function.comp_def,
          B.edge_opposite,hinv,invLetter]
      rw [he,B.positiveSides_label]
      exact symmetricRelator_inv (Or.inl hc)

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_NormalFaceFilling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (exteriorWalkTarget n w d ell hell word closed c hc f))

/-- Local source03 cost for an ACTUAL free face in a protected normal disk.
Simplicity is read in the template, never in the random bouquet labels. -/
theorem exterior_top_filling (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart)
    (hx : P.index x = .inl (.inl (a,e))) :
    ∃ ys : List P.Dart, IsBoundary P.pairing.face ys ∧ x ∈ ys ∧
      ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
        ((ys.map ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index)).flatMap
          (collapse n w)) [] k := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let j : I → MacroGraph.graph.Dart := fun y =>
    (exterior_same_top n w d ell hell word closed c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (.inl (a,j y)) :=
    (exterior_same_top n w d ell hell word closed c hc f P hx y.property).choose_spec
  let q : Perm I := P.pairing.face.subtypePerm (fun _ => sameCycle_apply_right)
  have hfree (y : I) : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind (P.index y.val)) = true := by
    rw [hj]; rfl
  have hclose (y : I) : (j (q y)).fst = (j y).snd := by
    have h := P.closed y.val
    change (exteriorWalkTarget n w d ell hell word closed c hc f).front
      (P.index (q y).val) = (exteriorWalkTarget n w d ell hell word closed c hc f).back
        (P.index y.val) at h
    rw [hj,hj] at h
    exact congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj h))
  have hinj : Function.Injective (fun y : I => (j y).fst) := by
    intro i k hik
    apply Subtype.ext
    apply P.simple_front hs (hfree i) (i.property.symm.trans k.property)
    rw [hj,hj]
    exact congrArg Sum.inl (congrArg Sum.inl (Prod.ext rfl hik))
  have hnobig : ∀ y, q (q y) ≠ y := by
    intro y he
    exact hb y.val (hfree y) (congrArg Subtype.val he)
  obtain ⟨zs,hzs,hm⟩ := exists_boundary q (⟨x,SameCycle.rfl⟩ : I)
  obtain ⟨k,hk,hfill⟩ := macro_boundary_filling n w d a q j hclose hinj hnobig zs hzs
    (by intro he; rw [he] at hm; cases hm)
  refine ⟨zs.map Subtype.val,hzs.map Subtype.val Subtype.val_injective (fun _ => rfl),
    List.mem_map_of_mem hm,k,hk,?_⟩
  convert hfill using 1
  all_goals try with_reducible_and_instances rfl
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro y hy
  dsimp only [Function.comp_apply]
  rw [hj]
  rfl

/-- Frozen triangles and decorations retain the complete indexed attaching
polygon. Pulling that literal boundary back preserves its true local cost. -/
theorem exterior_frozen_filling
    (hm : P.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f))
    (x : P.Dart) (s : (frozenBoundary n w d).Side)
    (hx : P.index x = .inl (.inr s)) :
    ∃ ys : List P.Dart, IsBoundary P.pairing.face ys ∧ x ∈ ys ∧
      ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
        ((ys.map ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index)).flatMap
          (collapse n w)) [] k := by
  obtain ⟨ys,hys,hmem,hrel⟩ := (frozenBoundary n w d).relator_boundary rfl s.1
    (R := Set.range (frozenBoundary n w d).attachingWord) ⟨s.1,rfl⟩ s.2.1 s.2.2
  have hlocal : ∀ r ∈ Set.range (frozenBoundary n w d).attachingWord,
      ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
        (r.flatMap (collapse n w)) [] k := by
    rintro r ⟨z,rfl⟩
    exact cell_collapse_filling n w d (frozenCell n w d z)
  obtain ⟨k,hk,hfill⟩ := hrel.filling.substitute (collapse n w)
    (fun e => collapse_rev n w e) hlocal
  have hxF : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind (P.index x)) = false := by
    rw [hx]; rfl
  let j : (frozenBoundary n w d).Side →
      WalkStep n w d ⊕ (walkTarget n w d c hc f).ExteriorSide ell hell word closed :=
    fun z => .inl (.inr z)
  have hj : Function.Injective j := Sum.inl_injective.comp Sum.inr_injective
  have hys' : IsBoundary (exteriorWalkFrozen n w d ell hell word closed c hc f).next
      (ys.map j) := hys.map j hj (fun _ => rfl)
  obtain ⟨zs,hzs,hzm,hmap⟩ := hm.pullback_boundary (⟨x,hxF⟩ : P.FrozenDart) hys'
    (by change P.index x ∈ ys.map j; rw [hx]; exact List.mem_map_of_mem hmem)
  have hlabel : (zs.map Subtype.val).map
        ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index) =
      ys.map (frozenBoundary n w d).sideLabel := by
    have hh := congrArg
      (List.map (exteriorWalkTarget n w d ell hell word closed c hc f).label) hmap
    simp only [List.map_map] at hh ⊢
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply List.map_congr_left
    intro z hz
    rfl
  refine ⟨zs.map Subtype.val,hzs.map Subtype.val Subtype.val_injective (fun _ => rfl),
    List.mem_map_of_mem hzm,k,by simpa using hk,?_⟩
  rw [hlabel]
  exact hfill

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_NormalDiskArea
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm WordPictures
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (exteriorWalkTarget n w d ell hell word closed c hc f))
variable (hm : P.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f))
  (hs : P.Simple) (hb : P.NoBigon)
variable (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
  (hw : xs.map ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index) =
    List.ofFn word)
  (ht : ∀ x, (walkTarget n w d c hc f).isExterior ell hell word closed (P.index x) ↔ x ∈ xs)

/-- A normalized actual cone disk defines a word picture whose every interior
face has a proved cost30 replacement. The protected exterior is EXCLUDED. -/
def normalWordPicture : WordPicture (BoundedConeRelator n w d) (List.ofFn word) where
  Dart := P.Dart
  pairing := P.pairing
  genusZero := P.genusZero
  label := (exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index
  paired := P.paired
  outside := xs
  boundary := hx
  word := hw
  interior := by
    intro x hxo
    cases hi : P.index x with
    | inl s =>
      cases s with
      | inl s =>
        obtain ⟨ys,hys,hym,hfill⟩ := exterior_top_filling n w d ell hell word closed c hc f P hs hb
          x s.1 s.2 hi
        exact ⟨ys,hys,hym,Or.inl hfill⟩
      | inr s =>
        obtain ⟨ys,hys,hym,hfill⟩ := exterior_frozen_filling n w d ell hell word closed c hc f P hm x s hi
        exact ⟨ys,hys,hym,Or.inl hfill⟩
    | inr s =>
      have he : (walkTarget n w d c hc f).isExterior ell hell word closed (P.index x) := by
        rw [hi]; trivial
      exact False.elim (hxo ((ht x).mp he))

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeRadialBoundary
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

lemma walk_apex_paired (x : P.Dart) (hx : walkApex n w d ell hell word c hc f P x = true) :
    walkApex n w d ell hell word c hc f P (P.pairing.edge x) = false := by
  change isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.edge x)))) = false
  have he : (target n w d ell hell word c hc f).label (P.index (P.pairing.edge x)) = rev n w ((target n w d ell hell word c hc f).label (P.index x)) := P.paired x
  rw [he]
  exact radial n w _ hx
lemma walk_apex_radial (x : P.Dart) (hx : walkApex n w d ell hell word c hc f P x = true) :
    walkRadial n w d ell hell word c hc f P x := by
  change isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true at hx
  change isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = false
  generalize hh : (target n w d ell hell word c hc f).label (P.index x) = l at *
  rcases l with ⟨e,o⟩
  cases e with
  | inl a => cases hx
  | inr e => rfl
lemma walk_radial_paired (x : P.Dart) :
    walkRadial n w d ell hell word c hc f P (P.pairing.edge x) ↔ walkRadial n w d ell hell word c hc f P x := by
  unfold walkRadial
  have he : (target n w d ell hell word c hc f).label (P.index (P.pairing.edge x)) = rev n w ((target n w d ell hell word c hc f).label (P.index x)) := P.paired x
  rw [he]
  rfl

lemma walk_transitions_le_boundary : Fintype.card
    (P.pairing.VertexTransition (walkApex n w d ell hell word c hc f P) (walkSelected n w d ell hell word c hc f P select)) ≤
    Fintype.card (RadialBoundarySide n w d ell hell word c hc f P select) := by
  apply P.pairing.vertex_transitions_le_boundary
  · intro x; exact congrArg select (P.faceClass_apply x)
  · exact walk_apex_previous n w d ell hell word c hc f P
  · exact walk_apex_paired n w d ell hell word c hc f P
  · exact walk_apex_radial n w d ell hell word c hc f P
  · exact walk_radial_paired n w d ell hell word c hc f P

lemma fragment_active (b : Fan n w) (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val) :
    (fragmentMark n w d ell hell word c hc f P select b z x).plain.active = select (P.faceClass x.val) := by
  unfold fragmentMark
  split_ifs with hs ht <;> simp_all [FanLink.Mark.plain,FanLink.State.active]

variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

def boundaryTransition (p : AllBoundaryIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    P.pairing.VertexTransition (walkApex n w d ell hell word c hc f P) (walkSelected n w d ell hell word c hc f P select) := by
  refine ⟨p.2.val.2.val,instance_apex n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2,?_⟩
  have hh := p.2.property
  change (fragmentMark n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2).plain.active ≠
    (fragmentMark n w d ell hell word c hc f P select p.1 p.2.val.1 (P.linkNext p.2.val.1.val p.2.val.2)).plain.active at hh
  rw [fragment_active,fragment_active] at hh
  exact hh

lemma boundaryTransition_injective : Function.Injective
    (boundaryTransition n w d ell hell word c hc f P select hs hm hred hrad) := by
  intro p q h
  have hh : (⟨p.1,p.2.val⟩ : Σ b : Fan n w, Σ z : ApexInstance n w d ell hell word c hc f P select b, P.Link z.val) =
      ⟨q.1,q.2.val⟩ := apexCorner_injective n w d ell hell word c hc f P select (congrArg Subtype.val h)
  rcases p with ⟨b,x⟩; rcases q with ⟨a,y⟩
  have hb : b = a := congrArg Sigma.fst hh
  subst a
  have hv : x.val = y.val := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))

lemma allBoundaryIndex_card : Fintype.card (AllBoundaryIndex n w d ell hell word c hc f P select hs hm hred hrad) =
    ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).boundary := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natBoundaryIndex_card
    (fun b => indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad)

/-- The partial-apex error is paid by actual radial boundary sides. No
radial-side accounting identity is supplied as an extra hypothesis. -/
theorem actual_radial_sides :
    (∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).boundary) ≤
      Fintype.card (RadialBoundarySide n w d ell hell word c hc f P select) := by
  rw [← allBoundaryIndex_card n w d ell hell word c hc f P select hs hm hred hrad]
  exact (Fintype.card_le_of_injective _
    (boundaryTransition_injective n w d ell hell word c hc f P select hs hm hred hrad)).trans
    (walk_transitions_le_boundary n w d ell hell word c hc f P select)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeMacroPolygon
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

/-- The actual simple macro polygon carried by one free source face. Its
vertices are the original TEMPLATE vertices in their original cyclic order,
not the possibly identified letter-bouquet vertices. This supplies the finite
macro-cycle perimeter/three-fan bounds from the produced normal picture. -/
noncomputable def mappedMacroPolygon (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart) (hx : P.index x = .inl (.inl (a,e))) :
    MacroGraph.Polygon := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let j : I → MacroGraph.graph.Dart := fun y =>
    (exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (.inl (a,j y)) :=
    (exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx y.property).choose_spec
  let q : Perm I := P.pairing.face.subtypePerm (fun _ => sameCycle_apply_right)
  let b : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfree (y : I) : (target n w d ell hell word c hc f).free
      ((target n w d ell hell word c hc f).kind (P.index y.val)) = true := by
    rw [hj]; rfl
  have hclose (y : I) : (j (q y)).fst = (j y).snd := by
    have h := P.closed y.val
    change (target n w d ell hell word c hc f).front (P.index (q y).val) = (target n w d ell hell word c hc f).back (P.index y.val) at h
    rw [hj,hj] at h
    exact congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj h))
  exact {
    n := Fintype.card I
    vertex := fun i => (j (b i)).fst
    next := b.trans (q.trans b.symm)
    injective := by
      intro i k hik
      apply b.injective
      apply Subtype.ext
      apply P.simple_front hs (hfree (b i)) ((b i).property.symm.trans (b k).property)
      rw [hj,hj]
      exact congrArg Sum.inl (congrArg Sum.inl (Prod.ext rfl hik))
    adjacent := by
      intro i
      change MacroGraph.Adjacent (j (b i)).fst (j (b (b.symm (q (b i))))).fst
      rw [b.apply_symm_apply,hclose]
      exact (j (b i)).adj
    no_backtrack := by
      intro i hi
      have hv := congrArg (fun k => (b k).val) hi
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply] at hv
      exact hb (b i).val (hfree (b i)) hv }

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeSlots
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

def faceOccurrence (F : SelectedTopFace n w d ell hell word c hc f P select) : Top n w := F.property.2.choose
lemma faceOccurrence_kind (F : SelectedTopFace n w d ell hell word c hc f P select) :
    P.faceKind F.val = .inl (.inl (faceOccurrence n w d ell hell word c hc f P select F)) := F.property.2.choose_spec

def topSlot (F : SelectedTopFace n w d ell hell word c hc f P select) (i : Fin 7) :
    Σ b : Fan n w, SelectedTop n w d ell hell word c hc f P select b :=
  ⟨slot n w (faceOccurrence n w d ell hell word c hc f P select F) i,
    F.val,F.property.1,faceOccurrence n w d ell hell word c hc f P select F,
    faceOccurrence_kind n w d ell hell word c hc f P select F,i,rfl⟩

lemma topSlot_injective : Function.Injective
    (fun p : SelectedTopFace n w d ell hell word c hc f P select × Fin 7 => topSlot n w d ell hell word c hc f P select p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : Σ b : Fan n w, SelectedTop n w d ell hell word c hc f P select b => z.2.val) h
  · exact congrArg (fun z : Σ b : Fan n w, SelectedTop n w d ell hell word c hc f P select b => z.1.val.1) h

lemma topSlot_surjective : Function.Surjective
    (fun p : SelectedTopFace n w d ell hell word c hc f P select × Fin 7 => topSlot n w d ell hell word c hc f P select p.1 p.2) := by
  rintro ⟨b,F⟩
  obtain ⟨a,ha,i,hi⟩ := F.property.2
  let H : SelectedTopFace n w d ell hell word c hc f P select := ⟨F.val,F.property.1,a,ha⟩
  have hocc : faceOccurrence n w d ell hell word c hc f P select H = a :=
    Sum.inl.inj (Sum.inl.inj ((faceOccurrence_kind n w d ell hell word c hc f P select H).symm.trans ha))
  have hslot : slot n w (faceOccurrence n w d ell hell word c hc f P select H) i = b := by rw [hocc,hi]
  refine ⟨(H,i),?_⟩
  apply Sigma.ext hslot
  apply (Subtype.heq_iff_coe_eq (fun z => by change (select z = true ∧ ∃ a, P.faceKind z = .inl (.inl a) ∧ ∃ j, slot n w a j = slot n w (faceOccurrence n w d ell hell word c hc f P select H) i) ↔ _; rw [hslot])).mpr
  rfl

/-- Each selected top polygon contributes all seven indexed fan slots,
including the fan slots its simple boundary omits. -/
theorem fragment_slots_eq :
    (∑ b : Fan n w, Fintype.card (SelectedTop n w d ell hell word c hc f P select b)) =
      7 * Fintype.card (SelectedTopFace n w d ell hell word c hc f P select) := by
  rw [← Fintype.card_sigma]
  have h := Fintype.card_congr (Equiv.ofBijective _
    ⟨topSlot_injective n w d ell hell word c hc f P select,topSlot_surjective n w d ell hell word c hc f P select⟩)
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using h.symm

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeTopTurns
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

/-- Actual source-face cardinal bound, not an assumed macro polygon. -/
lemma top_face_apex_card_ge (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart) (hx : P.index x = .inl (.inl (a,e))) :
    3 ≤ Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y ∧
      isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index y))) = true} := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let R := mappedMacroPolygon n w d ell hell word c hc f P hs hb x a e hx
  let b : Fin R.n ≃ I := (Fintype.equivFin I).symm
  let j (y : I) : MacroGraph.graph.Dart := (exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (.inl (a,j y)) :=
    (exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx y.property).choose_spec
  have hv (i : Fin R.n) : R.vertex i = (j (b i)).fst := rfl
  let : Nonempty I := ⟨⟨x,SameCycle.rfl⟩⟩
  have hn : 0 < R.n := Fintype.card_pos
  have hp := R.points_ge hn
  have hex (p : {p : Fin 7 // p ∈ R.points}) : ∃ i : Fin R.n, R.vertex i = MacroGraph.point p.val := by
    have hmem : MacroGraph.point p.val ∈ R.vertices := (Finset.mem_filter.mp p.property).2
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hmem
    exact ⟨i,hi⟩
  let choose (p : {p : Fin 7 // p ∈ R.points}) : Fin R.n := (hex p).choose
  have hchoose (p : {p : Fin 7 // p ∈ R.points}) : (j (b (choose p))).fst = MacroGraph.point p.val := by
    exact (hv _).symm.trans (hex p).choose_spec
  let g : {p : Fin 7 // p ∈ R.points} → {y : P.Dart // P.pairing.face.SameCycle x y ∧
      isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index y))) = true} := fun p =>
    ⟨(b (choose p)).val,(b (choose p)).property,by
      rw [hj]
      change isApex n w (start n w (macroStep n w a (show MacroGraph.Adjacent _ _ from (j (b (choose p))).adj))) = true
      rw [macroStep_start,hchoose]
      rfl⟩
  have hg : Function.Injective g := by
    intro p q he
    have hh := congrArg Subtype.val he
    change (b (choose p)).val = (b (choose q)).val at hh
    have hb : b (choose p) = b (choose q) := Subtype.ext hh
    have hpp : MacroGraph.point p.val = MacroGraph.point q.val :=
      (hchoose p).symm.trans ((congrArg (fun y => (j y).fst) hb).trans (hchoose q))
    exact Subtype.ext (Sum.inl.inj (Sum.inl.inj hpp))
  have hcard := Fintype.card_le_of_injective g hg
  exact hp.trans (by simpa only [Fintype.card_coe] using hcard)

variable (select : P.Face → Bool)
noncomputable instance instFintypeTopTurnDart : Fintype (TopTurnDart n w d ell hell word c hc f P select) := Fintype.ofFinite _

noncomputable instance instFintypeFaceApexDart (F : SelectedTopFace n w d ell hell word c hc f P select) :
    Fintype (FaceApexDart n w d ell hell word c hc f P select F) := Fintype.ofFinite _

lemma face_apex_card_ge (hs : P.Simple) (hb : P.NoBigon)
    (F : SelectedTopFace n w d ell hell word c hc f P select) :
    3 ≤ Fintype.card (FaceApexDart n w d ell hell word c hc f P select F) := by
  obtain ⟨a,ha⟩ := F.property.2
  have hk : (target n w d ell hell word c hc f).kind (P.index F.val.out) = .inl (.inl a) := by
    change P.faceKind (P.faceClass F.val.out) = _
    rw [P.faceClass_out]; exact ha
  obtain ⟨e,he⟩ : ∃ e, P.index F.val.out = .inl (.inl (a,e)) := by
    cases ht : P.index F.val.out with
    | inl s =>
      cases s with
      | inl s =>
        rw [ht] at hk
        exact ⟨s.2,congrArg Sum.inl (congrArg Sum.inl (Prod.ext (Sum.inl.inj (Sum.inl.inj hk)) rfl))⟩
      | inr s => rw [ht] at hk; cases hk
    | inr s => rw [ht] at hk; cases hk

  have h := top_face_apex_card_ge n w d ell hell word c hc f P hs hb F.val.out a e he
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [← P.faceClass_eq,P.faceClass_out]
  exact and_congr eq_comm Iff.rfl

/-- Source `sum d_z >= 3 T` at the actual selected top faces. The following
apex transport identifies these darts with the indexed fan-turn counts. -/
lemma selected_top_turns_ge (hs : P.Simple) (hb : P.NoBigon) :
    3 * Fintype.card (SelectedTopFace n w d ell hell word c hc f P select) ≤
      Fintype.card (TopTurnDart n w d ell hell word c hc f P select) := by
  let I := Σ F : SelectedTopFace n w d ell hell word c hc f P select, FaceApexDart n w d ell hell word c hc f P select F
  let g : I → TopTurnDart n w d ell hell word c hc f P select := fun p => ⟨p.2.val,by
    refine ⟨?_,p.2.property.2,?_⟩
    · rw [p.2.property.1]; exact p.1.property.1
    · have hk : (target n w d ell hell word c hc f).kind (P.index p.2.val) = .inl (.inl (faceOccurrence n w d ell hell word c hc f P select p.1)) := by
        change P.faceKind (P.faceClass p.2.val) = _
        rw [p.2.property.1]; exact faceOccurrence_kind n w d ell hell word c hc f P select p.1
      rw [hk]; rfl⟩
  have hg : Function.Injective g := by
    rintro ⟨F,x⟩ ⟨G,y⟩ h
    have hv : x.val = y.val := congrArg Subtype.val h
    have hf : F = G := Subtype.ext (x.property.1.symm.trans ((congrArg P.faceClass hv).trans y.property.1))
    subst G
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun F _ => face_apex_card_ge n w d ell hell word c hc f P select hs hb F)
  have hh' : 3 * Fintype.card (SelectedTopFace n w d ell hell word c hc f P select) ≤ Fintype.card I := by
    rw [Fintype.card_sigma]
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm] using hh
  exact hh'.trans (Fintype.card_le_of_injective g hg)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeTurnTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

def allTurnDart (p : AllTurnIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    TopTurnDart n w d ell hell word c hc f P select := by
  refine ⟨p.2.val.2.val,?_,instance_apex n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2,?_⟩
  · by_contra hh
    have he := (mark_absent n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2).mpr hh
    obtain ⟨F,hF⟩ := p.2.property
    change fragmentMark n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2 = .top F at hF
    rw [he] at hF
    cases hF
  · obtain ⟨F,hF⟩ := p.2.property
    obtain ⟨e,he⟩ := mark_top_index n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2 F hF
    rw [he]; rfl

lemma allTurnDart_surjective : Function.Surjective
    (allTurnDart n w d ell hell word c hc f P select hs hm hred hrad) := by
  intro x
  obtain ⟨b,hb⟩ : ∃ b, start n w ((target n w d ell hell word c hc f).label (P.index x.val)) = .inr b := by
    cases he : start n w ((target n w d ell hell word c hc f).label (P.index x.val)) with
    | inl a => have hh := x.property.2.1; rw [he] at hh; cases hh
    | inr b => exact ⟨b,rfl⟩
  let z := apexInstanceAt n w d ell hell word c hc f P select b x.val x.property.1 hb
  let y : P.Link z.val := ⟨x.val,rfl⟩
  have ht : ∃ a e, P.index x.val = .inl (.inl (a,e)) := by
    cases he : P.index x.val with
    | inl s =>
      cases s with
      | inl s => exact ⟨s.1,s.2,rfl⟩
      | inr s => have hh := x.property.2.2; rw [he] at hh; cases hh
    | inr s => have hh := x.property.2.2; rw [he] at hh; cases hh

  have hmark : ∃ F, fragmentMark n w d ell hell word c hc f P select b z y = .top F := by
    unfold fragmentMark
    exact ⟨_,by rw [dite_eq_left x.property.1,dite_eq_left ht]⟩
  exact ⟨⟨b,⟨⟨z,y⟩,hmark⟩⟩,Subtype.ext rfl⟩

lemma allTurnIndex_card :
    Fintype.card (AllTurnIndex n w d ell hell word c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).turns := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natTurnIndex_card
    (fun b => indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad)

/-- All selected top apex darts are really fan turns. Together with the
actual macro cycle bound this supplies the source `sum d_z >= 3T`. -/
theorem actual_turns_ge (hb : P.NoBigon) :
    3 * Fintype.card (SelectedTopFace n w d ell hell word c hc f P select) ≤
      ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).turns := by
  have h1 := selected_top_turns_ge n w d ell hell word c hc f P select hs hb
  have h2 := Fintype.card_le_of_surjective _
    (allTurnDart_surjective n w d ell hell word c hc f P select hs hm hred hrad)
  exact h1.trans (h2.trans_eq (allTurnIndex_card n w d ell hell word c hc f P select hs hm hred hrad))

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeApexAggregate
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

/-- The summed apex estimate is now a theorem about the actual selected
mixed-picture faces. All nominal slots, turns, partial links and radial
boundary sides are extracted from the picture itself. -/
theorem actual_nominal_apex (hb : P.NoBigon) :
    3 * (Fintype.card (SelectedTopFace n w d ell hell word c hc f P select) : ℝ) +
      2 * ((∑ b : Fan n w, ((indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).weight : ℝ)) -
        7 * Fintype.card (SelectedTopFace n w d ell hell word c hc f P select)) ≤
    ((∑ b : Fan n w, ((indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).triangles : ℝ)) +
      ∑ b : Fan n w, ((indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).payments : ℝ))/2 +
      2 * ∑ b : Fan n w, ((indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).partialCount : ℝ) := by
  have ha := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).apex_bound)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum] at ha
  have ht : 3 * (Fintype.card (SelectedTopFace n w d ell hell word c hc f P select) : ℝ) ≤
      ∑ b : Fan n w, ((indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).turns : ℝ) := by
    exact_mod_cast actual_turns_ge n w d ell hell word c hc f P select hs hm hred hrad hb
  have hslot : (∑ b : Fan n w, (Fintype.card (SelectedTop n w d ell hell word c hc f P select b) : ℝ)) =
      7 * Fintype.card (SelectedTopFace n w d ell hell word c hc f P select) := by
    exact_mod_cast fragment_slots_eq n w d ell hell word c hc f P select
  rw [hslot] at ha
  linarith

lemma actual_triangles_le :
    (∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).triangles) ≤
      5 * ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).weight := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).triangles_le)
  simpa only [← Finset.mul_sum] using h

lemma actual_partial_le :
    2 * (∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).partialCount) ≤
      Fintype.card (RadialBoundarySide n w d ell hell word c hc f P select) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).partial_le_boundary)
  have h' : 2 * (∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).partialCount) ≤
      ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).boundary := by
    simpa only [← Finset.mul_sum] using h
  exact h'.trans (actual_radial_sides n w d ell hell word c hc f P select hs hm hred hrad)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeRawPosition
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma contact_position_different (hred : P.FullyReduced) {x : P.Dart}
    {p : RawPosition n w d}
    (hx : isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true)
    (hpx : stepPosition n w d ell hell word c hc f (P.index x) = some p)
    (hpy : stepPosition n w d ell hell word c hc f (P.index (P.pairing.edge x)) = some p) : False := by
  obtain ⟨s,hxs,hps⟩ := stepPosition_some n w d ell hell word c hc f P hpx
  obtain ⟨t,hyt,hpt⟩ := stepPosition_some n w d ell hell word c hc f P hpy
  have he := P.paired x
  rw [hxs,hyt] at he
  change walkLabel n w d t = rev n w (walkLabel n w d s) at he
  rw [hxs] at hx
  have ht : isLetter n w (walkLabel n w d t) = true := by rw [he]; exact hx
  have hp := raw_position_reverse n w d hx ht (hps.trans hpt.symm) he
  apply hred x
  rw [hxs,hyt,hp]
  rfl

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeContact
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

variable (hsel : InteriorSelection n w d ell hell word c hc f P select)

lemma selectedPosition_value (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x)
    (hr : rawDart n w d ell hell word c hc f P x) :
    ((target n w d ell hell word c hc f).label (P.index x)).1 =
      .inl ((occurrenceValues n w d (rawToPosition n w d
        (selectedPosition n w d ell hell word c hc f P select hsel x hx))).1) := by
  have hi := selectedStep_index n w d ell hell word c hc f P select hsel x hx
  change isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true at hr
  rw [hi] at hr ⊢
  exact raw_label_value n w d _ hr

lemma actual_contact_ne (hred : P.FullyReduced) (e : ActualContact n w d ell hell word c hc f P select) :
    contactLeft n w d ell hell word c hc f P select hsel e ≠
      contactRight n w d ell hell word c hc f P select hsel e := by
  intro h
  have hp := (rawToPosition_injective n w d) h
  have hl := selectedPosition_eq n w d ell hell word c hc f P select hsel e.val e.property.2.1
  have hr := selectedPosition_eq n w d ell hell word c hc f P select hsel
    (P.pairing.edge e.val) e.property.2.2.1
  rw [← hp] at hr
  exact contact_position_different n w d ell hell word c hc f P hred e.property.1 hl hr

lemma actual_contact_value (e : ActualContact n w d ell hell word c hc f P select) :
    (occurrenceValues n w d (contactLeft n w d ell hell word c hc f P select hsel e)).1 =
      (occurrenceValues n w d (contactRight n w d ell hell word c hc f P select hsel e)).1 := by
  have hl := selectedPosition_value n w d ell hell word c hc f P select hsel
    e.val e.property.2.1 e.property.1
  have hr := selectedPosition_value n w d ell hell word c hc f P select hsel
    (P.pairing.edge e.val) e.property.2.2.1
    ((rawDart_pair n w d ell hell word c hc f P e.val).mpr e.property.1)
  have he := congrArg Prod.fst (P.paired e.val)
  exact (Sum.inl.inj (hr.symm.trans (he.trans hl))).symm

variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_contact_capacity (hb : P.NoBigon) (p : (occurrenceShape n w).Pos (Fintype.card (Six n d))) :
    (Finset.univ.filter (fun e : ActualContact n w d ell hell word c hc f P select =>
      contactLeft n w d ell hell word c hc f P select hsel e = p ∨
      contactRight n w d ell hell word c hc f P select hsel e = p)).card ≤
      (actualWeights n w d ell hell word c hc f P select hs hm hred hrad).position p := by
  obtain ⟨r,rfl⟩ := rawToPosition_surjective n w d p
  have heq (e : ActualContact n w d ell hell word c hc f P select) :
      (contactLeft n w d ell hell word c hc f P select hsel e = rawToPosition n w d r ∨
      contactRight n w d ell hell word c hc f P select hsel e = rawToPosition n w d r) ↔
      (stepPosition n w d ell hell word c hc f (P.index e.val) = some r ∨
      stepPosition n w d ell hell word c hc f (P.index (P.pairing.edge e.val)) = some r) := by
    rw [selectedPosition_eq n w d ell hell word c hc f P select hsel e.val e.property.2.1,
      selectedPosition_eq n w d ell hell word c hc f P select hsel (P.pairing.edge e.val) e.property.2.2.1]
    simp only [contactLeft,contactRight,(rawToPosition_injective n w d).eq_iff,Option.some.injEq]
  simp_rw [heq]
  rw [← Fintype.card_subtype]
  have hh := P.pairing.contact_capacity (selectedDart n w d ell hell word c hc f P select)
    (rawDart n w d ell hell word c hc f P) (rawDart_pair n w d ell hell word c hc f P)
    (fun x => stepPosition n w d ell hell word c hc f (P.index x)) (some r)
  have hcard : Fintype.card (PictureMap.PositionSide (selectedDart n w d ell hell word c hc f P select)
      (rawDart n w d ell hell word c hc f P)
      (fun x => stepPosition n w d ell hell word c hc f (P.index x)) (some r)) =
      Fintype.card (RawPositionSide n w d ell hell word c hc f P select r) := by
    apply Fintype.card_congr
    exact { toFun := fun x => ⟨x.val.val,x.val.property.2,x.val.property.1,x.property⟩
            invFun := fun x => ⟨⟨x.val,x.property.2.1,x.property.1⟩,x.property.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  simp only [← Nat.card_eq_fintype_card] at hcard hh
  rw [hcard] at hh
  have hp := actual_position_capacity n w d ell hell word c hc f P select hs hm hred hrad hb r
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [← Nat.card_eq_fintype_card] using hh.trans hp

include hsel in
/-- The contact-counting estimate for the literal normalized mixed picture.
Only the stochastic rank event and layer-size bounds remain here; no side
capacity, radial accounting, or label-incidence premise is assumed. -/
theorem actual_contact_bound {M : ℕ} {α β δ : ℝ}
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (ht : ∀ j, Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).TopAt j) ≤ M)
    (hf : ∀ j, Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).FanAt j) ≤ M)
    (hq : ∀ j, Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).SquareAt j) ≤ M)
    (hv : ∀ j, Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).SixAt j) ≤ M) :
    let W := actualWeights n w d ell hell word c hc f P select hs hm hred hrad
    (Fintype.card (ActualContact n w d ell hell word c hc f P select) : ℝ) ≤
      ((3-β)-7*(2-α)) * (∑ a, (W.top a : ℝ)) + (2-α) * (∑ b, (W.fan b : ℝ)) +
      (2-δ) * (∑ q, (W.square q : ℝ)) + (3-δ) * (∑ q, (W.six q : ℝ)) := by
  let W := actualWeights n w d ell hell word c hc f P select hs hm hred hrad
  let K := Finset.univ.sup W.top + Finset.univ.sup W.fan + Finset.univ.sup W.square + Finset.univ.sup W.six
  have htK (a) : W.top a ≤ K := by
    have h := Finset.le_sup (f := W.top) (Finset.mem_univ a)
    dsimp [K]; omega
  have hfK (b) : W.fan b ≤ K := by
    have h := Finset.le_sup (f := W.fan) (Finset.mem_univ b)
    dsimp [K]; omega
  have hqK (q) : W.square q ≤ K := by
    have h := Finset.le_sup (f := W.square) (Finset.mem_univ q)
    dsimp [K]; omega
  have hvK (q) : W.six q ≤ K := by
    have h := Finset.le_sup (f := W.six) (Finset.mem_univ q)
    dsimp [K]; omega
  exact W.contact_bound_local hgood ht hf hq hv (occurrenceValues n w d)
    (occurrence_row_injective n w d) (occurrence_present n w d) htK hfK hqK hvK
    (contactLeft n w d ell hell word c hc f P select hsel) (contactRight n w d ell hell word c hc f P select hsel)
    (actual_contact_ne n w d ell hell word c hc f P select hsel hred) (actual_contact_value n w d ell hell word c hc f P select hsel)
    (by
      intro p
      convert actual_contact_capacity n w d ell hell word c hc f P select hsel hs hm hred hrad hb p using 1
      all_goals try with_reducible_and_instances rfl
      exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _))

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeTriangleTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma allTriangleIndex_card :
    Fintype.card (AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).triangles := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natTriangleIndex_card
    (fun b => indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad)

def triangleFace (p : AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    SelectedTriangleFace n w d ell hell word c hc f P select := by
  refine ⟨P.faceClass (triangleCorner n w d ell hell word c hc f P select hs hm hred hrad p),
    triangle_selected n w d ell hell word c hc f P select hs hm hred hrad p,?_⟩
  obtain ⟨g,o,hx⟩ := mark_triangle_corner n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2 p.2.property
  refine ⟨g,?_⟩
  change (target n w d ell hell word c hc f).kind (P.index p.2.val.2.val) = _
  rw [hx]
  rfl

lemma triangleFace_surjective : Function.Surjective
    (triangleFace n w d ell hell word c hc f P select hs hm hred hrad) := by
  intro F
  obtain ⟨g,hg⟩ := F.property.2
  have ho := P.faceClass_out F.val
  have hg' : (target n w d ell hell word c hc f).kind (P.index F.val.out) = .inl (.inr (.inl g)) := by
    change P.faceKind (P.faceClass F.val.out) = _
    rw [ho]
    exact hg
  obtain ⟨o,i,hi⟩ : ∃ (o : Bool) (i : Fin 3), P.index F.val.out = .inl (.inr ⟨.inl g,o,i⟩) := by
    cases h : P.index F.val.out with
    | inl s =>
      cases s with
      | inl x => rw [h] at hg'; cases hg'
      | inr s =>
        rcases s with ⟨k,o,i⟩
        rw [h] at hg'
        have hk : k = .inl g := Sum.inr.inj (Sum.inl.inj hg')
        subst k
        exact ⟨o,i,rfl⟩
    | inr s => rw [h] at hg'; cases hg'

  obtain ⟨y,hy,he⟩ := frozen_side_exists n w d ell hell word c hc f P hm hi (if o then (0 : Fin 3) else (2 : Fin 3))
  have hface : P.faceClass y = F.val := ((P.faceClass_eq).mpr hy).symm.trans ho
  have hsel : select (P.faceClass y) = true := by rw [hface]; exact F.property.1
  have hstart : start n w ((target n w d ell hell word c hc f).label (P.index y)) = .inr g.1 := by
    change P.index y = .inl (frozenCorner n w d g o) at he
    rw [he,corner_label]
    cases o <;> rfl
  let z := apexInstanceAt n w d ell hell word c hc f P select g.1 y hsel hstart
  let x : P.Link z.val := ⟨y,rfl⟩
  have hnot : ¬∃ a e, P.index y = .inl (.inl (a,e)) := by rw [he]; simp
  have hmark : fragmentMark n w d ell hell word c hc f P select g.1 z x = .triangle := by
    unfold fragmentMark
    rw [dite_eq_left hsel,dite_eq_right hnot]
  refine ⟨⟨g.1,⟨⟨z,x⟩,hmark⟩⟩,?_⟩
  exact Subtype.ext hface

lemma triangleFace_injective (hb : P.NoBigon) : Function.Injective
    (triangleFace n w d ell hell word c hc f P select hs hm hred hrad) := by
  intro p q he
  apply triangleRawDart_injective n w d ell hell word c hc f P select hs hm hred hrad
  have hface := congrArg Subtype.val he
  change P.faceClass p.2.val.2.val = P.faceClass q.2.val.2.val at hface
  have hf : P.faceClass (triangleRawDart n w d ell hell word c hc f P select hs hm hred hrad p) =
      P.faceClass (triangleRawDart n w d ell hell word c hc f P select hs hm hred hrad q) := by
    simpa only [triangleRawDart,P.faceClass_apply] using hface
  obtain ⟨g,o,hp⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad p
  obtain ⟨g',o',hq⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad q
  have hk := congrArg P.faceKind hf
  change (target n w d ell hell word c hc f).kind (P.index (triangleRawDart n w d ell hell word c hc f P select hs hm hred hrad p)) =
    (target n w d ell hell word c hc f).kind (P.index (triangleRawDart n w d ell hell word c hc f P select hs hm hred hrad q)) at hk
  rw [hp,hq] at hk
  have hg : g = g' := Sum.inl.inj (Sum.inr.inj (Sum.inl.inj hk))
  apply raw_position_once_per_face n w d ell hell word c hc f P hs hb hm
    (p := .inr (.inl g)) (P.faceClass_eq.mp hf)
  · rw [hp]; cases o <;> rfl
  · rw [hq]; cases o' <;> rfl
  · rw [hp]; rfl
  · rw [hq,hg]; rfl

lemma selectedTriangles_eq (hb : P.NoBigon) :
    Fintype.card (SelectedTriangleFace n w d ell hell word c hc f P select) =
      ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).triangles := by
  rw [← allTriangleIndex_card n w d ell hell word c hc f P select hs hm hred hrad]
  exact (Fintype.card_congr (Equiv.ofBijective _
    ⟨triangleFace_injective n w d ell hell word c hc f P select hs hm hred hrad hb,
     triangleFace_surjective n w d ell hell word c hc f P select hs hm hred hrad⟩)).symm

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeFaceCounts
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_weights_top : (∑ a, (actualWeights n w d ell hell word c hc f P select hs hm hred hrad).top a) =
    actualTopCount n w d ell hell word c hc f P select := by
  change (∑ a, Fintype.card (KindFace n w d ell hell word c hc f P select (.inl ((enumTop n w).symm a)))) = _
  exact (Equiv.sum_comp (enumTop n w).symm (fun a => Fintype.card (KindFace n w d ell hell word c hc f P select (.inl a)))).trans
    (sum_top_count n w d ell hell word c hc f P select)
lemma actual_weights_square : (∑ q, (actualWeights n w d ell hell word c hc f P select hs hm hred hrad).square q) =
    actualSquareCount n w d ell hell word c hc f P select := by
  exact Equiv.sum_comp (enumSquare n w).symm (fun q => Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inl q)))))
lemma actual_weights_six : (∑ q, (actualWeights n w d ell hell word c hc f P select hs hm hred hrad).six q) =
    actualSixCount n w d ell hell word c hc f P select := by
  exact Equiv.sum_comp (enumSix n d).symm (fun q => Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inr q)))))
lemma actual_weights_fan : (∑ b, (actualWeights n w d ell hell word c hc f P select hs hm hred hrad).fan b) =
    ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).weight := by
  exact Equiv.sum_comp (enumFan n w).symm (fun b => (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).weight)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeLayers
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_top_layer (j : ℕ) :
    Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).TopAt j) ≤
      actualTopCount n w d ell hell word c hc f P select := by
  rw [← actual_weights_top n w d ell hell word c hc f P select hs hm hred hrad]
  exact card_layer_le_support _ _ j (fun _ h => h)
lemma actual_square_layer (j : ℕ) :
    Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).SquareAt j) ≤
      actualSquareCount n w d ell hell word c hc f P select := by
  rw [← actual_weights_square n w d ell hell word c hc f P select hs hm hred hrad]
  exact card_layer_le_support _ _ j (fun _ h => h)
lemma actual_six_layer (j : ℕ) :
    Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).SixAt j) ≤
      actualSixCount n w d ell hell word c hc f P select := by
  rw [← actual_weights_six n w d ell hell word c hc f P select hs hm hred hrad]
  exact card_layer_le_support _ _ j (fun _ h => h)

lemma actual_fan_layer (hb : P.NoBigon) (j : ℕ) :
    Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).FanAt j) ≤
      7 * actualTopCount n w d ell hell word c hc f P select + actualTriangleCount n w d ell hell word c hc f P select := by
  let D := fun b => indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad
  have hh := card_layer_le_support (fun b => (actualWeights n w d ell hell word c hc f P select hs hm hred hrad).fan b)
    (fun b => Fintype.card (SelectedTop n w d ell hell word c hc f P select ((enumFan n w).symm b)) +
      (D ((enumFan n w).symm b)).triangles) j
        (fun fan hactive => (D ((enumFan n w).symm fan)).activation_bound hactive)
  have he := Equiv.sum_comp (enumFan n w).symm (fun b =>
    Fintype.card (SelectedTop n w d ell hell word c hc f P select b) + (D b).triangles)
  rw [he,Finset.sum_add_distrib] at hh
  have hslot : (∑ b : Fan n w, Fintype.card (SelectedTop n w d ell hell word c hc f P select b)) =
      7 * actualTopCount n w d ell hell word c hc f P select := by
    have h0 := fragment_slots_eq n w d ell hell word c hc f P select
    simp only [actualTopCount,← Nat.card_eq_fintype_card] at h0 ⊢
    convert h0 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext face
    simp
  rw [hslot] at hh
  have ht : actualTriangleCount n w d ell hell word c hc f P select = ∑ b, (D b).triangles := by
    have h0 := selectedTriangles_eq n w d ell hell word c hc f P select hs hm hred hrad hb
    simp only [actualTriangleCount,← Nat.card_eq_fintype_card] at h0 ⊢
    convert h0 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext face
    simp
  rw [← ht] at hh
  exact hh

lemma actual_layer_bounds (hsel : InteriorSelection n w d ell hell word c hc f P select) {M : ℕ} (hb : P.NoBigon) (hM : 8 * actualArea n w d ell hell word c hc f P select ≤ M) (j : ℕ) :
    let W := actualWeights n w d ell hell word c hc f P select hs hm hred hrad
    Fintype.card (W.TopAt j) ≤ M ∧ Fintype.card (W.FanAt j) ≤ M ∧
      Fintype.card (W.SquareAt j) ≤ M ∧ Fintype.card (W.SixAt j) ≤ M := by
  have ht := actual_top_layer n w d ell hell word c hc f P select hs hm hred hrad j
  have hf := actual_fan_layer n w d ell hell word c hc f P select hs hm hred hrad hb j
  have hq := actual_square_layer n w d ell hell word c hc f P select hs hm hred hrad j
  have hv := actual_six_layer n w d ell hell word c hc f P select hs hm hred hrad j
  rw [actual_area_eq n w d ell hell word c hc f P select hsel] at hM
  dsimp only
  omega

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativePayment
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

variable (hs : P.Simple) (hb : P.NoBigon)
  (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma allPaymentIndex_card :
    Fintype.card (AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).payments := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natPaymentIndex_card
    (fun b => indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeRawCount
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_raw_account_le (hb : P.NoBigon) :
    Fintype.card (RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad) ≤
      Fintype.card (ActualRawSide n w d ell hell word c hc f P select) := by
  let g : RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad → ActualRawSide n w d ell hell word c hc f P select :=
    fun p => ⟨accountDart n w d ell hell word c hc f P select hs hm hred hrad p,
      accountDart_raw n w d ell hell word c hc f P select hs hm hred hrad hb p,
      accountDart_selected n w d ell hell word c hc f P select hs hm hred hrad p⟩
  exact Fintype.card_le_of_injective g (fun _ _ hh =>
    accountDart_injective n w d ell hell word c hc f P select hs hm hred hrad hb (congrArg Subtype.val hh))

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeRawAccount
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma decorationSideIndex_card :
    Fintype.card (DecorationSideIndex n w d ell hell word c hc f P select) =
      4 * actualSquareCount n w d ell hell word c hc f P select + 6 * actualSixCount n w d ell hell word c hc f P select := by
  rw [Fintype.card_sigma,Fintype.sum_sum_type]
  simp only [Fintype.card_prod,Fintype.card_fin]
  change (∑ q : Square n w, Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inl q)))) * 4) +
    (∑ q : Six n d, Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inr q)))) * 6) = _
  rw [← Finset.sum_mul,← Finset.sum_mul]
  change actualSquareCount n w d ell hell word c hc f P select * 4 + actualSixCount n w d ell hell word c hc f P select * 6 = _
  omega

lemma actual_raw_lower (hb : P.NoBigon) :
    (∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).payments) +
      actualTriangleCount n w d ell hell word c hc f P select + 4 * actualSquareCount n w d ell hell word c hc f P select +
      6 * actualSixCount n w d ell hell word c hc f P select ≤ Fintype.card (ActualRawSide n w d ell hell word c hc f P select) := by
  have hh := actual_raw_account_le n w d ell hell word c hc f P select hs hm hred hrad hb
  change Fintype.card (AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad ⊕
    (AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad ⊕ DecorationSideIndex n w d ell hell word c hc f P select)) ≤ _ at hh
  rw [Fintype.card_sum,Fintype.card_sum] at hh
  have hp : Fintype.card (AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).payments := by
    have h0 := allPaymentIndex_card n w d ell hell word c hc f P select hs hm hred hrad
    simp only [← Nat.card_eq_fintype_card] at h0 ⊢
    convert h0 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext index
    simp
  have ht : Fintype.card (AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad) =
      actualTriangleCount n w d ell hell word c hc f P select := by
    have h0 := (allTriangleIndex_card n w d ell hell word c hc f P select hs hm hred hrad).trans
      (selectedTriangles_eq n w d ell hell word c hc f P select hs hm hred hrad hb).symm
    simpa only [actualTriangleCount,← Nat.card_eq_fintype_card] using h0
  rw [hp,ht,decorationSideIndex_card n w d ell hell word c hc f P select] at hh
  omega

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeFragment
attribute [-instance] _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate.Occurrences.Shape
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hsel : InteriorSelection n w d ell hell word c hc f P select)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

include hsel in
lemma actual_contacts_le {M : ℕ} {α β δ : ℝ}
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (hM : 8 * actualArea n w d ell hell word c hc f P select ≤ M) :
    (Fintype.card (ActualContact n w d ell hell word c hc f P select) : ℝ) ≤
      ((3-β)-7*(2-α)) * actualTopCount n w d ell hell word c hc f P select +
      (2-α) * actualFanWeight n w d ell hell word c hc f P select hs hm hred hrad +
      (2-δ) * actualSquareCount n w d ell hell word c hc f P select +
      (3-δ) * actualSixCount n w d ell hell word c hc f P select := by
  have hl := actual_layer_bounds n w d ell hell word c hc f P select hs hm hred hrad hsel hb hM
  have hh := actual_contact_bound n w d ell hell word c hc f P select hsel hs hm hred hrad hgood hb
    (fun j => (hl j).1) (fun j => (hl j).2.1) (fun j => (hl j).2.2.1) (fun j => (hl j).2.2.2)
  dsimp only at hh
  have ht : (∑ a, ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).top a : ℝ)) =
      actualTopCount n w d ell hell word c hc f P select := by
    exact_mod_cast actual_weights_top n w d ell hell word c hc f P select hs hm hred hrad
  have hf : (∑ b, ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).fan b : ℝ)) =
      actualFanWeight n w d ell hell word c hc f P select hs hm hred hrad := by
    exact_mod_cast actual_weights_fan n w d ell hell word c hc f P select hs hm hred hrad
  have hq : (∑ q, ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).square q : ℝ)) =
      actualSquareCount n w d ell hell word c hc f P select := by
    exact_mod_cast actual_weights_square n w d ell hell word c hc f P select hs hm hred hrad
  have hv : (∑ q, ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).six q : ℝ)) =
      actualSixCount n w d ell hell word c hc f P select := by
    exact_mod_cast actual_weights_six n w d ell hell word c hc f P select hs hm hred hrad
  rwa [ht,hf,hq,hv] at hh

include hs hm hred hrad hsel in
/-- The full fragment estimate for the literal normalized mixed
picture, for any selected interior faces, with boundary contacts to the protected exterior counted. All counts, weights, normal fan links,
indexed coincidences and size bounds are produced, not assumed. -/
theorem actual_fragment_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (hM : 8 * actualArea n w d ell hell word c hc f P select ≤ M) :
    defectConstant α β δ * actualArea n w d ell hell word c hc f P select ≤
      actualBoundary n w d ell hell word c hc f P select := by
  have hI := actual_contacts_le n w d ell hell word c hc f P select hsel hs hm hred hrad hgood hb hM
  have hA := actual_nominal_apex n w d ell hell word c hc f P select hs hm hred hrad hb
  have hQ := actual_triangles_le n w d ell hell word c hc f P select hs hm hred hrad
  have hJ := actual_partial_le n w d ell hell word c hc f P select hs hm hred hrad
  have hR := actual_raw_lower n w d ell hell word c hc f P select hs hm hred hrad hb
  have hC := actual_boundary_contacts_eq n w d ell hell word c hc f P select
  rw [← hC] at hR
  have hT := selectedTriangles_eq n w d ell hell word c hc f P select hs hm hred hrad hb
  have hu : @Finset.univ (Fan n w) (Subtype.fintype _) =
      @Finset.univ (Fan n w) inferInstance := by ext x; simp
  try simp only [hu] at hA hQ hJ hT
  have hA' : 3*(actualTopCount n w d ell hell word c hc f P select : ℝ) +
      2*((actualFanWeight n w d ell hell word c hc f P select hs hm hred hrad : ℝ)-7*actualTopCount n w d ell hell word c hc f P select) ≤
      ((actualTriangleCount n w d ell hell word c hc f P select : ℝ)+actualPayments n w d ell hell word c hc f P select hs hm hred hrad)/2 +
      2*actualPartialCount n w d ell hell word c hc f P select hs hm hred hrad := by
    have ht' : (∑ b : Fan n w, ((indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).triangles : ℝ)) =
        actualTriangleCount n w d ell hell word c hc f P select := by
      have ht0 : (∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).triangles) =
          actualTriangleCount n w d ell hell word c hc f P select := by
        simpa only [actualTriangleCount,← Nat.card_eq_fintype_card] using hT.symm
      exact_mod_cast ht0
    simpa only [actualTopCount,actualFanWeight,actualPayments,actualPartialCount,Nat.cast_sum,ht',← Nat.card_eq_fintype_card] using hA
  have hQ' : actualTriangleCount n w d ell hell word c hc f P select ≤
      5 * actualFanWeight n w d ell hell word c hc f P select hs hm hred hrad := by
    change Fintype.card (SelectedTriangleFace n w d ell hell word c hc f P select) ≤ _
    rw [hT]
    simpa only [actualFanWeight] using hQ
  change 2 * actualPartialCount n w d ell hell word c hc f P select hs hm hred hrad ≤ _ at hJ
  rw [actual_area_eq n w d ell hell word c hc f P select hsel]
  exact fragment_numeric_bound ha _ _ _ _ _ _ _ _ _ _ hI hA' hQ' hJ hR

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativePartitionEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk

open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open scoped BigOperators
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

instance instFintypeInteriorFace : Fintype (InteriorFace n w d ell hell word c hc f P) := Fintype.ofFinite _

lemma interior_iff (x : P.Dart) : Interior n w d ell hell word c hc f P (P.faceClass x) ↔
    ¬ (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
      (letterWordClosed n w ell word) (P.index x) := by
  change (∃ k, (target n w d ell hell word c hc f).kind (P.index x) = .inl k) ↔ _
  cases hi : P.index x with
  | inl s =>
    change (∃ k, (Sum.inl (walkKind n w d s) : WalkKind n w d ⊕ Unit) = .inl k) ↔ ¬ False
    exact ⟨fun _ => not_false,fun _ => ⟨_,rfl⟩⟩
  | inr s =>
    change (∃ k, (Sum.inr () : WalkKind n w d ⊕ Unit) = .inl k) ↔ ¬ True
    simp only [Sum.inr_ne_inl,exists_false,not_true]

variable {I : Type*} (part : P.Face → I)
def partSelect (i : I) (F : P.Face) : Bool :=
  decide (Interior n w d ell hell word c hc f P F ∧ part F = i)

lemma part_interior (i : I) : InteriorSelection n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i) := by
  intro F hF
  exact (of_decide_eq_true hF).1

lemma part_area (i : I) : actualArea n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i) =
    Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} := by
  apply Fintype.card_congr
  exact {
    toFun := fun F => ⟨⟨F.val,(of_decide_eq_true F.property).1⟩,(of_decide_eq_true F.property).2⟩
    invFun := fun F => ⟨F.val.val,decide_eq_true ⟨F.val.property,F.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma part_boundary (i : I) : actualBoundary n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i) =
    Fintype.card (RelativePartBoundary P.pairing
      (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass) i) := by
  rw [actual_boundary_card]
  apply Fintype.card_congr (Equiv.subtypeEquivRight _)
  intro x
  simp only [partSelect,ne_eq,decide_eq_true_eq,Function.comp_apply]
  tauto

variable [Fintype I]

lemma sum_part_area : (∑ i, actualArea n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i)) =
    Fintype.card (InteriorFace n w d ell hell word c hc f P) := by
  simp only [part_area]
  exact sum_part_sizes (fun F : InteriorFace n w d ell hell word c hc f P => part F.val)

lemma sum_part_boundary : (∑ i, actualBoundary n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i)) =
    Fintype.card (OutsideContact P.pairing (Interior n w d ell hell word c hc f P ∘ P.faceClass)) +
      2 * Fintype.card (RelativeCutContact P.pairing
        (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass)) := by
  simp only [part_boundary]
  exact sum_relative_part_boundary P.pairing _ _

/-- The genuine relative summation identity applied to all small fragments.
This does NOT assume that a low-cut partition exists. -/
theorem actual_partition_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hM : ∀ i, 8 * Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ M) :
    defectConstant α β δ * Fintype.card (InteriorFace n w d ell hell word c hc f P) ≤
      (Fintype.card (OutsideContact P.pairing (Interior n w d ell hell word c hc f P ∘ P.faceClass)) : ℝ) +
      2 * Fintype.card (RelativeCutContact P.pairing
        (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass)) := by
  have hi (i : I) := actual_fragment_bound n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i)
    (part_interior n w d ell hell word c hc f P part i) hs hm hred hrad ha hgood hb
    (by rw [part_area]; exact hM i)
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hi i)
  rw [← Finset.mul_sum,← Nat.cast_sum,← Nat.cast_sum,sum_part_area,sum_part_boundary] at h
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using h

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeInteriorCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))
variable (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
  (hw : xs.map ((target n w d ell hell word c hc f).label ∘ P.index) =
    List.ofFn (letterDart n w ∘ word))
  (ht : ∀ x, (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) (P.index x) ↔ x ∈ xs)

include hw in
lemma exterior_length : xs.length = ell := by
  simpa only [List.length_map,List.length_ofFn] using congrArg List.length hw

include ht in
lemma interior_mem (x : P.Dart) : Interior n w d ell hell word c hc f P (P.faceClass x) ↔ x ∉ xs := by
  rw [interior_iff,ht]

include hx hw ht in
lemma exterior_face_unique : ∃! F : P.Face, ¬ Interior n w d ell hell word c hc f P F := by
  have hl := exterior_length n w d ell hell word c hc f P xs hw
  have hn : xs ≠ [] := by intro he; simp [he] at hl; omega
  obtain ⟨x,hxm⟩ := List.exists_mem_of_ne_nil xs hn
  refine ⟨P.faceClass x,?_,?_⟩
  · change ¬ Interior n w d ell hell word c hc f P (P.faceClass x)
    exact fun hi => (interior_mem n w d ell hell word c hc f P xs ht x).mp hi hxm
  · intro F hF
    have hF' : ¬ Interior n w d ell hell word c hc f P (P.faceClass F.out) := by
      rwa [P.faceClass_out]
    rw [interior_mem n w d ell hell word c hc f P xs ht] at hF'
    have hFm := Classical.not_not.mp hF'
    rw [← P.faceClass_out F,P.faceClass_eq]
    exact hx.sameCycle hFm hxm

include hx hw ht in
/-- Exactly one face is exterior, even with free outside-to-outside folds. -/
lemma interior_card : (Fintype.card (InteriorFace n w d ell hell word c hc f P) : ℤ) =
    cycles P.pairing.face - 1 := by
  obtain ⟨F,hF,huniq⟩ := exterior_face_unique n w d ell hell word c hc f P xs hx hw ht
  have he : Fintype.card {G : P.Face // ¬ Interior n w d ell hell word c hc f P G} = 1 := by
    have : Unique {G : P.Face // ¬ Interior n w d ell hell word c hc f P G} := {
      default := ⟨F,hF⟩
      uniq := fun G => Subtype.ext (huniq G.val G.property) }
    exact Fintype.card_unique
  have hsum := Fintype.card_subtype_compl (Interior n w d ell hell word c hc f P)
  rw [he] at hsum
  rw [cycles_eq_card_classes]
  change (Fintype.card (InteriorFace n w d ell hell word c hc f P) : ℤ) = (Nat.card P.Face : ℤ) - 1
  rw [Nat.card_eq_fintype_card]
  have hle := Fintype.card_subtype_le (Interior n w d ell hell word c hc f P)
  simp only [← Nat.card_eq_fintype_card] at hsum hle
  have hh : Fintype.card (InteriorFace n w d ell hell word c hc f P) + 1 = Fintype.card P.Face := by
    simp only [← Nat.card_eq_fintype_card]
    change Nat.card {G : P.Face // Interior n w d ell hell word c hc f P G} + 1 = Nat.card P.Face
    omega
  have hh' : (Fintype.card (InteriorFace n w d ell hell word c hc f P) : ℤ) + 1 = Fintype.card P.Face := by exact_mod_cast hh
  omega

include hw ht in
lemma outside_contacts_le :
    Fintype.card (OutsideContact P.pairing (Interior n w d ell hell word c hc f P ∘ P.faceClass)) ≤ ell := by
  exact (outside_contacts_le_length P.pairing _ xs (interior_mem n w d ell hell word c hc f P xs ht)).trans_eq
    (exterior_length n w d ell hell word c hc f P xs hw)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeGlobalStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm WordPictures
open scoped BigOperators
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))
variable (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
  (hw : xs.map ((target n w d ell hell word c hc f).label ∘ P.index) =
    List.ofFn (letterDart n w ∘ word))
  (ht : ∀ x, (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) (P.index x) ↔ x ∈ xs)
variable {I : Type*} [Fintype I] (part : P.Face → I)

include hw ht in
/-- The protected exterior contributes at most the literal outside word length.
The cut term is the number of unordered genuine interior contacts, not darts. -/
theorem partition_face_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hM : ∀ i, 8 * Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ M) :
    defectConstant α β δ * Fintype.card (InteriorFace n w d ell hell word c hc f P) ≤
      (ell : ℝ) + 2 * Fintype.card (RelativeCutContact P.pairing
        (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass)) := by
  have hp := actual_partition_bound n w d ell hell word c hc f P part ha hgood hs hm hred hrad hb hM
  have he : (Fintype.card (OutsideContact P.pairing
      (Interior n w d ell hell word c hc f P ∘ P.faceClass)) : ℝ) ≤ ell := by
    exact_mod_cast outside_contacts_le n w d ell hell word c hc f P xs hw ht
  linarith

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeDegree
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

namespace WalkPicture
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A] [DecidableEq S]
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T) {B : FrozenTarget T}

lemma FrozenMapped.face_card (hm : P.FrozenMapped B) (x : P.FrozenDart)
    (ys : List S) (hy : IsBoundary B.next ys) (hx : P.index x.val ∈ ys) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x.val y} = ys.length := by
  obtain ⟨zs,hzs,hzm,hmap⟩ := hm.pullback_boundary x hy hx
  have hb : IsBoundary P.pairing.face (zs.map Subtype.val) :=
    hzs.map Subtype.val Subtype.val_injective (fun _ => rfl)
  rw [← hb.length_eq_card (List.mem_map_of_mem hzm),List.length_map]
  simpa only [List.length_map] using congrArg List.length hmap
end WalkPicture
end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (exteriorWalkTarget n w d ell hell word closed c hc f))

lemma exterior_frozen_degree
    (hm : P.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f))
    (x : P.Dart) (s : (frozenBoundary n w d).Side)
    (hx : P.index x = .inl (.inr s)) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y} ≤ 6 := by
  obtain ⟨ys,hys,hmem,hlen⟩ := (frozenBoundary n w d).oriented_boundary s
  have hxF : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind (P.index x)) = false := by
    rw [hx]; rfl
  let j : (frozenBoundary n w d).Side →
      WalkStep n w d ⊕ (walkTarget n w d c hc f).ExteriorSide ell hell word closed :=
    fun z => .inl (.inr z)
  have hj : Function.Injective j := Sum.inl_injective.comp Sum.inr_injective
  have hys' : IsBoundary (exteriorWalkFrozen n w d ell hell word closed c hc f).next
      (ys.map j) := hys.map j hj (fun _ => rfl)
  have hh := hm.face_card P (⟨x,hxF⟩ : P.FrozenDart) (ys.map j) hys'
    (by change P.index x ∈ ys.map j; rw [hx]; exact List.mem_map_of_mem hmem)
  rw [List.length_map,hlen] at hh
  rw [hh]
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a) <;> norm_num [frozenBoundary,frozenCell,size]

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFillingValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction

/-! The integral filling value of a literal nullword. This is a consequence
of constructed disks and sphere vanishing, not a replacement hypothesis. -/

/-! Literal walks in a signed incidence graph, with componentwise root paths.
No connectedness or universal-cover assertion is assumed. -/

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/

/-! Local elementary triangle incidence induces the exact radial contraction. -/

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

/-! Group-isomorphism transport for geometric actions. -/

/-! Actual homotopy-equivalence invariance of the fundamental group. -/

/-! The literal finite barycentric complex has exactly the original letter group,
not a conditional presentation of it. -/

namespace ConeSkeleton

/-! Infinitude can be obtained without a topological Euler theorem: the many
six-letter cells alone inject into the original letter-edge module of any
finite cover. Their cardinality exceeds the number of original generators. -/

open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

abbrev SixChain := (LetterPresentation.Group n w d × Six n d) →₀ ℤ

end ConeSkeleton

/-! The same supplied final arrays yield infinite groups unconditionally.
This discharges the last group-action-side hypothesis; the finite-polyhedron
realization and group-to-topology consequences are still separate obligations. -/

/-! Elementary facts about WordLength and WordDistance for the four-point
characterization of hyperbolicity. -/

/-! Cochains are evaluated on the actual area-counted word homotopies.
Free folds contribute exactly zero; each literal relator contributes its
own cochain integral. No planar realization hypothesis is needed. -/

/-! Finite unit-speed vertex paths; all indices are bounded explicitly. -/

/-! A quantitative proof that linear word-homotopy filling bounds imply
four-point hyperbolicity. -/

/-! All clauses of the exact main except exclusion of compatible locally
CAT(-1) finite homotopy models. The complete literal hyperbolicity consequence
is now unconditional, on the SAME finite aspherical complex. -/

/-! The real comparison inequality needed to pass the manuscript's exact
cosh-midpoint CAT(-1) definition to the Euclidean CN midpoint inequality. -/

/-! The global cosh-midpoint comparison implies whole-segment CAT(0)
comparison. No completeness or globalization
hypothesis is hidden in this elementary curvature-monotonicity step. -/

/-! The finite difference maximum principle required for local geodesic
continuation. Endpoint estimates are literal, with no convergence assumption. -/

/-! Literal equal-time interpolation of finite geodesic polygons. -/
open Set Metric

end HyperbolicObstruction

end

end OAI
end



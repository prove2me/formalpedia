-- Prove2me | Definitions.Def_OAIQ034H011
-- name    : OAIQ034H011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:48:05.097324+00:00
-- url     : https://prove2.me/theorems/ca105ff1-3f68-43b3-95cd-32ad7178f56c
-- title:
--   Definitions bundle OAIQ034H011 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 224 declarations of OpenAI's Lean: 67 definitions, 2 inductive types or structures, 8 instances and 147 theorems. The definitions and types are `OAI.HyperbolicObstruction.ConeSkeleton.elementaryBasepoint`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryComparison`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryDecodePicture`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryEncodedBoundary`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryFiniteBasepoint`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryFiniteHomeomorph`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryFinitePiOneEquiv`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryHigherCoverEquiv`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryLetterLiftedBoundary`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryLetterToTopology`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryMacroPicture`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryPositiveVoltage`, `OAI.HyperbolicObstruction.ConeSkeleton.elementarySourceVoltage`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryTopologyEquiv`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryTopologyToLetter`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryUniversalBasepoint`, `OAI.HyperbolicObstruction.ConeSkeleton.letterBoundary₂`, `OAI.HyperbolicObstruction.ConeSkeleton.liftedFrozenTarget`, `OAI.HyperbolicObstruction.ConeSkeleton.liftedWalkTarget`, `OAI.HyperbolicObstruction.ConeSkeleton.sixBoundary`, `OAI.HyperbolicObstruction.ConeSkeleton.sixFaceBoundary`, `OAI.HyperbolicObstruction.ConeSkeleton.triangleFace`, `OAI.HyperbolicObstruction.CoreGeometry.MetricCore.toObstruction`, `OAI.HyperbolicObstruction.CoreGeometry.Valid`, `OAI.HyperbolicObstruction.FiniteComplex.EdgeGenerator`, `OAI.HyperbolicObstruction.FiniteComplex.generatorChain`, `OAI.HyperbolicObstruction.FiniteComplex.signedChain`, `OAI.HyperbolicObstruction.FiniteComplex.wordChain`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgeChain.ofListEnd`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgePresentation.WordRelation`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgePresentation.chainWord`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgePresentation.wordToTopology`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape.rate`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.Shape.cost`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.rankRate`, `OAI.HyperbolicObstruction.IncidenceTemplate.RankSamplingStage`, `OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage.letter`, `OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage.potential`, `OAI.HyperbolicObstruction.IncidenceTemplate.actualRankSamplingStage`, `OAI.HyperbolicObstruction.IncidenceTemplate.diagramCutoff` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_ActualContact`, `HyperbolicGroups_ActualDegree`, `HyperbolicGroups_ActualFaceCounts`, `HyperbolicGroups_ActualFragment`, `HyperbolicGroups_ActualLayers`, `HyperbolicGroups_ActualLiftedChain`, `HyperbolicGroups_ActualPartition`, `HyperbolicGroups_ActualRawAccount`, `HyperbolicGroups_ActualRawCount`, `HyperbolicGroups_ActualWeights`, `HyperbolicGroups_ConeDiskNormal`, `HyperbolicGroups_ConeFullNormal`, `HyperbolicGroups_ConePresentationGroup`, `HyperbolicGroups_CoreWordGraph`, `HyperbolicGroups_DiagramSampling`, `HyperbolicGroups_ElementaryCone`, `HyperbolicGroups_ElementaryCover`, `HyperbolicGroups_ExteriorTarget`, `HyperbolicGroups_FragmentSlots`, `HyperbolicGroups_GlobalClosedPicture`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_IndexedPictureAppend`, `HyperbolicGroups_LetterCover`, `HyperbolicGroups_LetterNormalPicture`, `HyperbolicGroups_LiftedClosedPicture`, `HyperbolicGroups_LiftedDiagramSampling`, `HyperbolicGroups_MetricHexagon`, `HyperbolicGroups_NormalDiskArea`, `HyperbolicGroups_OriginalLinearFilling`, `HyperbolicGroups_PolygonDiskProducer`, `HyperbolicGroups_Presentation`, `HyperbolicGroups_ProtectedNormal`, `HyperbolicGroups_RankCollection`, `HyperbolicGroups_RankSampling`, `HyperbolicGroups_RankSelection`, `HyperbolicGroups_RelativeDegree`, `HyperbolicGroups_RelativeGlobalStep`, `HyperbolicGroups_RelativeSmallPartition`, `HyperbolicGroups_SelectedPresentation`, `HyperbolicGroups_Shape`, `HyperbolicGroups_SimpleLetterPresentation`, `HyperbolicGroups_WalkApexAggregate`, `HyperbolicGroups_WalkMultiplicity`, `HyperbolicGroups_WalkPayment`, `HyperbolicGroups_WalkRadialBoundary`, `HyperbolicGroups_WalkRawPosition`, `HyperbolicGroups_WalkTopTurns`, `HyperbolicGroups_WalkTriangleTransport`, `HyperbolicGroups_WalkTurnTransport`, `HyperbolicGroups_WordDisk`, `HyperbolicGroups_WordPictureAppend`, `HyperbolicGroups_WordPictureArea`, `HyperbolicGroups_WordPictureExist`, `HyperbolicGroups_WordPictureLiteral`.
--
--   **Imports.** It imports the published bundle `Def_HyperbolicObstruction`; the bundles `OAIQ034H007`, `OAIQ034H008`, `OAIQ034H009` and `OAIQ034H010` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.HyperbolicObstruction.IncidenceTemplate.exists_finite_aspherical_hyperbolic_noAction`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_HyperbolicObstruction
import Definitions.Def_OAIQ034H007
import Definitions.Def_OAIQ034H008
import Definitions.Def_OAIQ034H009
import Definitions.Def_OAIQ034H010

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricHexagon
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate
instance instDecidableOpposite (v w : Vertex) : Decidable (Opposite v w) := by
  cases v <;> cases w <;> unfold Opposite <;> infer_instance

def Valid (H : HexagonCode) : Prop :=
  (∀ i : Fin 6, Adjacent (H.vertices i) (H.vertices (i+1))) ∧
  (∀ i : Fin 6, H.vertices i ≠ H.vertices (i+2)) ∧
  (∀ i : Fin 6, Opposite (H.vertices i) (H.vertices (i+3)))
instance instDecidableValid (H : HexagonCode) : Decidable (Valid H) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))


lemma centerHex_valid (n : Fin 44) : Valid (centerHex n) := by
  fin_cases n <;> decide

lemma lineHex_valid (l m : Fin 7) (hne : l ≠ m) : Valid (lineHex l m) := by
  fin_cases l <;> fin_cases m <;> first | contradiction | decide

end CoreGeometry
end HyperbolicObstruction


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate

lemma threeQuota_of_opposite {a b c d : Vertex}
    (hab : Adjacent a b) (hbc : Adjacent b c) (hcd : Adjacent c d)
    (had : Opposite a d) : ThreeQuota a b c d := by
  intro i hi
  rcases hi with ⟨hi₁, hi₂, hi₃⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Adjacent, Opposite, InFan]

namespace MetricCore
variable {X : Type*} [MetricSpace X] {z : Vertex → X} (D : MetricCore z)
include D

theorem three_of_opposite {a b c d : Vertex}
    (hab : Adjacent a b) (hbc : Adjacent b c) (hcd : Adjacent c d)
    (had : Opposite a d) : 3 ≤ dist (z a) (z d) ^ 2 := by
  apply D.threeStep a b c d hab hbc hcd
  · intro he
    subst c
    exact hcd.not_opposite had
  · intro he
    subst d
    exact hab.not_opposite had
  · exact threeQuota_of_opposite hab hbc hcd had

theorem hexagon (H : HexagonCode) (hH : Valid H) : MetricHexagon (z ∘ H.vertices) := by
  constructor
  · intro i
    exact D.side _ _ (hH.1 i)
  · intro i
    apply D.twoStep _ (H.vertices (i + 1)) _ (hH.1 i)
    · simpa [add_assoc] using hH.1 (i + 1)
    · exact hH.2.1 i
  · intro i
    apply D.three_of_opposite (hH.1 i)
    · exact hH.1 (i + 1)
    · convert hH.1 (i + 2) using 1 <;> fin_cases i <;> rfl
    · exact hH.2.2 i

theorem centerPairs (h : CATZero X) (n : Fin 44) :
    CATZero.mid h (z (.inl (centerPair n).1)) (z (.inr (centerPair n).2)) =
      center (z := z) h := by
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      rfl
    · obtain ⟨hlt, ha, hb⟩ := centerHex_parent n hn
      have hh := ((D.hexagon (centerHex n) (centerHex_valid n)).rigidity h).2 (2 : Fin 6)
      change CATZero.mid h (z (.inl (centerHex n).b)) (z (.inr (centerHex n).ca)) =
        CATZero.mid h (z (.inl (centerHex n).a)) (z (.inr (centerHex n).bc)) at hh
      rw [ha, hb, (centerHex_pair n).1, (centerHex_pair n).2] at hh
      exact hh.symm.trans (ih (centerParent n) hlt)

theorem hexagon_center (h : CATZero X) (H : HexagonCode) (hH : Valid H) :
    CATZero.mid h (z (H.vertices 0)) (z (H.vertices 3)) = center (z := z) h := by
  have ho := hH.2.2 (0 : Fin 6)
  change ¬ Incident (pointOfRepresentative H.a) H.bc at ho
  obtain ⟨n, hn⟩ := centerPair_complete H.a H.bc ho
  have he := D.centerPairs h n
  rw [hn] at he
  exact he

theorem radius_point (h : CATZero X) (r : Fin 11) :
    dist (center (z := z) h) (z (.inl r)) ^ 2 = 3 / 4 := by
  let H := centerHex (pointIndex r)
  have he := (D.hexagon H (centerHex_valid _)).radius h (0 : Fin 6)
  simp only [Function.comp_apply] at he
  rw [D.hexagon_center h H (centerHex_valid _)] at he
  change dist (center (z := z) h) (z (.inl (centerHex (pointIndex r)).a)) ^ 2 = _ at he
  rw [(centerHex_pair _).1, pointIndex_correct] at he
  exact he

theorem radius_line (h : CATZero X) (l : Fin 7) :
    dist (center (z := z) h) (z (.inr l)) ^ 2 = 3 / 4 := by
  let H := centerHex (lineIndex l)
  have he := (D.hexagon H (centerHex_valid _)).radius h (3 : Fin 6)
  simp only [Function.comp_apply] at he
  rw [D.hexagon_center h H (centerHex_valid _)] at he
  change dist (center (z := z) h) (z (.inr (centerHex (lineIndex l)).bc)) ^ 2 = _ at he
  rw [(centerHex_pair _).2, lineIndex_correct] at he
  exact he

theorem line_dist (h : CATZero X) (l m : Fin 7) (hne : l ≠ m) :
    dist (z (.inr l)) (z (.inr m)) ^ 2 = 2 := by
  have he := ((D.hexagon (lineHex l m) (lineHex_valid l m hne)).rigidity h).1
    (1 : Fin 6) (5 : Fin 6)
  change dist (z (.inr (lineHex l m).ab)) (z (.inr (lineHex l m).ca)) ^ 2 = (2 : ℕ) at he
  rw [(lineHex_coordinates _ _ hne).1, (lineHex_coordinates _ _ hne).2] at he
  exact_mod_cast he

theorem line_flat (h : CATZero X) (l m : Fin 7) (hne : l ≠ m) :
    dist (center (z := z) h) (CATZero.mid h (z (.inr l)) (z (.inr m))) ^ 2 = 1 / 4 := by
  let H := lineHex l m
  have he := (D.hexagon H (lineHex_valid l m hne)).central_mid h (1 : Fin 6) (5 : Fin 6)
  simp only [Function.comp_apply] at he
  rw [D.hexagon_center h H (lineHex_valid l m hne)] at he
  change dist (center (z := z) h)
    (CATZero.mid h (z (.inr (lineHex l m).ab)) (z (.inr (lineHex l m).ca))) ^ 2 =
      3 / 4 - (2 : ℕ) / 4 at he
  rw [(lineHex_coordinates _ _ hne).1, (lineHex_coordinates _ _ hne).2] at he
  norm_num at he ⊢
  exact he

end MetricCore
end CoreGeometry
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry

namespace MetricCore
variable {X : Type*} [MetricSpace X] {z : Vertex → X} (D : MetricCore z)

/-- Assemble the source's actual graph configuration, rather than assuming
common centers or tangent-cone distances, into the proved obstruction. -/
def toObstruction (h : CATZero X) (he : ExceptionalTest h z) : FiniteObstructionData h where
  c := center (z := z) h
  x := fun i => z (.inl (xRep i))
  y := fun i => z (.inl (yRep i))
  line := fun i => z (.inr (sixLine i))
  radiusX := fun i => D.radius_point h (xRep i)
  radiusY := fun i => D.radius_point h (yRep i)
  radiusLine := fun i => D.radius_line h (sixLine i)
  lineDist := fun a b hab => D.line_dist h _ _ (sixLine_injective.ne hab)
  lineFlat := fun a b hab => D.line_flat h _ _ (sixLine_injective.ne hab)
  square := by
    intro i a b ha hb hab
    constructor
    · exact D.side _ _ (fullLines_x i a ha)
    · exact D.side _ _ (fullLines_y i a ha).symm
    · exact D.side _ _ (fullLines_y i b hb)
    · exact D.side _ _ (fullLines_x i b hb).symm
    · exact D.twoStep _ _ _ (fullLines_x i a ha) (fullLines_y i a ha).symm
        (by simpa only [ne_eq, Sum.inl.injEq] using xy_distinct i)
    · exact D.line_dist h _ _ (sixLine_injective.ne hab)
  twoStepX := D.twoStep (.inl 2) (.inr 4) (.inl 3) (by decide) (by decide) (by decide)
  twoStepY := D.twoStep (.inl 9) (.inr 4) (.inl 3) (by decide) (by decide) (by decide)
  loose := D.side (.inr 4) (.inl 3) (by decide)
  missing := D.threeStep (.inl 10) (.inr 6) (.inl 3) (.inr 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  fractional := he

end MetricCore
end CoreGeometry
end HyperbolicObstruction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Presentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

theorem coreRoute_exists (v : CoreGeometry.Vertex) : ∃ p : Path root (.inl v), p.IsCore := by
  rcases v with r | l
  · fin_cases r
    · refine ⟨(.nil _), ?_⟩; simp only [Path.IsCore,Path.fields,List.not_mem_nil,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 1)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 3)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 4)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 6)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 7)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 8)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 9)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 10)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
  · fin_cases l
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.cons (coreStep (a := (.inl 2)) (b := (.inr 0)) (by decide)) (.nil _)))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.nil _)), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.nil _)), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.cons (coreStep (a := (.inl 5)) (b := (.inr 3)) (by decide)) (.nil _)))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.cons (coreStep (a := (.inl 2)) (b := (.inr 4)) (by decide)) (.nil _)))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.cons (coreStep (a := (.inl 5)) (b := (.inr 5)) (by decide)) (.nil _)))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.nil _)), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]

def coreRoute (v : CoreGeometry.Vertex) : Path root (.inl v) := (coreRoute_exists v).choose
lemma coreRoute_core (v : CoreGeometry.Vertex) : (coreRoute v).IsCore :=
  (coreRoute_exists v).choose_spec

end MasterGraph

namespace LetterPresentation
open IncidenceTemplate MasterGraph
variable (n : ℕ)

variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma top_relator (a : StarModel.Matches rowSupport w) (v : MasterGraph.Vertex)
    (p : MasterGraph.Path v v) (hp : p.IsCore) : p.eval a.val (letter n w d) = 1 := by
  change p.eval a.val (fun i => PresentedGroup.mk (Relator n w d) (freeLetter n i)) = 1
  rw [← Path.eval_map]
  exact PresentedGroup.one_of_mem (Relator.top a.val (a.property _) (fun i => a.property _) v p hp)

lemma square_relator (a : StarModel.Matches rowSupport w) (τ : TwoPath) :
    MasterGraph.squareWord a.val (letter n w d) τ = 1 := by
  change squareWord a.val (fun i => PresentedGroup.mk (Relator n w d) (freeLetter n i)) τ = 1
  rw [← squareWord_map]
  exact PresentedGroup.one_of_mem (Relator.square a.val τ (a.property _))


def coreValue (a : StarModel.Matches rowSupport w) (v : CoreGeometry.Vertex) : Group n w d :=
  (coreRoute v).eval a.val (letter n w d)

lemma coreValue_path (a : StarModel.Matches rowSupport w) {v z : CoreGeometry.Vertex}
    (p : MasterGraph.Path (.inl v) (.inl z)) (hp : p.IsCore) :
    coreValue n w d a z = coreValue n w d a v * p.eval a.val (letter n w d) := by
  have hh := top_relator n w d a root
    (((coreRoute v).append p).append (coreRoute z).symm)
    (Path.isCore_append _ _ (Path.isCore_append _ _ (coreRoute_core v) hp)
      (Path.isCore_symm _ (coreRoute_core z)))
  simp only [Path.eval_append,Path.eval_symm] at hh
  exact (eq_of_mul_inv_eq_one hh).symm

def vertexValue (a : StarModel.Matches rowSupport w) : MasterGraph.Vertex → Group n w d
  | .inl v => coreValue n w d a v
  | .inr τ => coreValue n w d a (right τ) * letter n w d (a.val (.inr (τ,0)))

lemma coreValue_step (a : StarModel.Matches rowSupport w)
    {v z : CoreGeometry.Vertex} (s : Step (.inl v) (.inl z))
    (hs : ∃ e : Edge, s.field = .inl e) :
    coreValue n w d a z = coreValue n w d a v * s.value a.val (letter n w d) := by
  have hh := coreValue_path n w d a (.cons s (.nil _)) (by
    intro f hf
    simp only [Path.fields,List.mem_cons,List.not_mem_nil,or_false] at hf
    exact hf ▸ hs)
  simpa only [Path.eval,mul_one] using hh

/-- Every master match has a genuine group-valued potential in the literal
letter presentation. Only its actual top and square relators are used. -/
def potential (a : StarModel.Matches rowSupport w) : Potential a.val (letter n w d) where
  val := vertexValue n w d a
  root_one := top_relator n w d a root (coreRoute (.inl 0)) (coreRoute_core _)
  edge f := by
    rcases f with e | ⟨τ,j⟩
    · exact coreValue_step n w d a (Step.pos (.inl e)) ⟨e,rfl⟩
    · fin_cases j
      · rfl
      · have h₁ := coreValue_step n w d a (first τ) ⟨_,first_field τ⟩
        have h₂ := coreValue_step n w d a (second τ) ⟨_,second_field τ⟩
        have hh := square_relator n w d a τ
        change coreValue n w d a (left τ) =
          (coreValue n w d a (right τ) * letter n w d (a.val (.inr (τ,0)))) *
            letter n w d (a.val (.inr (τ,1)))
        rw [h₂,h₁]
        simp only [mul_assoc]
        have hh' : (first τ).value a.val (letter n w d) *
            ((second τ).value a.val (letter n w d) *
              (letter n w d (a.val (.inr (τ,0))) * letter n w d (a.val (.inr (τ,1))))) = 1 := by
          simpa only [squareWord,mul_assoc] using hh
        rw [hh',mul_one]

end LetterPresentation
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordDisk
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace Homotopy
variable {R : Set (Word A)} {u v w : Word A} {n : ℕ}

lemma append {m : ℕ} (h : Homotopy R u v n) (h' : Homotopy R w [] m) :
    Homotopy R (u++w) v (n+m) := by
  have h1 : Homotopy R (u++w) (v++w) n := by
    simpa using h.contextual [] w
  have h2 : Homotopy R (v++w) v m := by
    simpa using h'.contextual v []
  exact h1.trans h2

lemma append_null {v : Word A} {m : ℕ} (h : Homotopy R u [] n)
    (h' : Homotopy R v [] m) : Homotopy R (u++v) [] (n+m) := h.append h'

end Homotopy

/-- Freely represented words admitting a finite disk construction. -/
def nullSubgroup (R : Set (Word A)) : Subgroup (FreeGroup A) where
  carrier g := ∃ w, FreeGroup.mk w = g ∧ ∃ n, Homotopy R w [] n
  one_mem' := ⟨[],rfl,0,.refl _⟩
  mul_mem' := by
    rintro _ _ ⟨u,rfl,m,hu⟩ ⟨v,rfl,n,hv⟩
    exact ⟨u++v,rfl,m+n,hu.append_null hv⟩
  inv_mem' := by
    rintro _ ⟨u,rfl,n,hu⟩
    exact ⟨FreeGroup.invRev u,rfl,n,by simpa using hu.reverse⟩

instance instNormalFreeGroupNullSubgroup (R : Set (Word A)) : (nullSubgroup R).Normal where
  conj_mem := by
    rintro _ ⟨u,rfl,n,hu⟩ g
    obtain ⟨q,rfl⟩ := Quot.exists_rep g
    exact ⟨q++u++FreeGroup.invRev q,rfl,n,hu.conjugate q⟩

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Shape
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.shapeFintype _root_.OAI.HyperbolicObstruction.LetterPresentation.group
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

def cost (α β δ : ℝ) : Trial s u q v → ℝ
  | .inl _ => -actualRowCost α β δ (.inr (.inl ()))
  | .inr (.inl b) => -actualRowCost α β δ (.inl (T.1 b))
  | .inr (.inr (.inl e)) => -actualRowCost α β δ (.inr (.inr (T.2.2 e)))
  | .inr (.inr (.inr _)) => -3-δ

lemma probability_row {A : Type*} [Fintype A] (α β δ : ℝ) (σ : T.Pos v → A)
    (r : Trial s u q v) : probability α β δ A (T.row σ r) =
      (Fintype.card A:ℝ)^(T.cost α β δ r) := by
  rcases r with a | (b | (e | e)) <;> rfl

/-- Cancellation of the field count with the exact negative Bernoulli costs.
This is the source rank budget, with p=3-beta and f=2-alpha. -/
lemma rank_budget (α β δ : ℝ) : (Fintype.card (T.Pos v):ℝ) + ∑ r : Trial s u q v, T.cost α β δ r =
    ((3-β)-7*(2-α))*s + (2-α)*u + (2-δ)*q + (3-δ)*v := by
  rw [cardinal_positions]
  simp only [cost,Fintype.sum_sum_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,actualRowCost,rowCost,rowSurcharge]
  push_cast
  rw [Finset.sum_neg_distrib,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

instance instDecidablePredForallEntrySymmetricAlphabetBoolGood {n : ℕ} (α β δ : ℝ) : DecidablePred (T.Good (v := v) (n := n) α β δ) :=
  fun _ => Classical.propDecidable _

lemma not_good_iff {n : ℕ} (α β δ : ℝ) (w : Entry (SymmetricAlphabet n) → Bool) :
    ¬T.Good (v := v) α β δ w ↔ Coincidence.RankBad (T.row (v := v)) (∑ r : Trial s u q v, T.cost α β δ r) w := by
  classical
  simp only [Good,Coincidence.RankBad,T.rank_budget,not_forall,not_le]
  aesop

/-- Source diagram:rank for a fixed shape, uniformly over all literal signed
assignments and all distinct actual trials. -/
theorem bad_bound {n : ℕ} {α β δ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) :
    (FiniteLaw.bernoulliProduct (probability α β δ (SymmetricAlphabet n))
      (probability_mem ha hb hd)).prob (fun w => ¬T.Good (v := v) α β δ w) ≤
      Coincidence.rankRate (Fintype.card (T.Pos v)) (∑ r : Trial s u q v, T.cost α β δ r)
        (Fintype.card (SymmetricAlphabet n)) := by
  classical
  simp_rw [T.not_good_iff]
  exact Coincidence.rank_bad_bound T.row _ _ (T.cost α β δ) (T.probability_row α β δ)

end Shape
end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRawPosition
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

universe u
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma contact_different (hred : P.FullyReduced) (x : P.Dart)
    (hx : isLetter n w (walkLabel n w d (P.index x)) = true) :
    rawPosition n w d (P.index x) ≠ rawPosition n w d (P.index (P.pairing.edge x)) := by
  intro hp
  have he : walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) := P.paired x
  apply hred x
  apply raw_position_reverse n w d hx _ hp he
  rw [he]
  exact hx

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RankCollection
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.LetterPresentation.group
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

instance instFintypeBoundedShape (M : ℕ) : Fintype (BoundedShape M) := by
  classical
  unfold BoundedShape
  infer_instance

namespace BoundedShape
variable {M : ℕ} (b : BoundedShape M)
instance instDecidablePredForallEntrySymmetricAlphabetBoolGood {n : ℕ} (α β δ : ℝ) : DecidablePred (b.Good (n := n) α β δ) :=
  fun _ => Classical.propDecidable _

def rate (α β δ N : ℝ) : ℝ :=
  Coincidence.rankRate (Fintype.card (b.shape.Pos b.sixes))
    (∑ r : Shape.Trial b.tops b.fans b.squares b.sixes, b.shape.cost α β δ r) N

lemma rate_tendsto (α β δ : ℝ) : Tendsto (b.rate α β δ) atTop (𝓝 0) :=
  Coincidence.rankRate_tendsto _ _

lemma bad_bound {n : ℕ} {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) :
    (FiniteLaw.bernoulliProduct (probability α β δ (SymmetricAlphabet n))
      (probability_mem ha hb hd)).prob (fun w => ¬b.Good α β δ w) ≤
      b.rate α β δ (Fintype.card (SymmetricAlphabet n)) :=
  b.shape.bad_bound ha hb hd
end BoundedShape

instance instDecidablePredForallEntrySymmetricAlphabetBoolGoodUpTo (M : ℕ) {n : ℕ} (α β δ : ℝ) : DecidablePred (GoodUpTo M (n := n) α β δ) :=
  fun _ => Classical.propDecidable _

def rankRate (M : ℕ) (α β δ N : ℝ) : ℝ := ∑ b : BoundedShape M, b.rate α β δ N

lemma rankRate_tendsto (M : ℕ) (α β δ : ℝ) : Tendsto (rankRate M α β δ) atTop (𝓝 0) := by
  unfold rankRate
  simpa only [rankRate,Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ : Finset (BoundedShape M)) (fun b _ => b.rate_tendsto α β δ)

/-- The bounded-rank bad-event probability tends to zero, with literal costs
and original full probability space. -/
theorem rank_bad_bound (M : ℕ) {n : ℕ} {α β δ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) :
    (FiniteLaw.bernoulliProduct (probability α β δ (SymmetricAlphabet n))
      (probability_mem ha hb hd)).prob (fun w => ¬GoodUpTo M α β δ w) ≤
      rankRate M α β δ (Fintype.card (SymmetricAlphabet n)) := by
  classical
  simp only [GoodUpTo,not_forall]
  exact (FiniteLaw.prob_exists_le _ _).trans (Finset.sum_le_sum fun b _ => b.bad_bound ha hb hd)

end IncidenceTemplate.Occurrences
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkMultiplicity
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

/-- Top loose fields and every decoration field occur at most once in each
selected source face of that occurrence. -/
lemma raw_multiplicity_le_faces (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f)) (p : RawPosition n w d) :
    Fintype.card (RawPositionSide n w d c hc f P select p) ≤
      Fintype.card (KindFace n w d c hc f P select (walkKind n w d (rawRepresentative n w d p))) := by
  let g : RawPositionSide n w d c hc f P select p →
      KindFace n w d c hc f P select (walkKind n w d (rawRepresentative n w d p)) := fun x =>
    ⟨P.faceClass x.val,x.property.1,by
      change walkKind n w d (P.index x.val) = _
      rw [raw_kind n w d (P.index x.val),x.property.2.2]⟩
  apply Fintype.card_le_of_injective g
  intro x y h
  apply Subtype.ext
  exact raw_position_once_per_face n w d c hc f P hs hb hm
    (P.faceClass_eq.mp (congrArg Subtype.val h)) x.property.2.1 y.property.2.1
    (x.property.2.2.trans y.property.2.2.symm)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualWeights
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_position_capacity (hb : P.NoBigon) (p : RawPosition n w d) :
    Fintype.card (RawPositionSide n w d c hc f P select p) ≤
      (actualWeights n w d c hc f P select hs hm hred hrad).position (rawToPosition n w d p) := by
  rcases p with a | (g | (⟨q,i⟩ | ⟨q,i⟩))
  · have hh := raw_multiplicity_le_faces n w d c hc f P select hs hb hm (.inl a)
    simp only [← Nat.card_eq_fintype_card] at hh
    simpa only [actualWeights,Occurrences.Shape.Weights.position,rawToPosition,Equiv.symm_apply_apply,
      rawRepresentative,walkKind,FanLink.IndexedFanData.weight, ← Nat.card_eq_fintype_card] using hh
  · have hh := raw_fan_multiplicity_le n w d c hc f P select hm hred hrad g
    change _ ≤ (indexedFanData n w d c hc f P select
      ((enumFan n w).symm ((enumFan n w) g.1)) hs hm hred hrad).weight
    rw [indexed_weight_congr n w d c hc f P select hs hm hred hrad ((enumFan n w).symm_apply_apply _)]
    exact hh.trans (le_max_left _ _)
  · have hh := raw_multiplicity_le_faces n w d c hc f P select hs hb hm (.inr (.inr (.inl (q,i))))
    simp only [← Nat.card_eq_fintype_card] at hh
    simpa only [actualWeights,Occurrences.Shape.Weights.position,rawToPosition,Equiv.symm_apply_apply,
      rawRepresentative,walkKind,FanLink.IndexedFanData.weight, ← Nat.card_eq_fintype_card] using hh
  · have hh := raw_multiplicity_le_faces n w d c hc f P select hs hb hm (.inr (.inr (.inr (q,i))))
    simp only [← Nat.card_eq_fintype_card] at hh
    simpa only [actualWeights,Occurrences.Shape.Weights.position,rawToPosition,Equiv.symm_apply_apply,
      rawRepresentative,walkKind,FanLink.IndexedFanData.weight, ← Nat.card_eq_fintype_card] using hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualContact
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

lemma actual_contact_ne (hred : P.FullyReduced) (e : ActualContact n w d c hc f P select) :
    contactLeft n w d c hc f P select e ≠ contactRight n w d c hc f P select e := by
  intro h
  exact contact_different n w d c hc f P hred e.val e.property.1 ((rawToPosition_injective n w d) h)

lemma actual_contact_value (e : ActualContact n w d c hc f P select) :
    (occurrenceValues n w d (contactLeft n w d c hc f P select e)).1 =
      (occurrenceValues n w d (contactRight n w d c hc f P select e)).1 := by
  have hl := raw_label_value n w d (P.index e.val) e.property.1
  have hr := raw_label_value n w d (P.index (P.pairing.edge e.val))
    ((rawDart_pair n w d c hc f P e.val).mpr e.property.1)
  have he := congrArg Prod.fst (P.paired e.val)
  have hh : Sum.inl ((occurrenceValues n w d (contactRight n w d c hc f P select e)).1) =
      (Sum.inl ((occurrenceValues n w d (contactLeft n w d c hc f P select e)).1) : ConeSkeleton.Edge n w) := by
    exact hr.symm.trans (he.trans hl)
  exact (Sum.inl.inj hh).symm

variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_contact_capacity (hb : P.NoBigon) (p : (occurrenceShape n w).Pos (Fintype.card (Six n d))) :
    (Finset.univ.filter (fun e : ActualContact n w d c hc f P select =>
      contactLeft n w d c hc f P select e = p ∨ contactRight n w d c hc f P select e = p)).card ≤
      (actualWeights n w d c hc f P select hs hm hred hrad).position p := by
  obtain ⟨r,rfl⟩ := rawToPosition_surjective n w d p
  have heq (e : ActualContact n w d c hc f P select) :
      (contactLeft n w d c hc f P select e = rawToPosition n w d r ∨
      contactRight n w d c hc f P select e = rawToPosition n w d r) ↔
      (rawPosition n w d (P.index e.val) = r ∨ rawPosition n w d (P.index (P.pairing.edge e.val)) = r) := by
    simp only [contactLeft,contactRight,(rawToPosition_injective n w d).eq_iff]
  simp_rw [heq]
  rw [← Fintype.card_subtype]
  have hh := P.pairing.contact_capacity (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)
    (rawDart_pair n w d c hc f P) (fun x => rawPosition n w d (P.index x)) r
  have hcard : Fintype.card (PictureMap.PositionSide (selectedDart n w d c hc f P select)
      (rawDart n w d c hc f P) (fun x => rawPosition n w d (P.index x)) r) =
      Fintype.card (RawPositionSide n w d c hc f P select r) := by
    apply Fintype.card_congr
    exact { toFun := fun x => ⟨x.val.val,x.val.property.2,x.val.property.1,x.property⟩
            invFun := fun x => ⟨⟨x.val,x.property.2.1,x.property.1⟩,x.property.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [hcard] at hh
  simpa only [← Nat.card_eq_fintype_card] using
    hh.trans (actual_position_capacity n w d c hc f P select hs hm hred hrad hb r)

/-- The contact-counting estimate for the literal normalized mixed picture.
Only the stochastic rank event and layer-size bounds remain here; no side
capacity, radial accounting, or label-incidence premise is assumed. -/
theorem actual_contact_bound {M : ℕ} {α β δ : ℝ}
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (ht : ∀ j, Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).TopAt j) ≤ M)
    (hf : ∀ j, Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).FanAt j) ≤ M)
    (hq : ∀ j, Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).SquareAt j) ≤ M)
    (hv : ∀ j, Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).SixAt j) ≤ M) :
    let W := actualWeights n w d c hc f P select hs hm hred hrad
    (Fintype.card (ActualContact n w d c hc f P select) : ℝ) ≤
      ((3-β)-7*(2-α)) * (∑ a, (W.top a : ℝ)) + (2-α) * (∑ b, (W.fan b : ℝ)) +
      (2-δ) * (∑ q, (W.square q : ℝ)) + (3-δ) * (∑ q, (W.six q : ℝ)) := by
  let W := actualWeights n w d c hc f P select hs hm hred hrad
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
    (contactLeft n w d c hc f P select) (contactRight n w d c hc f P select)
    (actual_contact_ne n w d c hc f P select hred) (actual_contact_value n w d c hc f P select)
    (by
      intro p
      convert actual_contact_capacity n w d c hc f P select hs hm hred hrad hb p using 1
      all_goals try with_reducible_and_instances rfl
      exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _))

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FragmentSlots
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

/-- Each selected top polygon contributes all seven indexed fan slots,
including the fan slots its simple boundary omits. -/
theorem fragment_slots_eq :
    (∑ b : Fan n w, Fintype.card (SelectedTop n w d c hc f P select b)) =
      7 * Fintype.card (SelectedTopFace n w d c hc f P select) := by
  rw [← Fintype.card_sigma]
  have h := Fintype.card_congr (Equiv.ofBijective _
    ⟨topSlot_injective n w d c hc f P select,topSlot_surjective n w d c hc f P select⟩)
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using h.symm

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRadialBoundary
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

lemma walk_transitions_le_boundary : Fintype.card
    (P.pairing.VertexTransition (walkApex n w d c hc f P) (walkSelected n w d c hc f P select)) ≤
    Fintype.card (RadialBoundarySide n w d c hc f P select) := by
  apply P.pairing.vertex_transitions_le_boundary
  · intro x; exact congrArg select (P.faceClass_apply x)
  · exact walk_apex_previous n w d c hc f P
  · exact walk_apex_paired n w d c hc f P
  · exact walk_apex_radial n w d c hc f P
  · exact walk_radial_paired n w d c hc f P

variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma allBoundaryIndex_card : Fintype.card (AllBoundaryIndex n w d c hc f P select hs hm hred hrad) =
    ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).boundary := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natBoundaryIndex_card
    (fun b => indexedFanData n w d c hc f P select b hs hm hred hrad)

/-- The partial-apex error is paid by actual radial boundary sides. No
radial-side accounting identity is supplied as an extra hypothesis. -/
theorem actual_radial_sides :
    (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).boundary) ≤
      Fintype.card (RadialBoundarySide n w d c hc f P select) := by
  rw [← allBoundaryIndex_card n w d c hc f P select hs hm hred hrad]
  exact (Fintype.card_le_of_injective _
    (boundaryTransition_injective n w d c hc f P select hs hm hred hrad)).trans
    (walk_transitions_le_boundary n w d c hc f P select)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTriangleTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma allTriangleIndex_card :
    Fintype.card (AllTriangleIndex n w d c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natTriangleIndex_card
    (fun b => indexedFanData n w d c hc f P select b hs hm hred hrad)

def triangleFace (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) :
    SelectedTriangleFace n w d c hc f P select := by
  refine ⟨P.faceClass (triangleCorner n w d c hc f P select hs hm hred hrad p),
    triangle_selected n w d c hc f P select hs hm hred hrad p,?_⟩
  obtain ⟨g,o,hx⟩ := mark_triangle_corner n w d c hc f P select p.1 p.2.val.1 p.2.val.2 p.2.property
  refine ⟨g,?_⟩
  change walkKind n w d (P.index p.2.val.2.val) = _
  rw [hx]
  rfl

lemma triangleFace_surjective : Function.Surjective
    (triangleFace n w d c hc f P select hs hm hred hrad) := by
  intro F
  obtain ⟨g,hg⟩ := F.property.2
  have ho := P.faceClass_out F.val
  have hg' : walkKind n w d (P.index F.val.out) = .inr (.inl g) := by
    change P.faceKind (P.faceClass F.val.out) = _
    rw [ho]
    exact hg
  obtain ⟨o,i,hi⟩ : ∃ (o : Bool) (i : Fin 3), P.index F.val.out = .inr ⟨.inl g,o,i⟩ := by
    cases h : P.index F.val.out with
    | inl x => rw [h] at hg'; cases hg'
    | inr s =>
      rcases s with ⟨k,o,i⟩
      have hk : k = .inl g := Sum.inr.inj (by simpa only [h,walkKind] using hg')
      subst k
      exact ⟨o,i,rfl⟩
  obtain ⟨y,hy,he⟩ := frozen_side_exists n w d c hc f P hm hi (if o then (0 : Fin 3) else (2 : Fin 3))
  have hface : P.faceClass y = F.val := ((P.faceClass_eq).mpr hy).symm.trans ho
  have hsel : select (P.faceClass y) = true := by rw [hface]; exact F.property.1
  have hstart : start n w (walkLabel n w d (P.index y)) = .inr g.1 := by
    change P.index y = frozenCorner n w d g o at he
    rw [he,frozenCorner_label]
    cases o <;> rfl
  let z := apexInstanceAt n w d c hc f P select g.1 y hsel hstart
  let x : P.Link z.val := ⟨y,rfl⟩
  have hnot : ¬∃ a e, P.index y = .inl (a,e) := by rw [he]; simp
  have hmark : fragmentMark n w d c hc f P select g.1 z x = .triangle := by
    unfold fragmentMark
    rw [dite_eq_left hsel,dite_eq_right hnot]
  refine ⟨⟨g.1,⟨⟨z,x⟩,hmark⟩⟩,?_⟩
  exact Subtype.ext hface

lemma triangleFace_injective (hb : P.NoBigon) : Function.Injective
    (triangleFace n w d c hc f P select hs hm hred hrad) := by
  intro p q he
  apply triangleRawDart_injective n w d c hc f P select hs hm hred hrad
  have hface := congrArg Subtype.val he
  change P.faceClass p.2.val.2.val = P.faceClass q.2.val.2.val at hface
  have hf : P.faceClass (triangleRawDart n w d c hc f P select hs hm hred hrad p) =
      P.faceClass (triangleRawDart n w d c hc f P select hs hm hred hrad q) := by
    simpa only [triangleRawDart,P.faceClass_apply] using hface
  obtain ⟨g,o,hp⟩ := triangle_raw_index n w d c hc f P select hs hm hred hrad p
  obtain ⟨g',o',hq⟩ := triangle_raw_index n w d c hc f P select hs hm hred hrad q
  have hk := congrArg P.faceKind hf
  change walkKind n w d (P.index (triangleRawDart n w d c hc f P select hs hm hred hrad p)) =
    walkKind n w d (P.index (triangleRawDart n w d c hc f P select hs hm hred hrad q)) at hk
  rw [hp,hq] at hk
  have hg : g = g' := Sum.inl.inj (Sum.inr.inj hk)
  apply raw_position_once_per_face n w d c hc f P hs hb hm (P.faceClass_eq.mp hf)
  · rw [hp]; cases o <;> rfl
  · rw [hq]; cases o' <;> rfl
  · rw [hp,hq,hg]; rfl

lemma selectedTriangles_eq (hb : P.NoBigon) :
    Fintype.card (SelectedTriangleFace n w d c hc f P select) =
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles := by
  rw [← allTriangleIndex_card n w d c hc f P select hs hm hred hrad]
  exact (Fintype.card_congr (Equiv.ofBijective _
    ⟨triangleFace_injective n w d c hc f P select hs hm hred hrad hb,
     triangleFace_surjective n w d c hc f P select hs hm hred hrad⟩)).symm

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualFaceCounts
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_weights_top : (∑ a, (actualWeights n w d c hc f P select hs hm hred hrad).top a) =
    actualTopCount n w d c hc f P select := by
  change (∑ a, Fintype.card (KindFace n w d c hc f P select (.inl ((enumTop n w).symm a)))) = _
  exact (Equiv.sum_comp (enumTop n w).symm (fun a => Fintype.card (KindFace n w d c hc f P select (.inl a)))).trans
    (sum_top_count n w d c hc f P select)
lemma actual_weights_square : (∑ q, (actualWeights n w d c hc f P select hs hm hred hrad).square q) =
    actualSquareCount n w d c hc f P select := by
  exact Equiv.sum_comp (enumSquare n w).symm (fun q => Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inl q)))))
lemma actual_weights_six : (∑ q, (actualWeights n w d c hc f P select hs hm hred hrad).six q) =
    actualSixCount n w d c hc f P select := by
  exact Equiv.sum_comp (enumSix n d).symm (fun q => Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inr q)))))
lemma actual_weights_fan : (∑ b, (actualWeights n w d c hc f P select hs hm hred hrad).fan b) =
    ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).weight := by
  exact Equiv.sum_comp (enumFan n w).symm (fun b => (indexedFanData n w d c hc f P select b hs hm hred hrad).weight)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualLayers
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction

namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_top_layer (j : ℕ) :
    Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).TopAt j) ≤
      actualTopCount n w d c hc f P select := by
  rw [← actual_weights_top n w d c hc f P select hs hm hred hrad]
  exact card_layer_le_support _ _ j (fun _ h => h)
lemma actual_square_layer (j : ℕ) :
    Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).SquareAt j) ≤
      actualSquareCount n w d c hc f P select := by
  rw [← actual_weights_square n w d c hc f P select hs hm hred hrad]
  exact card_layer_le_support _ _ j (fun _ h => h)
lemma actual_six_layer (j : ℕ) :
    Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).SixAt j) ≤
      actualSixCount n w d c hc f P select := by
  rw [← actual_weights_six n w d c hc f P select hs hm hred hrad]
  exact card_layer_le_support _ _ j (fun _ h => h)

lemma actual_fan_layer (hb : P.NoBigon) (j : ℕ) :
    Fintype.card ((actualWeights n w d c hc f P select hs hm hred hrad).FanAt j) ≤
      7 * actualTopCount n w d c hc f P select + actualTriangleCount n w d c hc f P select := by
  let D := fun b => indexedFanData n w d c hc f P select b hs hm hred hrad
  have hh := card_layer_le_support (fun b => (actualWeights n w d c hc f P select hs hm hred hrad).fan b)
    (fun b => Fintype.card (SelectedTop n w d c hc f P select ((enumFan n w).symm b)) +
      (D ((enumFan n w).symm b)).triangles) j (fun b hb => (D _).activation_bound hb)
  have he := Equiv.sum_comp (enumFan n w).symm (fun b =>
    Fintype.card (SelectedTop n w d c hc f P select b) + (D b).triangles)
  rw [he,Finset.sum_add_distrib] at hh
  have hslot : (∑ b : Fan n w, Fintype.card (SelectedTop n w d c hc f P select b)) =
      7 * actualTopCount n w d c hc f P select := by
    have h0 := fragment_slots_eq n w d c hc f P select
    simp only [actualTopCount,← Nat.card_eq_fintype_card] at h0 ⊢
    convert h0 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext face
    simp
  rw [hslot] at hh
  have ht : actualTriangleCount n w d c hc f P select = ∑ b, (D b).triangles := by
    have h0 := selectedTriangles_eq n w d c hc f P select hs hm hred hrad hb
    simp only [actualTriangleCount,← Nat.card_eq_fintype_card] at h0 ⊢
    convert h0 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext face
    simp
  rw [← ht] at hh
  exact hh

lemma actual_layer_bounds {M : ℕ} (hb : P.NoBigon) (hM : 8 * actualArea n w d c hc f P select ≤ M) (j : ℕ) :
    let W := actualWeights n w d c hc f P select hs hm hred hrad
    Fintype.card (W.TopAt j) ≤ M ∧ Fintype.card (W.FanAt j) ≤ M ∧
      Fintype.card (W.SquareAt j) ≤ M ∧ Fintype.card (W.SixAt j) ≤ M := by
  have ht := actual_top_layer n w d c hc f P select hs hm hred hrad j
  have hf := actual_fan_layer n w d c hc f P select hs hm hred hrad hb j
  have hq := actual_square_layer n w d c hc f P select hs hm hred hrad j
  have hv := actual_six_layer n w d c hc f P select hs hm hred hrad j
  rw [actual_area_eq n w d c hc f P select] at hM
  dsimp only
  omega

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkPayment
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

variable (hs : P.Simple) (hb : P.NoBigon)
  (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma allPaymentIndex_card :
    Fintype.card (AllPaymentIndex n w d c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).payments := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natPaymentIndex_card
    (fun b => indexedFanData n w d c hc f P select b hs hm hred hrad)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualRawCount
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_raw_account_le (hb : P.NoBigon) :
    Fintype.card (RawAccountIndex n w d c hc f P select hs hm hred hrad) ≤
      Fintype.card (ActualRawSide n w d c hc f P select) := by
  let g : RawAccountIndex n w d c hc f P select hs hm hred hrad → ActualRawSide n w d c hc f P select :=
    fun p => ⟨accountDart n w d c hc f P select hs hm hred hrad p,
      accountDart_raw n w d c hc f P select hs hm hred hrad hb p,
      accountDart_selected n w d c hc f P select hs hm hred hrad p⟩
  exact Fintype.card_le_of_injective g (fun _ _ hh =>
    accountDart_injective n w d c hc f P select hs hm hred hrad hb (congrArg Subtype.val hh))

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualRawAccount
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma decorationSideIndex_card :
    Fintype.card (DecorationSideIndex n w d c hc f P select) =
      4 * actualSquareCount n w d c hc f P select + 6 * actualSixCount n w d c hc f P select := by
  rw [Fintype.card_sigma,Fintype.sum_sum_type]
  simp only [Fintype.card_prod,Fintype.card_fin]
  change (∑ q : Square n w, Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inl q)))) * 4) +
    (∑ q : Six n d, Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inr q)))) * 6) = _
  rw [← Finset.sum_mul,← Finset.sum_mul]
  change actualSquareCount n w d c hc f P select * 4 + actualSixCount n w d c hc f P select * 6 = _
  omega

lemma actual_raw_lower (hb : P.NoBigon) :
    (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).payments) +
      actualTriangleCount n w d c hc f P select + 4 * actualSquareCount n w d c hc f P select +
      6 * actualSixCount n w d c hc f P select ≤ Fintype.card (ActualRawSide n w d c hc f P select) := by
  have hh := actual_raw_account_le n w d c hc f P select hs hm hred hrad hb
  change Fintype.card (AllPaymentIndex n w d c hc f P select hs hm hred hrad ⊕
    (AllTriangleIndex n w d c hc f P select hs hm hred hrad ⊕ DecorationSideIndex n w d c hc f P select)) ≤ _ at hh
  rw [Fintype.card_sum,Fintype.card_sum] at hh
  have hp : Fintype.card (AllPaymentIndex n w d c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).payments := by
    have h0 := allPaymentIndex_card n w d c hc f P select hs hm hred hrad
    simp only [← Nat.card_eq_fintype_card] at h0 ⊢
    convert h0 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext index
    simp
  have ht : Fintype.card (AllTriangleIndex n w d c hc f P select hs hm hred hrad) =
      actualTriangleCount n w d c hc f P select := by
    have h0 := (allTriangleIndex_card n w d c hc f P select hs hm hred hrad).trans
      (selectedTriangles_eq n w d c hc f P select hs hm hred hrad hb).symm
    simpa only [actualTriangleCount,← Nat.card_eq_fintype_card] using h0
  rw [hp,ht,decorationSideIndex_card n w d c hc f P select] at hh
  omega

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTopTurns
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

/-- Actual source-face cardinal bound, not an assumed macro polygon. -/
lemma top_face_apex_card_ge (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart) (hx : P.index x = .inl (a,e)) :
    3 ≤ Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y ∧
      isApex n w (start n w (walkLabel n w d (P.index y))) = true} := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let R := mappedMacroPolygon n w d c hc f P hs hb x a e hx
  let b : Fin R.n ≃ I := (Fintype.equivFin I).symm
  let j (y : I) : MacroGraph.graph.Dart := (same_top_face n w d c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (a,j y) :=
    (same_top_face n w d c hc f P hx y.property).choose_spec
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
      isApex n w (start n w (walkLabel n w d (P.index y))) = true} := fun p =>
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

lemma face_apex_card_ge (hs : P.Simple) (hb : P.NoBigon)
    (F : SelectedTopFace n w d c hc f P select) :
    3 ≤ Fintype.card (FaceApexDart n w d c hc f P select F) := by
  obtain ⟨a,ha⟩ := F.property.2
  have hk : walkKind n w d (P.index F.val.out) = .inl a := by
    change P.faceKind (P.faceClass F.val.out) = _
    rw [P.faceClass_out]; exact ha
  obtain ⟨e,he⟩ : ∃ e, P.index F.val.out = .inl (a,e) := by
    cases ht : P.index F.val.out with
    | inl s =>
      rw [ht] at hk
      exact ⟨s.2,congrArg Sum.inl (Prod.ext (Sum.inl.inj hk) rfl)⟩
    | inr s => rw [ht] at hk; cases hk
  have h := top_face_apex_card_ge n w d c hc f P hs hb F.val.out a e he
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [← P.faceClass_eq,P.faceClass_out]
  exact and_congr eq_comm Iff.rfl

/-- The bound `sum d_z >= 3 T` at the actual selected top faces. The following
apex transport identifies these darts with the indexed fan-turn counts. -/
lemma selected_top_turns_ge (hs : P.Simple) (hb : P.NoBigon) :
    3 * Fintype.card (SelectedTopFace n w d c hc f P select) ≤
      Fintype.card (TopTurnDart n w d c hc f P select) := by
  let I := Σ F : SelectedTopFace n w d c hc f P select, FaceApexDart n w d c hc f P select F
  let g : I → TopTurnDart n w d c hc f P select := fun p => ⟨p.2.val,by
    refine ⟨?_,p.2.property.2,?_⟩
    · rw [p.2.property.1]; exact p.1.property.1
    · have hk : walkKind n w d (P.index p.2.val) = .inl (faceOccurrence n w d c hc f P select p.1) := by
        change P.faceKind (P.faceClass p.2.val) = _
        rw [p.2.property.1]; exact faceOccurrence_kind n w d c hc f P select p.1
      rw [hk]; rfl⟩
  have hg : Function.Injective g := by
    rintro ⟨F,x⟩ ⟨G,y⟩ h
    have hv : x.val = y.val := congrArg Subtype.val h
    have hf : F = G := Subtype.ext (x.property.1.symm.trans ((congrArg P.faceClass hv).trans y.property.1))
    subst G
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun F _ => face_apex_card_ge n w d c hc f P select hs hb F)
  have hh' : 3 * Fintype.card (SelectedTopFace n w d c hc f P select) ≤ Fintype.card I := by
    rw [Fintype.card_sigma]
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm] using hh
  exact hh'.trans (Fintype.card_le_of_injective g hg)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTurnTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)


variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma allTurnIndex_card :
    Fintype.card (AllTurnIndex n w d c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).turns := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natTurnIndex_card
    (fun b => indexedFanData n w d c hc f P select b hs hm hred hrad)

/-- All selected top apex darts are really fan turns. Together with the
actual macro cycle bound this supplies the source `sum d_z >= 3T`. -/
theorem actual_turns_ge (hb : P.NoBigon) :
    3 * Fintype.card (SelectedTopFace n w d c hc f P select) ≤
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).turns := by
  have h1 := selected_top_turns_ge n w d c hc f P select hs hb
  have h2 := Fintype.card_le_of_surjective _
    (allTurnDart_surjective n w d c hc f P select hs hm hred hrad)
  exact h1.trans (h2.trans_eq (allTurnIndex_card n w d c hc f P select hs hm hred hrad))

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkApexAggregate
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

/-- The summed apex estimate is now a theorem about the actual selected
mixed-picture faces. All nominal slots, turns, partial links and radial
boundary sides are extracted from the picture itself. -/
theorem actual_nominal_apex (hb : P.NoBigon) :
    3 * (Fintype.card (SelectedTopFace n w d c hc f P select) : ℝ) +
      2 * ((∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).weight : ℝ)) -
        7 * Fintype.card (SelectedTopFace n w d c hc f P select)) ≤
    ((∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).triangles : ℝ)) +
      ∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).payments : ℝ))/2 +
      2 * ∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).partialCount : ℝ) := by
  have ha := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => (indexedFanData n w d c hc f P select b hs hm hred hrad).apex_bound)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum] at ha
  have ht : 3 * (Fintype.card (SelectedTopFace n w d c hc f P select) : ℝ) ≤
      ∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).turns : ℝ) := by
    exact_mod_cast actual_turns_ge n w d c hc f P select hs hm hred hrad hb
  have hslot : (∑ b : Fan n w, (Fintype.card (SelectedTop n w d c hc f P select b) : ℝ)) =
      7 * Fintype.card (SelectedTopFace n w d c hc f P select) := by
    exact_mod_cast fragment_slots_eq n w d c hc f P select
  rw [hslot] at ha
  linarith

lemma actual_triangles_le :
    (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles) ≤
      5 * ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).weight := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles_le)
  simpa only [← Finset.mul_sum] using h

lemma actual_partial_le :
    2 * (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).partialCount) ≤
      Fintype.card (RadialBoundarySide n w d c hc f P select) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => (indexedFanData n w d c hc f P select b hs hm hred hrad).partial_le_boundary)
  have h' : 2 * (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).partialCount) ≤
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).boundary := by
    simpa only [← Finset.mul_sum] using h
  exact h'.trans (actual_radial_sides n w d c hc f P select hs hm hred hrad)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualFragment
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
open IncidenceTemplate.Occurrences.Shape

namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_contacts_le {M : ℕ} {α β δ : ℝ}
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (hM : 8 * actualArea n w d c hc f P select ≤ M) :
    (Fintype.card (ActualContact n w d c hc f P select) : ℝ) ≤
      ((3-β)-7*(2-α)) * actualTopCount n w d c hc f P select +
      (2-α) * actualFanWeight n w d c hc f P select hs hm hred hrad +
      (2-δ) * actualSquareCount n w d c hc f P select +
      (3-δ) * actualSixCount n w d c hc f P select := by
  have hl := actual_layer_bounds n w d c hc f P select hs hm hred hrad hb hM
  have hh := actual_contact_bound n w d c hc f P select hs hm hred hrad hgood hb
    (fun j => (hl j).1) (fun j => (hl j).2.1) (fun j => (hl j).2.2.1) (fun j => (hl j).2.2.2)
  dsimp only at hh
  have ht : (∑ a, ((actualWeights n w d c hc f P select hs hm hred hrad).top a : ℝ)) =
      actualTopCount n w d c hc f P select := by
    exact_mod_cast actual_weights_top n w d c hc f P select hs hm hred hrad
  have hf : (∑ b, ((actualWeights n w d c hc f P select hs hm hred hrad).fan b : ℝ)) =
      actualFanWeight n w d c hc f P select hs hm hred hrad := by
    exact_mod_cast actual_weights_fan n w d c hc f P select hs hm hred hrad
  have hq : (∑ q, ((actualWeights n w d c hc f P select hs hm hred hrad).square q : ℝ)) =
      actualSquareCount n w d c hc f P select := by
    exact_mod_cast actual_weights_square n w d c hc f P select hs hm hred hrad
  have hv : (∑ q, ((actualWeights n w d c hc f P select hs hm hred hrad).six q : ℝ)) =
      actualSixCount n w d c hc f P select := by
    exact_mod_cast actual_weights_six n w d c hc f P select hs hm hred hrad
  rwa [ht,hf,hq,hv] at hh

include hs hm hred hrad in
/-- The full fragment estimate for the literal normalized mixed
picture, for ANY selected faces. All counts, weights, normal fan links,
indexed coincidences and size bounds are produced, not assumed. -/
theorem actual_fragment_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (hM : 8 * actualArea n w d c hc f P select ≤ M) :
    defectConstant α β δ * actualArea n w d c hc f P select ≤
      actualBoundary n w d c hc f P select := by
  have hI := actual_contacts_le n w d c hc f P select hs hm hred hrad hgood hb hM
  have hA := actual_nominal_apex n w d c hc f P select hs hm hred hrad hb
  have hQ := actual_triangles_le n w d c hc f P select hs hm hred hrad
  have hJ := actual_partial_le n w d c hc f P select hs hm hred hrad
  have hR := actual_raw_lower n w d c hc f P select hs hm hred hrad hb
  have hC := actual_boundary_contacts_eq n w d c hc f P select
  rw [← hC] at hR
  have hT := selectedTriangles_eq n w d c hc f P select hs hm hred hrad hb
  have hu : @Finset.univ (Fan n w) (Subtype.fintype _) =
      @Finset.univ (Fan n w) inferInstance := by ext x; simp
  try simp only [hu] at hA hQ hJ hT
  have hA' : 3*(actualTopCount n w d c hc f P select : ℝ) +
      2*((actualFanWeight n w d c hc f P select hs hm hred hrad : ℝ)-7*actualTopCount n w d c hc f P select) ≤
      ((actualTriangleCount n w d c hc f P select : ℝ)+actualPayments n w d c hc f P select hs hm hred hrad)/2 +
      2*actualPartialCount n w d c hc f P select hs hm hred hrad := by
    have ht' : (∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).triangles : ℝ)) =
        actualTriangleCount n w d c hc f P select := by
      have ht0 : (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles) =
          actualTriangleCount n w d c hc f P select := by
        simpa only [actualTriangleCount,← Nat.card_eq_fintype_card] using hT.symm
      exact_mod_cast ht0
    simpa only [actualTopCount,actualFanWeight,actualPayments,actualPartialCount,Nat.cast_sum,ht',← Nat.card_eq_fintype_card] using hA
  have hQ' : actualTriangleCount n w d c hc f P select ≤
      5 * actualFanWeight n w d c hc f P select hs hm hred hrad := by
    change Fintype.card (SelectedTriangleFace n w d c hc f P select) ≤ _
    rw [hT]
    simpa only [actualFanWeight] using hQ
  change 2 * actualPartialCount n w d c hc f P select hs hm hred hrad ≤ _ at hJ
  rw [actual_area_eq n w d c hc f P select]
  exact fragment_numeric_bound ha _ _ _ _ _ _ _ _ _ _ hI hA' hQ' hJ hR

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualPartition
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

variable {I : Type*} [Fintype I] (part : P.Face → I)

omit [Fintype I] in
lemma part_area (i : I) : actualArea n w d c hc f P (partSelect n w d c hc f P part i) =
    Fintype.card {F : P.Face // part F = i} := by
  apply Fintype.card_congr (Equiv.subtypeEquivRight _)
  intro F
  simp only [partSelect,decide_eq_true_eq]

omit [Fintype I] in
lemma part_boundary (i : I) : actualBoundary n w d c hc f P (partSelect n w d c hc f P part i) =
    Fintype.card (PartBoundary P.pairing (part ∘ P.faceClass) i) := by
  rw [actual_boundary_card]
  apply Fintype.card_congr (Equiv.subtypeEquivRight _)
  intro x
  simp [partSelect,Function.comp_apply]

lemma sum_part_area : (∑ i, actualArea n w d c hc f P (partSelect n w d c hc f P part i)) =
    Fintype.card P.Face := by
  simp only [part_area]
  exact sum_part_sizes part

lemma sum_part_boundary : (∑ i, actualBoundary n w d c hc f P (partSelect n w d c hc f P part i)) =
    2 * Fintype.card (CutContact P.pairing (part ∘ P.faceClass)) := by
  simp only [part_boundary]
  exact (PictureSwitch.sum_part_boundary P.pairing (part ∘ P.faceClass)).trans
    (cut_sides_twice P.pairing (part ∘ P.faceClass))

/-- Summing fragment bounds over a partition of faces bounds the total defect
by twice the number of cut contacts. -/
theorem actual_partition_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hM : ∀ i, 8 * Fintype.card {F : P.Face // part F = i} ≤ M) :
    defectConstant α β δ * Fintype.card P.Face ≤
      2 * (Fintype.card (CutContact P.pairing (part ∘ P.faceClass)) : ℝ) := by
  have hi (i : I) := actual_fragment_bound n w d c hc f P (partSelect n w d c hc f P part i)
    hs hm hred hrad ha hgood hb (by rw [part_area]; exact hM i)
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hi i)
  rw [← Finset.mul_sum,← Nat.cast_sum,← Nat.cast_sum,sum_part_area,sum_part_boundary] at h
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualDegree
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

/-- With a small sparse partition, the closed normal picture is empty. -/
theorem normal_empty_of_sparse_partition {I : Type*} [Fintype I] (part : P.Face → I)
    {K : ℕ} {α β δ η : ℝ} (ha : 0 < α) (hbeta : 7*α < β) (hd : 0 < δ)
    (heta : 2*η < defectConstant α β δ)
    (hgood : Occurrences.GoodUpTo (8*K) α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hsize : ∀ i, Fintype.card {F : P.Face // part F = i} ≤ K)
    (hcut : (Fintype.card (CutContact P.pairing (part ∘ P.faceClass)) : ℝ) ≤ η*Fintype.card P.Face) :
    IsEmpty P.Dart := by
  have halpha : 0 ≤ α := by
    have hdefect := defectConstant_pos ha hbeta hd
    have hbound : defectConstant α β δ ≤ α / 5 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hdefect, hbound]
  have h := actual_partition_bound n w d c hc f P part halpha hgood hs hm hred hrad hb
    (fun i => Nat.mul_le_mul_left 8 (hsize i))
  simp only [← Nat.card_eq_fintype_card] at h hcut
  have hz : (Nat.card P.Face : ℝ) = 0 := by
    have hnonneg := Nat.cast_nonneg (α := ℝ) (Nat.card P.Face)
    nlinarith
  have hf : Fintype.card P.Face = 0 := by rw [← Nat.card_eq_fintype_card]; exact_mod_cast hz
  have : IsEmpty P.Face := Fintype.card_eq_zero_iff.mp hf
  exact ⟨fun x => isEmptyElim (P.faceClass x)⟩

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConePresentationGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

/-- No round trip or presentation-equivalence assumption: every original
null letter word is an actual cone-polygon nullword. -/
theorem nullWord_to_polygon (z : List (Alphabet n))
    (hz : PresentedGroup.mk (Relator n w d) (FreeGroup.mk z) = 1) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)
      (FreeGroup.mk (z.map (letterDart n w))) = 1 := by
  have hh := relator_normalClosure_le n w d (PresentedGroup.mk_eq_one_iff.mp hz)
  change freeComparison n w d (FreeGroup.mk z) = 1 at hh
  rwa [freeComparison_word] at hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeFullNormal
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

/-- Full actual mixed-cell normal form, with literal complete frozen face
maps as the only raw indexing condition. Every finite genus-zero input is
normalized by the checked surgeries, without assuming any fan link data,
contact bound, or filling estimate. -/
theorem normalizedPicture (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f)) :
    ∃ Q : WalkPicture.{u} (walkTarget n w d c hc f),
      Nonempty (P.Survives Q) ∧ Q.FrozenMapped (walkFrozenTarget n w d c hc f) ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective (isApex n w) ∧
      Q.chain = P.chain ∧
      ∀ (hs : Q.Simple) (hb : Q.NoBigon) (x : Q.Dart) (a : Top n w)
        (e : MacroGraph.graph.Dart) (hx : Q.index x = .inl (a,e)),
        Fintype.card {y : Q.Dart // Q.pairing.face.SameCycle x y} ≤ 15 ∧
          3 ≤ (mappedMacroPolygon n w d c hc f Q hs hb x a e hx).points.card := by
  obtain ⟨Q,hr,hm,hs,hb,hred,hrad,hchain⟩ := P.normalize_full
    (walkFrozenTarget n w d c hc f) hm (isApex n w)
    (fun s => radial n w (walkLabel n w d s))
  refine ⟨Q,hr,hm,hs,hb,hred,hrad,hchain,?_⟩
  intro hs hb x a e hx
  let B := mappedMacroPolygon n w d c hc f Q hs hb x a e hx
  constructor
  · exact B.perimeter_le
  · apply B.points_ge
    change 0 < Fintype.card {y : Q.Dart // Q.pairing.face.SameCycle x y}
    exact Fintype.card_pos_iff.mpr ⟨⟨x,SameCycle.rfl⟩⟩
end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GlobalClosedPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
universe u v

/-- Unbounded normal spherical-picture vanishing. The size cutoff is in the
rank EVENT, not in the picture: the theorem applies to every finite normal
picture for that realization, without any assumed separator interface. -/
theorem uniform_normal_picture_empty {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ K : ℕ, 0 < K ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo (8*K) α β δ (Sum.elim w d) →
      ∀ (A : Type v) [AddCommGroup A]
        (c : Top n w → MacroGraph.graph.Dart → A)
        (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
        (P : WalkPicture.{u} (walkTarget n w d c hc f)),
        P.Simple → P.FrozenMapped (walkFrozenTarget n w d c hc f) →
        P.FullyReduced → P.RadialInjective (isApex n w) → P.NoBigon → IsEmpty P.Dart := by
  have hk := defectConstant_pos ha hb hd
  obtain ⟨K,hK,hh⟩ := uniform_genusZero_face_partition.{u} 15
    (defectConstant α β δ / 4) (div_pos hk (by norm_num))
  refine ⟨K,hK,?_⟩
  intro n w d hgood A _ c hc f P hs hm hred hrad hbig
  let U : Finset P.Face := Finset.univ
  have hdegree (F : P.Face) (_ : F ∈ U) :
      Nat.card {x : P.Dart // P.faceClass x = F} ≤ 15 := by
    rw [Nat.card_eq_fintype_card]
    exact actual_face_degree_le n w d c hc f P hs hbig hm F
  obtain ⟨I,inst,part,hsize,hcut⟩ := hh P.Dart P.pairing P.genusZero U hdegree
  let := inst
  apply normal_empty_of_sparse_partition n w d c hc f P part ha hb hd
    (η := defectConstant α β δ / 4) (by linarith) hgood hs hm hred hrad hbig
  · intro i
    simpa only [U,← Fintype.card_subtype] using hsize i
  · simp only [← Nat.card_eq_fintype_card] at hcut ⊢
    simpa only [U,Finset.mem_univ,Finset.card_univ,RelativeCutContact,CutContact,
      true_and,WalkPicture.faceClass,Function.comp_apply,← Nat.card_eq_fintype_card] using hcut

/-- Every literal genus-zero closed picture carries zero chain, after the
proved finite normal-form surgeries. This is not yet the topological theorem
that a nonzero Hurewicz cycle admits such a picture. -/
theorem uniform_closed_picture_chain_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (A : Type v) [AddCommGroup A]
        (c : Top n w → MacroGraph.graph.Dart → A)
        (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
        (P : WalkPicture.{u} (walkTarget n w d c hc f)),
        P.FrozenMapped (walkFrozenTarget n w d c hc f) → P.chain = 0 := by
  obtain ⟨K,hK,hh⟩ := uniform_normal_picture_empty.{u,v} ha hb hd
  refine ⟨8*K,Nat.mul_pos (by decide) hK,?_⟩
  intro n w d hgood A _ c hc f P hm
  obtain ⟨Q,_,hmQ,hsQ,hbQ,hrQ,hradQ,hchain,_⟩ := normalizedPicture n w d c hc f P hm
  have : IsEmpty Q.Dart := hh n w d hgood A c hc f Q hsQ hmQ hrQ hradQ hbQ
  rw [← hchain]
  simp only [WalkPicture.chain,Finset.univ_eq_empty,Finset.sum_empty]

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LiftedClosedPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
universe u v z

/-- Normal-form vanishing holds in every regular voltage cover, with each
signed lifted cell retained separately. This is stronger than vanishing of
the projected base-cell chain. -/
theorem uniform_lifted_picture_chain_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (G : Type v) [Group G] (B : Type z) [AddCommMonoid B]
        (H : WalkCellCover (indexingTarget n w d) G) (weight : G → WalkStep n w d → B)
        (hw : ∀ g s, weight g s + weight g (walkOpposite n w d s) = 0)
        (P : WalkPicture.{u} (H.target weight (fun g s _ => hw g s))),
        P.FrozenMapped (H.frozenTarget weight (fun g s _ => hw g s)
          (indexingFrozenTarget n w d) hw) → P.chain = 0 := by
  obtain ⟨K,hK,hh⟩ := uniform_normal_picture_empty.{u,0} ha hb hd
  refine ⟨8*K,Nat.mul_pos (by decide) hK,?_⟩
  intro n w d hgood G _ B _ H weight hw P hm
  let T := H.target weight (fun g s _ => hw g s)
  let F := H.frozenTarget weight (fun g s _ => hw g s) (indexingFrozenTarget n w d) hw
  obtain ⟨Q,_,hmQ,hsQ,hbQ,hrQ,hradQ,hchain⟩ :=
    P.normalize_full F hm (isApex n w ∘ Prod.snd) (by
      intro s hs
      exact radial n w (walkLabel n w d s.2) hs)
  let R := H.forget weight (fun g s _ => hw g s) Q
  have hR : IsEmpty R.Dart := hh n w d hgood ℤ (fun _ _ => 0) (by simp) (fun _ => 0) R
    (H.forget_simple _ _ Q hsQ)
    (H.forget_frozenMapped _ _ Q (indexingFrozenTarget n w d) hw hmQ)
    (H.forget_fullyReduced _ _ Q hrQ)
    (H.forget_radialInjective _ _ Q (isApex n w) hradQ)
    (H.forget_noBigon _ _ Q hbQ)
  have : IsEmpty Q.Dart := hR
  rw [← hchain]
  simp only [WalkPicture.chain,Finset.univ_eq_empty,Finset.sum_empty]

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualLiftedChain
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
universe u v z
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type v} [Group G] (voltage : Dart n w → G)
  (hv : ∀ e, voltage (rev n w e) = (voltage e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => voltage (side n w d a i))).prod = 1)
variable {A : Type z} [AddCommGroup A]
  (c : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, c g a e.symm = -c g a e) (f : G → FrozenCell n w d → A)

def liftedWalkTarget :=
  (actualCellCover n w d voltage hv hcell).target
    (fun g => walkWeight n w d (c g) (f g))
    (fun g s _ => walkWeight_opposite n w d (c g) (hc g) (f g) s)

def liftedFrozenTarget : FrozenTarget (liftedWalkTarget n w d voltage hv hcell c hc f) :=
  (actualCellCover n w d voltage hv hcell).frozenTarget
    (fun g => walkWeight n w d (c g) (f g))
    (fun g s _ => walkWeight_opposite n w d (c g) (hc g) (f g) s)
    (indexingFrozenTarget n w d)
    (fun g s => walkWeight_opposite n w d (c g) (hc g) (f g) s)

/-- Source closed-picture conclusion with independent signed coefficients for
EACH lift of every elementary cone triangle and frozen cell, and actual
prefix-product and cone-route coordinates. The cutoff is selected before
the realization, deck group, voltage and coefficients. -/
theorem uniform_actual_lifted_chain_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (G : Type v) [Group G] (A : Type z) [AddCommGroup A]
        (voltage : Dart n w → G) (hv : ∀ e, voltage (rev n w e) = (voltage e)⁻¹)
        (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => voltage (side n w d a i))).prod = 1)
        (c : G → Top n w → MacroGraph.graph.Dart → A)
        (hc : ∀ g a e, c g a e.symm = -c g a e) (f : G → FrozenCell n w d → A)
        (P : WalkPicture.{u} (liftedWalkTarget n w d voltage hv hcell c hc f)),
        P.FrozenMapped (liftedFrozenTarget n w d voltage hv hcell c hc f) → P.chain = 0 := by
  obtain ⟨M,hM,hh⟩ := uniform_lifted_picture_chain_zero.{u,v,z} ha hb hd
  refine ⟨M,hM,?_⟩
  intro n w d hgood G _ A _ voltage hv hcell c hc f P hm
  exact hh n w d hgood G A (actualCellCover n w d voltage hv hcell)
    (fun g => walkWeight n w d (c g) (f g))
    (fun g s => walkWeight_opposite n w d (c g) (hc g) (f g) s) P hm

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ProtectedNormal
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

variable {P}

variable (P)
lemma cancel_frozen_protected (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (keep : S → Prop) (hu : P.Unopposed keep)
    (a : P.Dart) (ha : T.free (T.kind (P.index a)) = false)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a)) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Preserves keep Q) ∧ Q.FrozenMapped B ∧
      Fintype.card Q.Dart < Fintype.card P.Dart ∧ Q.chain = P.chain := by
  let a' : P.FrozenDart := ⟨a,ha⟩
  let I := {x : P.FrozenDart // P.frozenFace.SameCycle a' x}
  obtain ⟨q,v,hF,hv,hmap⟩ := P.frozen_opposite_faces B hm a (P.pairing.edge a) ha hop
  let i₀ : I := ⟨a',SameCycle.rfl⟩
  obtain ⟨R,hRG,hRM,hRF,hRC,hRW,hRchain⟩ := P.pairing.cancel_mapped_dipole hF i₀ hv.symm
    P.respects P.genusZero T.rev_rev
    (fun i => by change T.label (P.index (v i)) = _; rw [hmap,T.opposite_label]; rfl)
    (fun _ : P.Dart => (0 : ℤ)) (fun _ => rfl) (by simp)
  let Q : WalkPicture.{u} T := {
    Dart := {x : P.Dart // ¬ PictureMap.InDipole (fun y : I => y.val.val) v x}
    pairing := R
    index := P.index ∘ Subtype.val
    closed := by
      intro x
      change T.front (P.index (R.face x).val) = T.back (P.index x.val)
      rw [hRF]
      exact P.closed x.val
    kind := by
      intro x
      change T.kind (P.index (R.face x).val) = T.kind (P.index x.val)
      rw [hRF]
      exact P.kind x.val
    paired := hRM.2
    genusZero := hRG }
  have hret : P.Preserves keep Q := {
    map := Subtype.val
    injective := Subtype.val_injective
    index := fun _ => rfl
    face := fun x _ => hRF x
    complete := by
      intro x hx
      refine ⟨⟨x,?_⟩,rfl⟩
      rintro (⟨i,hi⟩ | ⟨i,hi⟩)
      · subst x
        exact hu i.val.val (v i) hx (hmap i)
      · subst x
        apply hu (v i) i.val.val hx
        rw [hmap,← B.reverse_eq,← B.reverse_eq]
        have h := congrArg (fun p : Perm S => p (P.index i.val.val)) B.reverse_sq
        exact h.symm }
  refine ⟨Q,⟨hret⟩,hret.toSurvives.frozenMapped P B hm,?_,?_⟩
  · exact Fintype.card_subtype_lt (x := a) (by
      intro hh
      exact hh (Or.inl ⟨i₀,rfl⟩))
  · change (∑ x : {x : P.Dart // ¬ PictureMap.InDipole (fun y : I => y.val.val) v x},
        T.weight (P.index x.val)) = ∑ x : P.Dart, T.weight (P.index x)
    apply PictureMap.sum_not_inDipole hF (T.weight ∘ P.index)
    intro i
    change T.weight (P.index i.val.val) + T.weight (P.index (v i)) = 0
    rw [hmap,← B.reverse_eq]
    exact B.opposite_weight _

/-- Relative mixed normal form. Every protected frozen side, with its exact
cyclic successor and index, survives. In particular the operation does not
turn an exterior null-word into a fictitious target relator. -/
theorem normalize_protected (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (keep : S → Prop) (hk : ∀ s, keep s → T.free (T.kind s) = false)
    (hu : P.Unopposed keep) (apex : V → Bool)
    (hr : ∀ s, apex (T.start (T.label s)) = true →
      apex (T.start (T.rev (T.label s))) = false) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Preserves keep Q) ∧ Q.FrozenMapped B ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
      Q.chain = P.chain := by
  have produce : ∀ n, ∀ P : WalkPicture.{u} T, Fintype.card P.Dart = n →
      P.FrozenMapped B → P.Unopposed keep →
      ∃ Q : WalkPicture.{u} T, Nonempty (P.Preserves keep Q) ∧ Q.FrozenMapped B ∧
        Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
        Q.chain = P.chain := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn hm hu
      obtain ⟨P',⟨hret⟩,hs,hnb,hred,hrad,hc⟩ := P.normalize_radial apex hr
      let hsur : P.Preserves keep P' :=
        ⟨hret.survives,fun x hx => hret.complete x (hk _ hx)⟩
      have hm' := hsur.toSurvives.frozenMapped P B hm
      have hu' := hsur.toSurvives.unopposed hu
      by_cases hf : P'.FullyReduced
      · exact ⟨P',⟨hsur⟩,hm',hs,hnb,hf,hrad,hc⟩
      · obtain ⟨a,ha⟩ := not_forall.mp hf
        have hop : P'.index (P'.pairing.edge a) = T.opposite (P'.index a) := not_not.mp ha
        have hfree : T.free (T.kind (P'.index a)) = false := by
          cases hb : T.free (T.kind (P'.index a)) with
          | false => rfl
          | true => exact False.elim (hred a hb hop)
        obtain ⟨P₀,⟨hcan⟩,hm₀,hsmall,hchain⟩ := P'.cancel_frozen_protected B hm' keep hu' a hfree hop
        have hsmall' : Fintype.card P₀.Dart < n := by
          apply lt_of_lt_of_le hsmall
          rw [← hn]
          exact Fintype.card_le_of_injective _ hret.injective
        obtain ⟨Q,⟨hq⟩,hqm,hqs,hqb,hqr,hqd,hqc⟩ :=
          ih _ hsmall' P₀ rfl hm₀ (hcan.toSurvives.unopposed hu')
        exact ⟨Q,⟨hsur.trans (hcan.trans hq)⟩,hqm,hqs,hqb,hqr,hqd,hqc.trans (hchain.trans hc)⟩
  exact produce (Fintype.card P.Dart) P rfl hm hu

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ExteriorTarget
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex
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

lemma exterior_frozen (s) (hs : T.isExterior ell hell word closed s) :
    (T.withExterior ell hell word closed).free ((T.withExterior ell hell word closed).kind s) = false := by
  rcases s with s | s
  · exact False.elim hs
  · rfl

lemma exterior_unopposed (P : WalkPicture.{u} (T.withExterior ell hell word closed))
    (hp : ∀ x s, P.index x = .inr s → s.2.1 = true) :
    P.Unopposed (T.isExterior ell hell word closed) := by
  intro x y hx he
  cases hxi : P.index x with
  | inl s => rw [hxi] at hx; exact hx
  | inr s =>
    have hs := hp x s hxi
    rw [hxi] at he
    change P.index y = .inr ((T.exteriorBoundary ell hell word closed).opposite s) at he
    have ht := hp y _ he
    change (!s.2.1) = true at ht
    rw [hs] at ht
    cases ht

/-- Normalization with the literal outside word preserved side-for-side. -/
theorem normalize_exterior (P : WalkPicture.{u} (T.withExterior ell hell word closed))
    (hm : P.FrozenMapped (T.exteriorFrozen ell hell word closed B))
    (hp : ∀ x s, P.index x = .inr s → s.2.1 = true)
    (apex : V → Bool)
    (hr : ∀ l, apex (T.start l) = true → apex (T.start (T.rev l)) = false) :
    ∃ Q : WalkPicture.{u} (T.withExterior ell hell word closed),
      Nonempty (P.Preserves (T.isExterior ell hell word closed) Q) ∧
      Q.FrozenMapped (T.exteriorFrozen ell hell word closed B) ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
      Q.chain = P.chain := by
  exact P.normalize_protected _ hm _ (T.exterior_frozen ell hell word closed)
    (T.exterior_unopposed ell hell word closed P hp) apex (fun s => hr _)

end WalkCellTarget
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureAppend
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section

namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {u v : Word A}
namespace WordPicture
variable (P : WordPicture R u) (Q : WordPicture R v)

/-- Literal concatenation by a genus-zero connected sum at exterior corners. -/
def appendNonempty (hp : P.outside ≠ []) (hq : Q.outside ≠ []) : WordPicture R (u++v) where
  Dart := P.Dart ⊕ Q.Dart
  pairing := (P.pairing.sum Q.pairing).splice
    (Sum.inl (P.outside.getLast hp)) (Sum.inr (Q.outside.getLast hq))
  genusZero := (P.pairing.sum Q.pairing).splice_genusZero
    (P.pairing.sum_genusZero Q.pairing P.genusZero Q.genusZero) _ _
    (P.pairing.sum_not_components Q.pairing _ _)
  label := Sum.elim P.label Q.label
  paired := by
    intro x; cases x with
    | inl x => exact P.paired x
    | inr x => exact Q.paired x
  outside := P.outside.map Sum.inl ++ Q.outside.map Sum.inr
  boundary := by
    have hp' : P.outside.map (Sum.inl (β := Q.Dart)) ≠ [] := by simpa using hp
    have hq' : Q.outside.map (Sum.inr (α := P.Dart)) ≠ [] := by simpa using hq
    have h := IsBoundary.splice_nonempty
      (P.boundary.map (g := (P.pairing.sum Q.pairing).face) (Sum.inl (β := Q.Dart)) Sum.inl_injective (fun _ => rfl))
      (Q.boundary.map (g := (P.pairing.sum Q.pairing).face) (Sum.inr (α := P.Dart)) Sum.inr_injective (fun _ => rfl))
      hp' hq' (by simp only [List.mem_map]; rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩; cases he)
    simpa only [List.getLast_map,PictureMap.splice] using h
  word := by simp only [List.map_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr,P.word,Q.word]
  interior := by
    intro z hz
    cases z with
    | inl x =>
      have hx : x ∉ P.outside := by intro hx; exact hz (List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩))
      obtain ⟨xs,hxs,hxm,hr⟩ := P.interior x hx
      have hdis : ∀ a ∈ xs, a ∉ P.outside := by
        intro a ha hoa
        exact hx (P.boundary.mem_of_sameCycle hoa (hxs.sameCycle ha hxm))
      refine ⟨xs.map Sum.inl,?_,List.mem_map.mpr ⟨x,hxm,rfl⟩,?_⟩
      · exact (hxs.map (Sum.inl (β := Q.Dart)) Sum.inl_injective (fun _ => rfl)).splice_away
          (by simp only [List.mem_map]; rintro ⟨y,hy,he⟩; exact hdis y hy (Sum.inl.inj he ▸ List.getLast_mem hp))
          (by simp)
      · simpa only [List.map_map,Function.comp_def,Sum.elim_inl] using hr
    | inr x =>
      have hx : x ∉ Q.outside := by intro hx; exact hz (List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩))
      obtain ⟨xs,hxs,hxm,hr⟩ := Q.interior x hx
      have hdis : ∀ a ∈ xs, a ∉ Q.outside := by
        intro a ha hoa
        exact hx (Q.boundary.mem_of_sameCycle hoa (hxs.sameCycle ha hxm))
      refine ⟨xs.map Sum.inr,?_,List.mem_map.mpr ⟨x,hxm,rfl⟩,?_⟩
      · exact (hxs.map (Sum.inr (α := P.Dart)) Sum.inr_injective (fun _ => rfl)).splice_away
          (by simp)
          (by simp only [List.mem_map]; rintro ⟨y,hy,he⟩; exact hdis y hy (Sum.inr.inj he ▸ List.getLast_mem hq))
      · simpa only [List.map_map,Function.comp_def,Sum.elim_inr] using hr

def append : WordPicture R (u++v) := by
  by_cases hp : P.outside = []
  · have hu : u = [] := by rw [← P.word,hp]; rfl
    simpa only [hu,List.nil_append] using Q
  by_cases hq : Q.outside = []
  · have hv : v = [] := by rw [← Q.word,hq]; rfl
    simpa only [hv,List.append_nil] using P
  exact P.appendNonempty Q hp hq
end WordPicture
end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureExist
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section

namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
namespace WordPicture
variable (P : WordPicture R w)

def conjugateLetter (a : A × Bool) : WordPicture R (a::(w++[invLetter a])) := by
  have P' := (P.append (freePair R (invLetter a))).rotate (w.length+1)
  have he : (w++[invLetter a,invLetter (invLetter a)]).rotate (w.length+1) =
      a::(w++[invLetter a]) := by
    rw [invLetter_invLetter]
    have hh := List.rotate_append_length_eq (w++[invLetter a]) [a]
    simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton] using hh
  rw [he] at P'
  exact P'

def conjugate (q : Word A) : WordPicture R (q++w++FreeGroup.invRev q) := by
  induction q with
  | nil => simpa using P
  | cons a q ih =>
    have h := ih.conjugateLetter a
    rw [FreeGroup.invRev_cons,show FreeGroup.invRev [a] = [invLetter a] from rfl]
    simpa only [List.cons_append,List.append_assoc] using h
end WordPicture

/-- Elements represented by actual finite genus-zero diagrams. The subgroup
and its normality are proved by gluing, reflecting and attaching a whisker. -/
def pictureSubgroup (R : Set (Word A)) : Subgroup (FreeGroup A) where
  carrier g := ∃ w, FreeGroup.mk w = g ∧ Nonempty (WordPicture R w)
  one_mem' := ⟨[],rfl,⟨WordPicture.empty R⟩⟩
  mul_mem' := by
    rintro _ _ ⟨u,rfl,⟨P⟩⟩ ⟨v,rfl,⟨Q⟩⟩
    exact ⟨u++v,rfl,⟨P.append Q⟩⟩
  inv_mem' := by
    rintro _ ⟨u,rfl,⟨P⟩⟩
    exact ⟨FreeGroup.invRev u,rfl,⟨P.mirror⟩⟩

instance instNormalFreeGroupPictureSubgroup (R : Set (Word A)) : (pictureSubgroup R).Normal where
  conj_mem := by
    rintro _ ⟨u,rfl,⟨P⟩⟩ g
    obtain ⟨q,rfl⟩ := Quot.exists_rep g
    exact ⟨q++u++FreeGroup.invRev q,rfl,⟨P.conjugate q⟩⟩

/-- Van Kampen realization at the freely represented boundary level: every
null element has an actual finite genus-zero side-pairing with only the
specified relator faces. The next literal-boundary step is free folding. -/
theorem picture_existence {R : Set (Word A)} (w : Word A)
    (h : PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk w) = 1) :
    ∃ v, FreeGroup.mk v = FreeGroup.mk w ∧ Nonempty (WordPicture R v) := by
  apply (Subgroup.normalClosure_le_normal (N := pictureSubgroup R) ?_) (PresentedGroup.mk_eq_one_iff.mp h)
  rintro _ ⟨v,hv,rfl⟩
  exact ⟨v,rfl,WordPicture.of_relator hv⟩

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureLiteral
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w v : Word A}
namespace WordPicture

/-- Inserting a freely canceling pair is attaching a thickened edge at the
specified exterior corner, including the formerly empty exterior. -/
def insertAt (P : WordPicture R w) {l r : Word A} (he : w = l++r) (a : A × Bool) :
    WordPicture R (l++a::invLetter a::r) := by
  have P' := P.rotate l.length
  have he' : w.rotate l.length = r++l := by rw [he,List.rotate_append_length_eq]
  rw [he'] at P'
  have Q := (P'.append (freePair R a)).rotate r.length
  have he'' : ((r++l)++[a,invLetter a]).rotate r.length = l++a::invLetter a::r := by
    rw [List.append_assoc,List.rotate_append_length_eq]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  exact he'' ▸ Q

lemma of_reverse_step (P : WordPicture R v) (h : FreeGroup.Red.Step w v) :
    Nonempty (WordPicture R w) := by
  cases h with
  | @not l r x b => exact ⟨P.insertAt rfl (x,b)⟩

lemma of_reverse_red (h : FreeGroup.Red w v) :
    Nonempty (WordPicture R v) → Nonempty (WordPicture R w) := by
  induction h with
  | refl => exact id
  | tail h h' ih => rintro ⟨P⟩; exact ih (P.of_reverse_step h')

lemma of_free_eq (P : WordPicture R w) (he : FreeGroup.mk w = FreeGroup.mk v) :
    Nonempty (WordPicture R v) := by
  obtain ⟨z,hw,hv⟩ := FreeGroup.Red.exact.mp he
  exact of_reverse_red hv (P.of_red hw)

end WordPicture

/-- Literal van Kampen disk realization from the ordinary presented group.
All sides and relator boundaries are indexed; the map is genuinely finite
and genus zero. There is no disk realization, area bound, or planarity premise.
This producer handles arbitrary (not just reduced or nonempty) null words. -/
theorem literal_picture_existence {R : Set (Word A)} (w : Word A)
    (h : PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk w) = 1) :
    Nonempty (WordPicture R w) := by
  obtain ⟨v,hv,⟨P⟩⟩ := picture_existence w h
  exact P.of_free_eq hv

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonDiskProducer
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open HyperbolicObstruction.PictureSwitch HyperbolicObstruction.WordPictures Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C A V M : Type*} [AddCommGroup M]
variable (B : PolygonTarget.Boundary C (A × Bool) V)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → A × Bool)
  (closed : ∀ i, B.start (word (finRotate ell i)) = B.start (B.rev (word i)))
variable (weight : C → M) (apex : V → Bool)
  (radial : ∀ l, apex (B.start l) = true → apex (B.start (B.rev l)) = false)

/-- Every nonempty literal null word produces an actual mapped genus-zero
cell picture with ONE distinguished exterior boundary. Every other face maps
with its own indexed enumeration to a genuine attaching polygon, in either
orientation. The exterior has positive orientation and coefficient zero. -/
theorem nullWord_picture (hinv : B.rev = invLetter)
    (h : PresentedGroup.mk (FreeGroup.mk '' Set.range B.attachingWord)
      (FreeGroup.mk (List.ofFn word)) = 1) :
    ∃ (Q : CellPicture.{0} (B.outsideTarget ell hell word closed weight apex radial))
      (xs : List Q.Dart), IsBoundary Q.pairing.face xs ∧
      xs.map ((B.outsideTarget ell hell word closed weight apex radial).edge ∘ Q.index) = List.ofFn word ∧
      ∀ x, B.outsideTag ell hell word closed (Q.index x) =
        if x ∈ xs then some true else none := by
  let : DecidableEq (C ⊕ Unit) := Classical.decEq _
  let T := B.outsideTarget ell hell word closed weight apex radial
  have ht : T.rev = invLetter := hinv
  obtain ⟨P⟩ := literal_picture_existence (List.ofFn word) h
  have hR : ∀ r ∈ Set.range B.attachingWord,
      ∃ ys : List (B.withOutside ell hell word closed).Side,
        IsBoundary T.next ys ∧ ys.map T.edge = r ∧
        (∀ y ∈ ys, B.outsideTag ell hell word closed y = none ∧
          B.outsideTag ell hell word closed (T.opposite y) = none) := by
    rintro r ⟨c,rfl⟩
    refine ⟨(B.withOutside ell hell word closed).positiveSides (.inl c),
      (B.withOutside ell hell word closed).positiveSides_boundary _,?_,?_⟩
    · exact (B.withOutside ell hell word closed).positiveSides_label _
    · exact B.positive_inside_tag ell hell word closed c
  have hw : ∃ ys : List (B.withOutside ell hell word closed).Side,
      IsBoundary T.next ys ∧ ys.map T.edge = List.ofFn word ∧
      (∀ y ∈ ys, B.outsideTag ell hell word closed y = some true) := by
    refine ⟨(B.withOutside ell hell word closed).positiveSides (.inr ()),
      (B.withOutside ell hell word closed).positiveSides_boundary _,?_,?_⟩
    · exact (B.withOutside ell hell word closed).positiveSides_label _
    · exact B.positive_outside_tag ell hell word closed
  obtain ⟨j,hj,hl,hmark⟩ := P.cellular_index_tag T ht
    (B.outsideTag ell hell word closed) none (some true) hR hw
  let Q : CellPicture T := {
    Dart := P.Dart
    pairing := P.pairing
    index := j
    mapped := hj
    respects := T.respects_of_edge P.pairing j hj (by
      intro x
      rw [hl,hl,ht]
      exact P.paired x)
    genusZero := P.genusZero }
  refine ⟨Q,P.outside,P.boundary,?_,hmark⟩
  have he : T.edge ∘ j = P.label := funext hl
  exact (congrArg (List.map · P.outside) he).trans P.word

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeDiskNormal
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

lemma exteriorCellToWalk_exterior_iff
    (weight : Cell n w d → A)
    (P : CellPicture (exteriorCellTarget n w d ell hell word closed weight))
    (xs : List P.Dart)
    (hp : ∀ x, (boundary n w d).outsideTag ell hell word closed (P.index x) =
      if x ∈ xs then some true else none) :
    ∀ x, (walkTarget n w d c hc f).isExterior ell hell word closed
      ((exteriorCellToWalk n w d ell hell word closed c hc f weight P).index x) ↔ x ∈ xs := by
  intro x
  have ht : (walkTarget n w d c hc f).isExterior ell hell word closed
      ((exteriorCellToWalk n w d ell hell word closed c hc f weight P).index x) ↔
      (boundary n w d).outsideTag ell hell word closed (P.index x) ≠ none := by
    rcases hxi : P.index x with ⟨a,b,i⟩
    cases a with
    | inl a =>
      change (walkTarget n w d c hc f).isExterior ell hell word closed
        (exteriorCellStep n w d ell hell word closed c hc f (P.index x)) ↔ _
      rw [hxi]
      simp only [exteriorCellStep,WalkCellTarget.isExterior,Sum.elim_inl,
        PolygonTarget.Boundary.outsideTag,ne_eq,not_true_eq_false]
    | inr a =>
      change (walkTarget n w d c hc f).isExterior ell hell word closed
        (exteriorCellStep n w d ell hell word closed c hc f (P.index x)) ↔ _
      rw [hxi]
      simp only [exteriorCellStep,WalkCellTarget.isExterior,Sum.elim_inr,
        PolygonTarget.Boundary.outsideTag,ne_eq,Option.some_ne_none,not_false_eq_true]
  refine ht.trans ⟨?_, ?_⟩
  · intro h
    by_contra hnot
    exact h ((hp x).trans (ite_eq_right hnot))
  · intro h he
    exact (Option.some_ne_none true) (((hp x).trans (ite_eq_left h)).symm.trans he)

/-- Disk producer for the finite polygonal cone target:
a nonempty closed literal nullword has a genus-zero mixed picture in the
full normal form, with all outside positions and labels preserved. No
existence of a disk diagram, normal form, or boundary matching is assumed. -/
theorem nullWord_normal_picture
    (h : PresentedGroup.mk (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)
      (FreeGroup.mk (List.ofFn word)) = 1) :
    ∃ (Q : WalkPicture.{0} (exteriorWalkTarget n w d ell hell word closed c hc f))
      (xs : List Q.Dart),
      Q.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f) ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective (isApex n w) ∧
      IsBoundary Q.pairing.face xs ∧
      xs.map ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ Q.index) = List.ofFn word ∧
      (∀ x, (walkTarget n w d c hc f).isExterior ell hell word closed (Q.index x) ↔ x ∈ xs) ∧
      (∀ x s, Q.index x = .inr s → s.2.1 = true) := by
  let wt : Cell n w d → A := fun _ => 0
  obtain ⟨P,xs,hb,hl,ht⟩ := (boundary n w d).nullWord_picture ell hell word closed wt
    (isApex n w) (radial n w) rfl h
  let P' := exteriorCellToWalk n w d ell hell word closed c hc f wt P
  have hm := exteriorCellToWalk_frozen n w d ell hell word closed c hc f wt P
  have hp := exteriorCellToWalk_tag n w d ell hell word closed c hc f wt P xs ht
  have hk := exteriorCellToWalk_exterior_iff n w d ell hell word closed c hc f wt P xs ht
  obtain ⟨Q,⟨hr⟩,hqm,hqs,hqb,hqr,hqa,hchain⟩ :=
    (walkTarget n w d c hc f).normalize_exterior ell hell word closed
      (walkFrozenTarget n w d c hc f) P' hm hp (isApex n w) (radial n w)
  obtain ⟨ys,hy,he,hword,hkeep⟩ := hr.boundary
    ((walkTarget n w d c hc f).exterior_frozen ell hell word closed) xs hb hk
  refine ⟨Q,ys,hqm,hqs,hqb,hqr,hqa,hy,?_,hkeep,?_⟩
  · rw [hword]
    have hv : (exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P'.index =
        (exteriorCellTarget n w d ell hell word closed wt).edge ∘ P.index := by
      funext x
      exact exteriorCellStep_label n w d ell hell word closed c hc f _
    rw [hv]
    exact hl
  · intro x s hx
    apply hp (hr.map x) s
    rw [← hr.index]
    exact hx

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CoreWordGraph
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry MasterGraph LetterPresentation SimpleGraph
variable (S : Finset IncidenceTemplate.Edge)

lemma toMaster_fields {a b : CoreGeometry.Vertex} (p : (graph S).Walk a b) :
    Fields S (toMaster S p) := by
  induction p with
  | nil => simp [toMaster,Fields,Path.fields]
  | cons h p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨_,coreStep_field _,core_edge_mem S h⟩
    · exact ih f hf

end HyperbolicObstruction.CoreWordGraph
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SimpleLetterPresentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.WordPictures.instNormalFreeGroupPictureSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.LetterPresentation
open IncidenceTemplate CoreGeometry MasterGraph SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma simpleWordRelator_original {z : List (Alphabet n)} (hz : SimpleWordRelator n w d z) :
    WordRelator n w d z := by
  cases hz with
  | fan l i present v p simple =>
    rw [← CoreWordGraph.toMaster_word]
    apply WordRelator.fan l i present (.inl v)
    intro f hf
    have hm := CoreWordGraph.toMaster_fields (fan i) p f (List.mem_toFinset.mp hf)
    obtain ⟨e,rfl,he⟩ := hm
    simpa [rowSupport] using he
  | top l present fans v p simple =>
    rw [← CoreWordGraph.toMaster_word]
    apply WordRelator.top l present fans (.inl v)
    intro f hf
    obtain ⟨e,rfl,he⟩ := CoreWordGraph.toMaster_fields Finset.univ p f hf
    exact ⟨e,rfl⟩
  | square l τ present => exact WordRelator.square l τ present
  | six x present => exact WordRelator.six x present

/-- Every ORIGINAL relator has a quantitative derivation in the finite
simple-cycle presentation. The bound is its literal length (zero included). -/
theorem relator_simple_filling {z : List (Alphabet n)} (hz : WordRelator n w d z) :
    ∃ a ≤ z.length, WordPictures.Homotopy (SimpleWordRelator n w d) z [] a := by
  cases hz with
  | fan l i present v p fields =>
    have hp := fan_fields i p fields
    obtain ⟨a,ha,hh⟩ := GraphWordFilling.closed_filling (CoreWordGraph.label (fan i) n l)
      (CoreWordGraph.label_rev _ _ _) (SimpleWordRelator n w d)
      (fun v p h => SimpleWordRelator.fan l i present v p h) (CoreWordGraph.path _ p hp)
    rw [CoreWordGraph.path_word] at hh
    rw [CoreWordGraph.path_length] at ha
    exact ⟨a,by simpa only [pathWord_length] using ha,hh⟩
  | top l present fans v p core =>
    have hp := top_fields p core
    obtain ⟨a,ha,hh⟩ := GraphWordFilling.closed_filling (CoreWordGraph.label Finset.univ n l)
      (CoreWordGraph.label_rev _ _ _) (SimpleWordRelator n w d)
      (fun v p h => SimpleWordRelator.top l present fans v p h) (CoreWordGraph.path _ p hp)
    rw [CoreWordGraph.path_word] at hh
    rw [CoreWordGraph.path_length] at ha
    exact ⟨a,by simpa only [pathWord_length] using ha,hh⟩
  | square l τ present =>
    refine ⟨1,by simp [literalSquare],?_⟩
    simpa only [List.nil_append,List.append_nil] using
      (WordPictures.Homotopy.move (WordPictures.Move.face [] [] _
        (SimpleWordRelator.square l τ present)))
  | six x present =>
    refine ⟨1,by simp,?_⟩
    simpa only [List.nil_append,List.append_nil] using
      (WordPictures.Homotopy.move (WordPictures.Move.face [] [] _
        (SimpleWordRelator.six x present)))

/-- Exact normal-closure equality, giving the same original marked group,
not merely a surjection from a conveniently chosen finite presentation. -/
theorem simple_presentation_normalClosure :
    Subgroup.normalClosure (FreeGroup.mk '' SimpleWordRelator n w d) =
    Subgroup.normalClosure (Relator n w d) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_mono
    rintro _ ⟨z,hz,rfl⟩
    rw [← wordRelator_image]
    exact ⟨z,simpleWordRelator_original n w d hz,rfl⟩
  · apply Subgroup.normalClosure_le_normal
    intro g hg
    rw [← wordRelator_image] at hg
    obtain ⟨z,hz,rfl⟩ := hg
    obtain ⟨a,ha,hh⟩ := relator_simple_filling n w d hz
    apply PresentedGroup.mk_eq_one_iff.mp
    have he := WordPictures.sound hh
    exact he

end HyperbolicObstruction.LetterPresentation
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureArea
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

/-- The distinguished outside is not paid for: a nonempty literal boundary
has a filling costing at most the number of INTERIOR face cycles. -/
theorem filling_interior {w : Word A} (P : WordPicture R w) (ho : P.outside ≠ []) :
    ∃ n, Homotopy R w [] n ∧ n ≤ Fintype.card P.Dart / 2 ∧
      (n : ℤ) + 1 ≤ cycles P.pairing.face := by
  by_cases hc : ∀ x ∈ P.outside, P.pairing.edge x ∈ P.outside
  · refine ⟨0,P.isolated_outside_filling hc,Nat.zero_le _,?_⟩
    obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil _ ho
    exact cycles_positive P.pairing.face a
  push Not at hc
  obtain ⟨a,hao,hai⟩ := hc
  obtain ⟨ol,orr,ho⟩ := List.mem_iff_append.mp hao
  let Q := P.rotate ol.length
  have hqo : Q.outside = a::(orr++ol) := by
    change P.outside.rotate ol.length = _
    rw [ho,List.rotate_append_length_eq,List.cons_append]
  have hqi : Q.pairing.edge a ∉ Q.outside := by
    change P.pairing.edge a ∉ P.outside.rotate ol.length
    simpa only [List.mem_rotate] using hai
  have hne : ¬ Q.pairing.face.SameCycle a (Q.pairing.edge a) := by
    intro hh
    have haQ : a ∈ Q.outside := hqo.symm ▸ List.mem_cons_self
    exact hqi (Q.boundary.mem_of_sameCycle haQ hh)
  obtain ⟨xs,hs,hm,hrel⟩ := Q.interior (Q.pairing.edge a) hqi
  obtain ⟨il,irr,hi⟩ := List.mem_iff_append.mp hm
  have hin : IsBoundary Q.pairing.face (Q.pairing.edge a::(irr++il)) := by
    simpa only [List.cons_append] using (hi ▸ hs).rotate_append
  have hface : Homotopy R ((Q.pairing.edge a::(irr++il)).map Q.label) [] 1 := by
    have hh := hrel.filling
    rw [hi,List.map_append] at hh
    simpa only [List.map_append,List.map_cons,List.cons_append] using hh.rotate_null
  let S := Q.peelAt hqo hin hne
  have hrem : ∃ n, Homotopy R (((irr++il) ++ (show List Q.Dart from orr++ol)).map Q.label) [] n ∧
      n ≤ Fintype.card S.Dart / 2 ∧ (n : ℤ) + 2 ≤ cycles P.pairing.face := by
    by_cases hz : S.outside = []
    · have hempty : (irr++il) ++ (show List Q.Dart from orr++ol) = [] := by
        have he := congrArg (List.map Subtype.val) hz
        simpa only [S,WordPicture.peelAt,List.map_attachWith,List.map_nil,List.attach_map_subtype_val] using he
      refine ⟨0,?_,Nat.zero_le _,?_⟩
      · rw [hempty,List.map_nil]; exact Homotopy.refl []
      · have hp := cycles_positive (Q.pairing.face * swap (show Q.Dart from a) (Q.pairing.edge a)) a
        have hm := cycles_merge_right Q.pairing.face hne
        change 0 + 2 ≤ cycles Q.pairing.face
        calc
          (0 : ℤ) + 2 = 1 + 1 := rfl
          _ ≤ cycles (Q.pairing.face * swap (show Q.Dart from a) (Q.pairing.edge a)) + 1 := by simpa only [add_comm] using add_le_add_right hp 1
          _ = cycles Q.pairing.face := hm
    · obtain ⟨n,hn,he,hf⟩ := filling_interior (w := _) S hz
      refine ⟨n,hn,he,?_⟩
      have hF := Q.pairing.eraseEdge_faces_le a hne
      change cycles S.pairing.face + 1 ≤ cycles P.pairing.face at hF
      omega
  obtain ⟨n,hn,he,hf⟩ := hrem
  refine ⟨1+n,?_,?_,?_⟩
  · have hword : w.rotate ol.length = Q.label a :: (orr ++ ol).map Q.label :=
      Q.word.symm.trans (congrArg (List.map Q.label) hqo)
    have hh : Homotopy R (w.rotate ol.length) [] (1+n) := by
      rw [hword]
      have hn' : Homotopy R ((irr++il).map Q.label ++ (orr++ol).map Q.label) [] n := by
        exact (List.map_append (f := Q.label) (l₁ := irr ++ il) (l₂ := orr ++ ol)) ▸ hn
      exact Homotopy.peel (Q.paired a) hface hn'
    apply Homotopy.unrotate_null ol.length _ hh
    have hl : P.outside.length = w.length := by simpa using congrArg List.length P.word
    simp only [ho,List.length_append,List.length_cons] at hl
    omega
  · have hD := card_offPair (Q.pairing.edge_ne a).symm
    simp only [← Nat.card_eq_fintype_card] at hD he ⊢
    change Nat.card {x : Q.Dart // OffPair a (Q.pairing.edge a) x} + 2 =
      Nat.card P.Dart at hD
    change n ≤ Nat.card {x : Q.Dart // OffPair a (Q.pairing.edge a) x} / 2 at he
    omega
  · omega
termination_by Fintype.card P.Dart
decreasing_by
  have hD := card_offPair (Q.pairing.edge_ne a).symm
  simp only [← Nat.card_eq_fintype_card] at hD ⊢
  change Nat.card {x : Q.Dart // OffPair a (Q.pairing.edge a) x} < Nat.card P.Dart
  change Nat.card {x : Q.Dart // OffPair a (Q.pairing.edge a) x} + 2 =
    Nat.card P.Dart at hD
  omega

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_NormalDiskArea
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

include hm hs hb xs hx hw ht in
/-- The genuine normalized cone disk costs at most
THIRTY times its number of INTERIOR cells in the finite simple presentation.
No bound on the number of diagram cells is assumed or claimed here. -/
theorem normal_disk_area :
    ∃ a, Homotopy (SimpleWordRelator n w d) ((List.ofFn word).flatMap (collapse n w)) [] a ∧
      (a : ℤ) ≤ 30 * (cycles P.pairing.face - 1) := by
  let Q := normalWordPicture n w d ell hell word closed c hc f P hm hs hb xs hx hw ht
  have ho : Q.outside ≠ [] := by
    intro he
    have hh := hw
    change xs = [] at he
    rw [he,List.map_nil] at hh
    have hl := congrArg List.length hh
    simp only [List.length_nil,List.length_ofFn] at hl
    omega
  obtain ⟨k,hk,he,hF⟩ := Q.filling_interior ho
  obtain ⟨a,ha,hfill⟩ := hk.substitute (collapse n w) (fun e => collapse_rev n w e)
    (fun r hr => hr)
  refine ⟨a,hfill,?_⟩
  have hb' : (a : ℤ) ≤ 30 * (k : ℤ) := by exact_mod_cast ha
  change (k : ℤ) + 1 ≤ cycles P.pairing.face at hF
  omega

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LetterNormalPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (word : Fin ell → Alphabet n)

variable (hell : 0 < ell)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

/-- Diagram existence and normalization for the original letter
presentation, not merely for a surrogate cone presentation. All literal
outside positions survive. Every mixed interior face maps to an actual
included source row, and no injectivity of random letter labels is assumed. -/
theorem null_letter_word_normal_picture
    (h : PresentedGroup.mk (Relator n w d) (FreeGroup.mk (List.ofFn word)) = 1) :
    ∃ (Q : WalkPicture.{0} (exteriorWalkTarget n w d ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) c hc f)) (xs : List Q.Dart),
      Q.FrozenMapped (exteriorWalkFrozen n w d ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) c hc f) ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective (isApex n w) ∧
      IsBoundary Q.pairing.face xs ∧
      xs.map ((exteriorWalkTarget n w d ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) c hc f).label ∘ Q.index) =
        List.ofFn (letterDart n w ∘ word) ∧
      (∀ x, (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) (Q.index x) ↔ x ∈ xs) ∧
      (∀ x s, Q.index x = .inr s → s.2.1 = true) := by
  apply nullWord_normal_picture n w d ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) c hc f
  have hh := nullWord_to_polygon n w d (List.ofFn word) h
  simpa only [List.map_ofFn] using hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeGlobalStep
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty
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

include hx hw ht in
/-- Actual relator filling with its exact fragment-cut cost. This is valid for
every small partition, without assuming that a low-cut separator exists. -/
theorem partition_filling_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hk : 0 ≤ defectConstant α β δ)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hM : ∀ i, 8 * Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ M) :
    ∃ a, Homotopy (SimpleWordRelator n w d) (List.ofFn word) [] a ∧
      defectConstant α β δ * a ≤ 30 * ((ell : ℝ) +
        2 * Fintype.card (RelativeCutContact P.pairing
          (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass))) := by
  obtain ⟨a,hfill,ha'⟩ := normal_disk_area n w d ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) c hc f P hm hs hb xs hx hw ht
  have he : (List.ofFn (letterDart n w ∘ word)).flatMap (collapse n w) = List.ofFn word := by
    rw [← List.map_ofFn]
    exact collapse_letter_word n w (List.ofFn word)
  rw [he] at hfill
  refine ⟨a,hfill,?_⟩
  rw [← interior_card n w d ell hell word c hc f P xs hx hw ht] at ha'
  have haR : (a : ℝ) ≤ 30 * Fintype.card (InteriorFace n w d ell hell word c hc f P) := by
    exact_mod_cast ha'
  have hp := partition_face_bound n w d ell hell word c hc f P xs hw ht part ha hgood hs hm hred hrad hb hM
  calc
    defectConstant α β δ * a ≤ defectConstant α β δ *
      (30 * Fintype.card (InteriorFace n w d ell hell word c hc f P)) := mul_le_mul_of_nonneg_left haR hk
    _ = 30 * (defectConstant α β δ * Fintype.card (InteriorFace n w d ell hell word c hc f P)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeDegree
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

/-- The actual interior dual multigraph of a protected normal disk has the
source's uniform bound15. The arbitrary exterior degree is not bounded. -/
theorem exterior_interior_degree (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f))
    (x : P.Dart)
    (hx : ¬ (walkTarget n w d c hc f).isExterior ell hell word closed (P.index x)) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y} ≤ 15 := by
  cases hi : P.index x with
  | inl s =>
    cases s with
    | inl s => exact exterior_top_degree n w d ell hell word closed c hc f P hs hb x s.1 s.2 hi
    | inr s => exact (exterior_frozen_degree n w d ell hell word closed c hc f P hm x s hi).trans (by decide)
  | inr s => rw [hi] at hx; exact False.elim (hx trivial)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeSmallPartition
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

/-- The random-data-independent cutoff for literal small interior fragments.
The genus-zero planar partition producer is proved, not a hypothesis. -/
theorem uniform_small_interior_partition (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧
    ∀ (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool) (ell : ℕ) (hell : 0 < ell)
      (word : Fin ell → Alphabet n)
      (c : Top n w → MacroGraph.graph.Dart → ℤ)
      (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → ℤ)
      (P : WalkPicture.{0} (target n w d ell hell word c hc f)),
      P.Simple → P.NoBigon → P.FrozenMapped (frozen n w d ell hell word c hc f) →
      ∃ (I : Type) (_ : Fintype I) (part : P.Face → I),
        (∀ i, Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ K) ∧
        (Fintype.card (RelativeCutContact P.pairing
          (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass)) : ℝ) ≤
          eta * Fintype.card (InteriorFace n w d ell hell word c hc f P) := by
  obtain ⟨K,hK,hh⟩ := uniform_genusZero_face_partition.{0} 15 eta heta
  refine ⟨K,hK,?_⟩
  intro n w d ell hell word c hc f P hs hb hm
  let U : Finset P.Face := Finset.univ.filter (Interior n w d ell hell word c hc f P)
  have hUm (F : P.Face) : F ∈ U ↔ Interior n w d ell hell word c hc f P F := by simp [U]
  have hd (F : P.Face) (hF : F ∈ U) :
      Nat.card {x : P.Dart // P.faceClass x = F} ≤ 15 := by
    have hi : ¬ (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) (P.index F.out) := by
      apply (interior_iff n w d ell hell word c hc f P F.out).mp
      rw [P.faceClass_out]
      exact (hUm F).mp hF
    have he : {x : P.Dart // P.faceClass x = F} ≃
        {x : P.Dart // P.pairing.face.SameCycle F.out x} :=
      Equiv.subtypeEquivRight (fun x => by
        rw [← P.faceClass_eq]
        exact ⟨fun h => (P.faceClass_out F).trans h.symm,
          fun h => h.symm.trans (P.faceClass_out F)⟩)
    rw [Nat.card_congr he,Nat.card_eq_fintype_card]
    exact exterior_interior_degree n w d ell hell (letterDart n w ∘ word)
      (letterWordClosed n w ell word) c hc f P hs hb hm F.out hi
  obtain ⟨I,inst,part,hsize,hcut⟩ := hh P.Dart P.pairing P.genusZero U hd
  let := inst
  have hcard : U.card = Fintype.card (InteriorFace n w d ell hell word c hc f P) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight hUm)
  refine ⟨I,inst,part,?_,?_⟩
  · intro i
    have e : {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≃
        {F // F ∈ U.filter (fun x => part x = i)} := {
      toFun := fun F => ⟨F.val.val,Finset.mem_filter.mpr ⟨(hUm _).mpr F.val.property,F.property⟩⟩
      invFun := fun F => ⟨⟨F.val,(hUm _).mp (Finset.mem_filter.mp F.property).1⟩,
        (Finset.mem_filter.mp F.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Fintype.card_congr e,Fintype.card_coe]
    exact hsize i
  · rw [hcard] at hcut
    simp only [← Nat.card_eq_fintype_card] at hcut ⊢
    simpa only [hUm,Function.comp_apply,WalkPicture.faceClass,RelativeCutContact] using hcut

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_OriginalLinearFilling
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
open Occurrences.Shape
attribute [local instance] Classical.propDecidable

/-- Deterministic linear filling theorem, with a uniform cutoff for
all random tables and all original-letter null words, including the empty word. -/
theorem original_letter_linear_filling {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (ell : ℕ) (word : Fin ell → Alphabet n),
      PresentedGroup.mk (Relator n w d) (FreeGroup.mk (List.ofFn word)) = 1 →
      ∃ a, Homotopy (SimpleWordRelator n w d) (List.ofFn word) [] a ∧
        defectConstant α β δ * a ≤ 60 * (ell : ℝ) := by
  have hk := defectConstant_pos ha hb hd
  obtain ⟨K,hK,hpart⟩ := RelDisk.uniform_small_interior_partition
    (defectConstant α β δ / 4) (div_pos hk (by norm_num))
  refine ⟨8*K,Nat.mul_pos (by decide) hK,?_⟩
  intro n w d hgood ell word hnull
  rcases Nat.eq_zero_or_pos ell with he | hell
  · subst ell
    refine ⟨0,?_,by simp⟩
    simpa only [List.ofFn_zero] using (WordPictures.Homotopy.refl (R := SimpleWordRelator n w d) [])
  let c : Top n w → MacroGraph.graph.Dart → ℤ := fun _ _ => 0
  have hc : ∀ a e, c a e.symm = -c a e := by intros; simp [c]
  let f : FrozenCell n w d → ℤ := fun _ => 0
  obtain ⟨P,xs,hm,hs,hbig,hred,hrad,hboundary,hword,htag,_hor⟩ :=
    null_letter_word_normal_picture n w d ell word hell c hc f hnull
  obtain ⟨I,inst,part,hsize,hcut⟩ := hpart n w d ell hell word c hc f P hs hbig hm
  let := inst
  have hM (i : I) : 8 * Fintype.card
      {F : RelDisk.InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ 8*K :=
    Nat.mul_le_mul_left 8 (hsize i)
  have hface := RelDisk.partition_face_bound n w d ell hell word c hc f P xs hword htag
    part ha.le hgood hs hm hred hrad hbig hM
  obtain ⟨a,hfill,ha'⟩ := RelDisk.partition_filling_bound n w d ell hell word c hc f P
    xs hboundary hword htag part ha.le hk.le hgood hs hm hred hrad hbig hM
  refine ⟨a,hfill,?_⟩
  nlinarith

/-- The same theorem in list-word form, with an explicit positive
linear constant depending only on the fixed parameters. -/
theorem original_letter_linear_filling_list {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ (M : ℕ) (C : ℝ), 0 < M ∧ 0 < C ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ word : List (Alphabet n),
      PresentedGroup.mk (Relator n w d) (FreeGroup.mk word) = 1 →
      ∃ a, Homotopy (SimpleWordRelator n w d) word [] a ∧ (a : ℝ) ≤ C * word.length := by
  obtain ⟨M,hM,hh⟩ := original_letter_linear_filling ha hb hd
  have hk := defectConstant_pos ha hb hd
  refine ⟨M,60 / defectConstant α β δ,hM,div_pos (by norm_num) hk,?_⟩
  intro n w d hgood word hnull
  have he : List.ofFn word.get = word := List.ofFn_get word
  obtain ⟨a,hfill,ha'⟩ := hh n w d hgood word.length word.get (by rwa [he])
  refine ⟨a,he ▸ hfill,?_⟩
  calc
    (a : ℝ) ≤ (60 * word.length) / defectConstant α β δ :=
      (le_div_iff₀ hk).mpr (by nlinarith)
    _ = _ := by ring

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RankSelection
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.LetterPresentation.group
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

lemma rank_bad_join_bound (M : ℕ) {n : ℕ} {α β δ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) :
    ((TableModel.law rowSupport (actualProbability α β δ (SymmetricAlphabet n))
      (actualProbability_mem ha hb hd)).prod (SixTable.law (A := SymmetricAlphabet n) δ hd)).prob
        (fun z => ¬GoodUpTo M α β δ (Sum.elim z.1 z.2)) ≤
      rankRate M α β δ (Fintype.card (SymmetricAlphabet n)) := by
  have hh := rank_bad_bound M (n := n) ha hb hd
  unfold FiniteLaw.prob at *
  rw [expect_join ha hb hd] at hh
  exact hh

/-- Simultaneous selection with the genuine bounded-rank event, not independent
new copies of the arrays used for sampling. -/
theorem exists_tables_of_estimate {J : Type*} [Fintype J]
    (T : J → ConditionalTest) (M n : ℕ) {α β δ ε τ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hsmall : ∀ j, ((T j).k+1:ℝ)*(β+90*δ) ≤ 1/2)
    (hN : ∀ j, (T j).threshold ≤ Fintype.card (SymmetricAlphabet n))
    (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2)
    (hest : (∑ j, (T j).rate (Fintype.card (SymmetricAlphabet n))) +
      ε*(60*(Fintype.card (SymmetricAlphabet n):ℝ)^2*
        Real.exp (-τ^2*(Fintype.card (SymmetricAlphabet n):ℝ)^(1-δ)/4) +
        rankRate M α β δ (Fintype.card (SymmetricAlphabet n))) < ε) :
    ∃ (w : TableModel.Entry (A := SymmetricAlphabet n) rowSupport → Bool)
      (d : (Fin 6 → SymmetricAlphabet n) → Bool),
      ¬SixTable.BadPairs δ τ d ∧ GoodUpTo M α β δ (Sum.elim w d) ∧
      ∀ j, (T j).Satisfies w
        (ε/(1-ε) + (1-((Fintype.card (SymmetricAlphabet n)).descFactorial ((T j).k+1):ℝ)/
          (Fintype.card (SymmetricAlphabet n):ℝ)^((T j).k+1))) := by
  classical
  let A := SymmetricAlphabet n
  let μ : FiniteLaw (TableModel.Entry (A := A) rowSupport → Bool) :=
    TableModel.law rowSupport (actualProbability α β δ A) (actualProbability_mem ha hb hd)
  let ν := SixTable.law (A := A) δ hd
  let E (j : J) (w : TableModel.Entry (A := A) rowSupport → Bool) :=
    (T j).error α β δ ha hb hd (hN j) w
  have hx (j : J) : (μ.prod ν).expect (fun z => E j z.1) ≤ (T j).rate (Fintype.card A) := by
    rw [FiniteLaw.expect_prod_fst]
    exact ConditionalTest.expectedError _ ha hb hd (hsmall j) (hN j)
  let B (z : (TableModel.Entry (A := A) rowSupport → Bool) × ((Fin 6 → A) → Bool)) :=
    SixTable.BadPairs δ τ z.2 ∨ ¬GoodUpTo M α β δ (Sum.elim z.1 z.2)
  have hb' : (μ.prod ν).prob B ≤
      60*(Fintype.card A:ℝ)^2*Real.exp (-τ^2*(Fintype.card A:ℝ)^(1-δ)/4) +
        rankRate M α β δ (Fintype.card A) := by
    apply (FiniteLaw.prob_or_le (μ.prod ν) _ _).trans
    apply add_le_add _ (rank_bad_join_bound M ha hb hd)
    unfold FiniteLaw.prob
    rw [FiniteLaw.expect_prod_snd μ ν (fun d => if SixTable.BadPairs δ τ d then 1 else 0)]
    exact SixTable.badPairs_bound hd hτ0 hτ2
  have hh : (∑ j, (μ.prod ν).expect (fun z => E j z.1)) + ε*(μ.prod ν).prob B < ε :=
    lt_of_le_of_lt (add_le_add (Finset.sum_le_sum fun j _ => hx j)
      (mul_le_mul_of_nonneg_left hb' hε0.le)) hest
  obtain ⟨⟨w,d⟩,hw,hE⟩ := FiniteLaw.exists_good_simultaneously (μ.prod ν) (fun j z => E j z.1)
    (fun j z => ConditionalTest.error_nonneg _ _ _ _ _ _ _ _ _) B hε0 hh
  refine ⟨w,d,fun h => hw (Or.inl h),not_not.mp (fun h => hw (Or.inr h)),?_⟩
  exact fun j => (T j).satisfies_of_error ha hb hd (hN j) w hε1 (hE j).le

end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RankSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage.instNonemptyRows _root_.OAI.HyperbolicObstruction.LetterPresentation.group
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
namespace IncidenceTemplate
namespace Occurrences

theorem eventually_exists_tables {J : Type*} [Fintype J]
    (T : J → ConditionalTest) (M : ℕ) {α β δ ε τ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (hd1 : δ < 1)
    (hsmall : ∀ j, ((T j).k+1:ℝ)*(β+90*δ) ≤ 1/2)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2) :
    ∀ᶠ n in atTop, ∃ (w : TableModel.Entry (A := SymmetricAlphabet n) rowSupport → Bool)
      (d : (Fin 6 → SymmetricAlphabet n) → Bool),
      ¬SixTable.BadPairs δ τ d ∧ GoodUpTo M α β δ (Sum.elim w d) ∧
      ∀ j, (T j).Satisfies w
        (ε/(1-ε) + (1-((Fintype.card (SymmetricAlphabet n)).descFactorial ((T j).k+1):ℝ)/
          (Fintype.card (SymmetricAlphabet n):ℝ)^((T j).k+1))) := by
  have hs : Tendsto (fun N => ∑ j, (T j).rate N) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ => (T j).rate_tendsto)
  have hr := (rankRate_tendsto M α β δ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hd' := ((SixTable.badPairs_rate_tendsto hd1 hτ0).add hr).const_mul ε
  have hh : Tendsto (fun N : ℕ => (∑ j, (T j).rate N) +
      ε*(60*(N:ℝ)^2*Real.exp (-τ^2*(N:ℝ)^(1-δ)/4) + rankRate M α β δ N)) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero,Function.comp_def] using hs.add hd'
  have he := (hh.comp alphabet_size_tendsto).eventually (gt_mem_nhds hε0)
  let K : ℕ := Finset.univ.sup (fun j => (T j).threshold)
  have hK := alphabet_size_tendsto.eventually (eventually_ge_atTop K)
  filter_upwards [he,hK] with n hn hN
  exact exists_tables_of_estimate T M n ha hb hd hsmall
    (fun j => (Finset.le_sup (f := fun j => (T j).threshold) (Finset.mem_univ j)).trans hN)
    hε0 hε1 hτ0 hτ2 hn

/-- Arbitrary finite conditional sampling data and the literal bounded-rank
producer are simultaneous on arbitrarily large original signed alphabets. -/
theorem eventually_exists_tables_precision {J : Type*} [Fintype J]
    (T : J → ConditionalTest) (M : ℕ) {α β δ ξ τ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (hd1 : δ < 1)
    (hsmall : ∀ j, ((T j).k+1:ℝ)*(β+90*δ) ≤ 1/2)
    (hξ : 0 < ξ) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2) :
    ∀ᶠ n in atTop, ∃ (w : TableModel.Entry (A := SymmetricAlphabet n) rowSupport → Bool)
      (d : (Fin 6 → SymmetricAlphabet n) → Bool),
      ¬SixTable.BadPairs δ τ d ∧ GoodUpTo M α β δ (Sum.elim w d) ∧
      ∀ j, (T j).Satisfies w ξ := by
  let ε : ℝ := min (ξ/4) (1/4)
  have he0 : 0 < ε := lt_min (by positivity) (by norm_num)
  have he4 : ε ≤ 1/4 := min_le_right _ _
  have he1 : ε < 1 := lt_of_le_of_lt he4 (by norm_num)
  have hq : ε/(1-ε) ≤ ξ/2 := by
    have hε : ε ≤ ξ/4 := min_le_left _ _
    have hh : ε/(1-ε) ≤ 2*ε := by
      rw [div_le_iff₀ (by linarith : 0 < 1-ε)]
      nlinarith
    exact hh.trans (by linarith)
  have hd' : ∀ᶠ n in atTop, ∀ j : J,
      1 - ((Fintype.card (SymmetricAlphabet n)).descFactorial ((T j).k+1):ℝ)/
        (Fintype.card (SymmetricAlphabet n):ℝ)^((T j).k+1) < ξ/2 := by
    rw [Filter.eventually_all]
    intro j
    exact ((FiniteLaw.distinct_error_tendsto ((T j).k+1)).comp alphabet_size_tendsto).eventually
      (gt_mem_nhds (by positivity))
  filter_upwards [eventually_exists_tables T M ha hb hd hd1 hsmall he0 he1 hτ0 hτ2,hd'] with n hn hdn
  obtain ⟨w,d,hw,hR,ht⟩ := hn
  refine ⟨w,d,hw,hR,fun j => (T j).satisfies_mono (ht j) ?_⟩
  linarith [hdn j]

end Occurrences

/-- A genuine stage with a bounded-rank certificate for the same arrays. The
size cutoff is arbitrary and fixed before the alphabet is selected. -/
structure RankSamplingStage (m M : ℕ) (φ : ℝ) extends SamplingStage m φ where
  rank_good : Occurrences.GoodUpTo M φ (8*φ) φ (Sum.elim master six)

lemma exists_rankSamplingStage (m M : ℕ) {φ : ℝ} (hφ : 0 < φ) (hφ1 : φ < 1)
    (hsmall : (m+1:ℝ)*(98*φ) ≤ 1/2) : Nonempty (RankSamplingStage m M φ) := by
  let T (j : ConditionalData × Fin (m+1)) := j.1.test j.2.val
  have hest : ∀ j, ((T j).k+1:ℝ)*(8*φ+90*φ) ≤ 1/2 := by
    intro j
    have hk : ((T j).k+1:ℝ) ≤ m+1 := by
      dsimp [T,ConditionalData.test]
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ j.2.isLt)
    have hh := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 98*φ)
    nlinarith
  have hh := Occurrences.eventually_exists_tables_precision T M hφ.le (by linarith : 7*φ ≤ 8*φ)
    hφ.le hφ1 hest (stageError_pos m) (stageError_pos m)
    ((stageError_le_third m).trans (by norm_num : (1:ℝ)/3 ≤ 2))
  obtain ⟨n,hn,hw⟩ := (hh.and (eventually_ge_atTop m)).exists
  obtain ⟨w,d,hd,hR,ht⟩ := hn
  have ht' (p : ConditionalData) (k : ℕ) (hk : k ≤ m) :
      (p.test k).Satisfies w (stageError m) := ht (p,⟨k,Nat.lt_succ_of_le hk⟩)
  have he : Nonempty Field := Fintype.card_pos_iff.mp (by rw [card_fields]; decide)
  let e : Field := Classical.choice he
  have hne := (ht' (singletonData e) 0 (Nat.zero_le _)).choose
  exact ⟨⟨⟨n,hw,w,d,hne,hd,ht'⟩,hR⟩⟩

/-- Diagonalizing in the desired diagram size imposes no additional sampling
hypothesis, and does not change the defining presentation. -/
def actualRankSamplingStage (M : ℕ → ℕ) (m : ℕ) : RankSamplingStage m (M m) (samplingParameter m) :=
  Classical.choice (exists_rankSamplingStage m (M m) (samplingParameter_pos m)
    (samplingParameter_lt_one m) (samplingParameter_small m))

def rankSelectedStage (M : ℕ → ℕ) (m : ℕ) : SamplingStage m (samplingParameter m) :=
  (actualRankSamplingStage M m).toSamplingStage

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DiagramSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
open Occurrences.Shape
attribute [local instance] Classical.propDecidable

/-- One cutoff simultaneously enforces the original-letter linear filling and
unbounded closed-picture chain vanishing. It is selected before each alphabet
and realization. -/
def diagramCutoff (m : ℕ) : ℕ :=
  max (original_letter_linear_filling_list (samplingParameter_pos m)
      (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
      (samplingParameter_pos m)).choose
    (uniform_closed_picture_chain_zero.{0,0} (samplingParameter_pos m)
      (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
      (samplingParameter_pos m)).choose

end HyperbolicObstruction.IncidenceTemplate
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SelectedPresentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace SamplingStage
variable {δ : ℕ → ℝ} (s : ∀ m, SamplingStage m (δ m))

def letter (m : ℕ) : (Alphabet s) m → LetterGroup s m :=
  LetterPresentation.letter (s m).size (s m).master (s m).six

def potential (m : ℕ) (a : (Matches s) m) : MasterGraph.Potential (label s m a) (letter s m) :=
  LetterPresentation.potential _ _ _ a

end SamplingStage
end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LiftedDiagramSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
open Occurrences.Shape
attribute [local instance] Classical.propDecidable

/-- A single diagonal cutoff for filling and the full LIFTED chain statement.
Nothing about a future picture, action, word, or deck group is sampled later. -/
def finalDiagramCutoff (m : ℕ) : ℕ :=
  max (diagramCutoff m)
    (uniform_actual_lifted_chain_zero.{0,0,0} (samplingParameter_pos m)
      (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
      (samplingParameter_pos m)).choose

def finalDiagramStage (m : ℕ) : SamplingStage m (samplingParameter m) :=
  rankSelectedStage finalDiagramCutoff m

end HyperbolicObstruction.IncidenceTemplate
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LetterCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma letterVoltage_rev (e : Dart n w) :
    letterVoltage n w d (rev n w e) = (letterVoltage n w d e)⁻¹ := by
  simp only [letterVoltage,collapse_rev,← FreeGroup.inv_mk,map_inv]

lemma letterVoltage_word (z : List (Dart n w)) :
    (z.map (letterVoltage n w d)).prod =
      PresentedGroup.mk (Relator n w d) (FreeGroup.mk (z.flatMap (collapse n w))) := by
  induction z with
  | nil => simp only [List.map_nil,List.prod_nil,List.flatMap_nil,← FreeGroup.one_eq_mk,map_one]
  | cons e z ih =>
    simp only [List.map_cons,List.prod_cons,List.flatMap_cons,← FreeGroup.mul_mk,map_mul,← ih]
    rfl

lemma letterVoltage_cell (a : Cell n w d) :
    (List.ofFn (fun i => letterVoltage n w d (side n w d a i))).prod = 1 := by
  have heq := letterVoltage_word n w d (List.ofFn (side n w d a))
  simp only [List.map_ofFn,Function.comp_def] at heq
  rw [heq]
  obtain ⟨_, _, filling⟩ := cell_collapse_filling n w d a
  have he := WordPictures.sound filling
  apply PresentedGroup.mk_eq_one_iff.mpr
  have hm := PresentedGroup.mk_eq_one_iff.mp he
  rw [simple_presentation_normalClosure] at hm
  exact hm

lemma letterVoltage_letter (a : Alphabet n) :
    letterVoltage n w d (letterDart n w a) = LetterPresentation.letter n w d a := by
  simp only [letterVoltage,collapse_letter,LetterPresentation.letter,freeLetter_mk]

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ElementaryCone
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

/-- Unconditional original-group values on the actual pre-compression cells. -/
lemma elementaryLetterVoltage_cell (a : ElementaryCell n w d) :
    (List.ofFn (fun i => elementaryVoltage n w (letterVoltage n w d)
      (elementarySide n w d a i))).prod = 1 :=
  elementaryVoltage_cell n w d (letterVoltage n w d)
    (letterVoltage_rev n w d) (letterVoltage_cell n w d) a

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ElementaryCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

/-- The actual original quotient supplies every triangle and frozen-cell lift;
no relator equations or nonvacuity properties are added as hypotheses. -/
def elementaryLetterLiftedBoundary :=
  elementaryLiftedBoundary n w d (letterVoltage n w d)
    (letterVoltage_rev n w d) (letterVoltage_cell n w d)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureAppend
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary _root_.OAI.HyperbolicObstruction.WordPictures.instNormalFreeGroupPictureSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {u v : Word E}
  {B : PolygonTarget.Boundary C (E × Bool) V}
  {P : WordPicture R u} {Q : WordPicture R v}
namespace Indexing
variable (I : Indexing B P) (J : Indexing B Q)
  (hp : P.outside ≠ []) (hq : Q.outside ≠ [])

lemma append_left_boundary {x : P.Dart} (hx : x ∉ P.outside) :
    ∃ xs : List P.Dart, IsBoundary P.pairing.face xs ∧ x ∈ xs ∧
      IsBoundary (P.appendNonempty Q hp hq).pairing.face (xs.map Sum.inl) := by
  obtain ⟨xs,hs,hxm,_⟩ := P.interior x hx
  have hdis : ∀ a ∈ xs, a ∉ P.outside := by
    intro a ha hoa
    exact hx (P.boundary.mem_of_sameCycle hoa (hs.sameCycle ha hxm))
  refine ⟨xs,hs,hxm,?_⟩
  exact (hs.map (Sum.inl (β := Q.Dart)) Sum.inl_injective (fun _ => rfl)).splice_away
    (by simp only [List.mem_map]; rintro ⟨y,hy,he⟩
        exact hdis y hy (Sum.inl.inj he ▸ List.getLast_mem hp))
    (by simp)

lemma append_right_boundary {x : Q.Dart} (hx : x ∉ Q.outside) :
    ∃ xs : List Q.Dart, IsBoundary Q.pairing.face xs ∧ x ∈ xs ∧
      IsBoundary (P.appendNonempty Q hp hq).pairing.face (xs.map Sum.inr) := by
  obtain ⟨xs,hs,hxm,_⟩ := Q.interior x hx
  have hdis : ∀ a ∈ xs, a ∉ Q.outside := by
    intro a ha hoa
    exact hx (Q.boundary.mem_of_sameCycle hoa (hs.sameCycle ha hxm))
  refine ⟨xs,hs,hxm,?_⟩
  exact (hs.map (Sum.inr (α := P.Dart)) Sum.inr_injective (fun _ => rfl)).splice_away
    (by simp)
    (by simp only [List.mem_map]; rintro ⟨y,hy,he⟩
        exact hdis y hy (Sum.inr.inj he ▸ List.getLast_mem hq))

def appendNonempty : Indexing B (P.appendNonempty Q hp hq) where
  index := Sum.elim I.index J.index
  outside x := by
    change P.Dart ⊕ Q.Dart at x
    change Sum.elim I.index J.index x = none ↔
      x ∈ P.outside.map Sum.inl ++ Q.outside.map Sum.inr
    have hmem {α β : Type} (xs : List α) (ys : List β) (z : α ⊕ β) :
        Sum.elim (fun x => x ∈ xs) (fun y => y ∈ ys) z ↔
          z ∈ xs.map Sum.inl ++ ys.map Sum.inr := by
      cases z <;> simp
    cases x with
    | inl x => exact (I.outside x).trans (hmem P.outside Q.outside (.inl x))
    | inr x => exact (J.outside x).trans (hmem P.outside Q.outside (.inr x))
  commute x := by
    change P.Dart ⊕ Q.Dart at x
    let j := Sum.elim I.index J.index
    let a : P.Dart ⊕ Q.Dart := .inl (P.outside.getLast hp)
    let b : P.Dart ⊕ Q.Dart := .inr (Q.outside.getLast hq)
    have ha : j a = none := (I.outside _).mpr (List.getLast_mem hp)
    have hb : j b = none := (J.outside _).mpr (List.getLast_mem hq)
    have hs : j (swap a b x) = j x := by
      by_cases hxa : x = a
      · subst x; rw [swap_apply_left,ha,hb]
      by_cases hxb : x = b
      · subst x; rw [swap_apply_right,ha,hb]
      rw [swap_apply_of_ne_of_ne hxa hxb]
    have hc : ∀ z, j ((P.pairing.sum Q.pairing).face z) = (j z).map B.next := by
      intro z; cases z with
      | inl z => exact I.commute z
      | inr z => exact J.commute z
    exact (hc (swap a b x)).trans (congrArg (Option.map B.next) hs)
  injective := by
    intro x y hxy s hx hy
    change P.Dart ⊕ Q.Dart at x y
    cases x with
    | inl x =>
      have hxo : x ∉ P.outside := by
        intro h; have hh : some s = none := hx.symm.trans ((I.outside x).mpr h); cases hh
      obtain ⟨xs,hs,hxm,hms⟩ := append_left_boundary hp hq hxo
      obtain ⟨y',hy',he⟩ := List.mem_map.mp
        (hms.mem_of_sameCycle (List.mem_map.mpr ⟨x,hxm,rfl⟩) hxy)
      subst y
      exact congrArg Sum.inl (I.injective (hs.sameCycle hxm hy') s hx hy)
    | inr x =>
      have hxo : x ∉ Q.outside := by
        intro h; have hh : some s = none := hx.symm.trans ((J.outside x).mpr h); cases hh
      obtain ⟨xs,hs,hxm,hms⟩ := append_right_boundary hp hq hxo
      obtain ⟨y',hy',he⟩ := List.mem_map.mp
        (hms.mem_of_sameCycle (List.mem_map.mpr ⟨x,hxm,rfl⟩) hxy)
      subst y
      exact congrArg Sum.inr (J.injective (hs.sameCycle hxm hy') s hx hy)
  label x s hx := by
    cases x with
    | inl x => exact I.label x s hx
    | inr x => exact J.label x s hx

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
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
namespace PictureSwitch

/-! Literal radial triangulation of the free polygon faces of a finite map.
This section concerns genuine permutations; no topological genus assertion is
included in the input. -/

/-! Exact contraction of radial triangle stars. -/
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

namespace TriangleMarking
variable {M : PictureMap D} (H : TriangleMarking M)

omit [Fintype D] [DecidableEq D] in
lemma free_invariant (x : H.Base) : H.free (H.contraction.face x) ↔ H.free x := by
  change H.top (H.next x.val) = true ↔ H.top x.val = true
  rw [H.next_top]

/-- Each elementary dart has its own retained old side, with the two radial
copies kept separately until the final contraction. -/
def expand : ConeExpansion.Point H.free → D
  | .inl x => x.val
  | .inr (.inl x) => M.face x.val.val
  | .inr (.inr x) => M.face (M.face x.val.val)

omit [Fintype D] [DecidableEq D] in
lemma expand_injective : Function.Injective H.expand := by
  rintro (a|(a|a)) (b|(b|b)) h
  · exact congrArg Sum.inl (Subtype.ext h)
  · have hh := congrArg H.role h
    change H.role a.val = H.role (M.face b.val.val) at hh
    rw [a.property,H.role_next0 b.property b.val.property] at hh
    contradiction
  · have hh := congrArg H.role h
    change H.role a.val = H.role (M.face (M.face b.val.val)) at hh
    rw [a.property,H.role_next1 (H.role_next0 b.property b.val.property)] at hh
    contradiction
  · have hh := congrArg H.role h
    change H.role (M.face a.val.val) = H.role b.val at hh
    rw [b.property,H.role_next0 a.property a.val.property] at hh
    contradiction
  · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext (Subtype.ext (M.face.injective h)))
  · have hh := congrArg H.role h
    change H.role (M.face a.val.val) = H.role (M.face (M.face b.val.val)) at hh
    rw [H.role_next0 a.property a.val.property,H.role_next1 (H.role_next0 b.property b.val.property)] at hh
    contradiction
  · have hh := congrArg H.role h
    change H.role (M.face (M.face a.val.val)) = H.role b.val at hh
    rw [b.property,H.role_next1 (H.role_next0 a.property a.val.property)] at hh
    contradiction
  · have hh := congrArg H.role h
    change H.role (M.face (M.face a.val.val)) = H.role (M.face b.val.val) at hh
    rw [H.role_next1 (H.role_next0 a.property a.val.property),H.role_next0 b.property b.val.property] at hh
    contradiction
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext (Subtype.ext (M.face.injective (M.face.injective h))))

omit [Fintype D] [DecidableEq D] in
lemma expand_surjective : Function.Surjective H.expand := by
  intro x
  rcases (show H.role x = 0 ∨ H.role x = 1 ∨ H.role x = 2 by omega) with hr|hr|hr
  · exact ⟨.inl ⟨x,hr⟩,rfl⟩
  · have ht := H.top_of_role (by rw [hr]; decide)
    refine ⟨.inr (.inl ⟨⟨M.face.symm x,H.role_prev1 hr⟩,?_⟩),?_⟩
    · exact (H.top_prev x).trans ht
    · exact M.face.apply_symm_apply x
  · have ht := H.top_of_role (by rw [hr]; decide)
    refine ⟨.inr (.inr ⟨⟨M.face x,H.role_next2 hr⟩,?_⟩),?_⟩
    · exact (H.top_face x).trans ht
    · exact H.period x ht

def expandEquiv : ConeExpansion.Point H.free ≃ D :=
  Equiv.ofBijective H.expand ⟨H.expand_injective,H.expand_surjective⟩

omit [Fintype D] [DecidableEq D] in
lemma expand_face (x : ConeExpansion.Point H.free) :
    H.expandEquiv ((ConeExpansion.map H.contraction H.free H.free_invariant).face x) =
      M.face (H.expandEquiv x) := by
  change H.expand ((ConeExpansion.map H.contraction H.free H.free_invariant).face x) = M.face (H.expand x)
  rcases x with a|(a|a)
  · by_cases ht : H.free a
    · simp only [ConeExpansion.map,ConeExpansion.face,Equiv.coe_fn_mk,dite_eq_left ht,
        expand]
    · have hh : H.top a.val = false := Bool.eq_false_iff.mpr ht
      simp only [ConeExpansion.map,ConeExpansion.face,Equiv.coe_fn_mk,dite_eq_right ht,
        expand,contraction,face,next,hh,Bool.false_eq_true,ite_false]
  · rfl
  · exact (H.period a.val.val a.property).symm

omit [Fintype D] [DecidableEq D] in
lemma expand_edge (x : ConeExpansion.Point H.free) :
    H.expandEquiv ((ConeExpansion.map H.contraction H.free H.free_invariant).edge x) =
      M.edge (H.expandEquiv x) := by
  rcases x with a|(a|a)
  · rfl
  · change M.face (M.face (H.next a.val.val)) = M.edge (M.face a.val.val)
    have hr := H.edge1 _ (H.role_next0 a.property a.val.property)
    have ht : H.top (M.edge (M.face a.val.val)) = true := H.top_of_role (by rw [hr]; decide)
    have ha : H.top a.val.val = true := a.property
    simp only [next,ha,ite_true]
    exact H.period _ ht
  · change M.face (H.prev a.val.val) = M.edge (M.face (M.face a.val.val))
    have ha : H.top a.val.val = true := a.property
    simp only [prev,ha,ite_true,apply_symm_apply,H.prev_eq ha]

/-- The contraction is a genuine genus-zero map with all old sides retained.
No surface classification, drawing, or asserted Euler correction is used. -/
theorem contraction_genusZero (h : M.GenusZero) : H.contraction.GenusZero := by
  apply ConeExpansion.genusZero_of_expansion
  exact (PictureMap.genusZero_equiv _ _ H.expandEquiv H.expand_face H.expand_edge).mpr h

end TriangleMarking
end PictureSwitch

/-! Local elementary triangle incidence induces the exact radial contraction. -/
namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

variable {A : Type*} [AddCommGroup A] (weight : G × ElementaryCell n w d → A)

variable (P : CellPicture (elementaryRawTarget n w d v hv hcell weight))

lemma elementaryContraction_genusZero :
    (elementaryMarking n w d v hv hcell weight P).contraction.GenusZero :=
  TriangleMarking.contraction_genusZero _ P.genusZero

end

/-! Exact deck coordinates on the old and two radial sides of every triangle. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

lemma elementary_old_label (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementarySideRole n w d v hv hcell s = 0) :
    (elementaryLiftedBoundary n w d v hv hcell).sideLabel s =
      ((elementaryWalkIndex n w d v hv hcell s).1 *
        coverOffset n w d v (elementaryWalkIndex n w d v hv hcell s).2,
        elementaryOld n w (walkLabel n w d (elementaryWalkIndex n w d v hv hcell s).2)) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · have hi : i = (1 : Fin 3) := by
      cases b <;> fin_cases i <;> first | rfl | cases h
    subst i
    cases b with
    | false =>
      change (g * elementaryOffset n w d v (.inl c) (1 : Fin 3) *
        v (macroStep n w c.1 (macroCellDart c.2).adj),
        elementaryOld n w (rev n w (macroStep n w c.1 (macroCellDart c.2).adj))) =
        (g * macroPotential n w v c.1 (macroCellDart c.2).snd,
         elementaryOld n w (macroStep n w c.1 (macroCellDart c.2).symm.adj))
      apply Prod.ext
      · exact (congrArg (fun z => g * z * v (macroStep n w c.1 (macroCellDart c.2).adj))
          (elementaryOffset_triangle_one n w d v c.1 c.2)).trans
          ((mul_assoc _ _ _).trans (congrArg (g * ·)
            (macroPotential_edge n w d v hv hcell c.1 (macroCellDart c.2).adj)))
      · exact congrArg (elementaryOld n w)
          (macroStep_reverse n w c.1 (macroCellDart c.2).adj).symm
    | true =>
      change (g * elementaryOffset n w d v (.inl c) (1 : Fin 3),_) = (g * macroPotential n w v c.1 _,_)
      rw [elementaryOffset_triangle_one]
      rfl
  · change Fin ((frozenBoundary n w d).size c) at i
    cases b with
    | false =>
      change (g * elementaryOffset n w d v (.inr c) i * v ((frozenBoundary n w d).label c i),_) =
        (g * (_ * v ((frozenBoundary n w d).label c i)),_)
      rw [elementaryOffset_frozen n w d v g,mul_assoc]
      rfl
    | true =>
      change (g * elementaryOffset n w d v (.inr c) i,_) = (g * _,_)
      rw [elementaryOffset_frozen n w d v g]
      rfl

end

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

variable {A : Type*} [AddCommGroup A]
  (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

lemma elementary_frozen_kind (s : ElementaryLiftSide n w d v hv hcell)
    (hs : elementaryTop n w d v hv hcell s = false) :
    (liftedWalkTarget n w d v hv hcell tc hc fc).kind
      (elementaryWalkIndex n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).kind (elementaryWalkIndex n w d v hv hcell s) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases hs
  · rfl

lemma elementary_frozen_closed (s : ElementaryLiftSide n w d v hv hcell)
    (hs : elementaryTop n w d v hv hcell s = false) :
    (liftedWalkTarget n w d v hv hcell tc hc fc).front
      (elementaryWalkIndex n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).back (elementaryWalkIndex n w d v hv hcell s) := by
  let B := elementaryLiftedBoundary n w d v hv hcell
  have hh := B.next_start s
  rw [elementary_old_label n w d v hv hcell (B.next s)
    (elementaryRole_frozen n w d v hv hcell _ ((elementaryTop_next n w d v hv hcell s).trans hs)),
    elementary_old_label n w d v hv hcell s (elementaryRole_frozen n w d v hv hcell s hs)] at hh
  have hp := congrArg Prod.fst hh
  have hq := congrArg Prod.snd hh
  change _ = _ * elementaryVoltage n w v (elementaryOld n w
     (walkLabel n w d (elementaryWalkIndex n w d v hv hcell s).2)) at hp
  change _ = _ * v (walkLabel n w d (elementaryWalkIndex n w d v hv hcell s).2) at hp
  rw [mul_assoc, ← coverOffset_opposite n w d v hv hcell] at hp
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases hs
  · apply Prod.ext
    · exact hp
    · exact congrArg Sum.inr (Sum.inl.inj hq)

end

/-! Every genuine elementary genus-zero picture contracts to the unchanged
macro/frozen target, preserving the literal original-group deck coordinates. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
variable {A : Type*} [AddCommGroup A] (weight : G × ElementaryCell n w d → A)
  (P : CellPicture (elementaryRawTarget n w d v hv hcell weight))

lemma elementaryContract_top_next (x : ElementaryBases n w d v hv hcell weight P)
    (ht : (elementaryMarking n w d v hv hcell weight P).free x) :
    ∃ (g : G) (a : Top n w) (e f : MacroGraph.graph.Dart),
      elementaryContractIndex n w d v hv hcell weight P x = (g,.inl (a,e)) ∧
      elementaryContractIndex n w d v hv hcell weight P
        ((elementaryMarking n w d v hv hcell weight P).contraction.face x) = (g,.inl (a,f)) ∧
      f.fst = e.snd := by
  let H := elementaryMarking n w d v hv hcell weight P
  let y := H.contraction.face x
  have hyt : H.free y := (H.free_invariant x).mpr ht
  rcases hx : elementaryContractIndex n w d v hv hcell weight P x with ⟨g,s|s⟩
  · rcases s with ⟨a,e⟩
    rcases hy : elementaryContractIndex n w d v hv hcell weight P y with ⟨k,t|t⟩
    · rcases t with ⟨b,f⟩
      have hf2 : P.pairing.face (P.pairing.face y.val) = P.pairing.edge (P.pairing.face x.val) :=
        H.expand_edge (.inr (.inl ⟨x,ht⟩))
      have hp := P.respects.2 (P.pairing.face x.val)
      change (elementaryLiftedBoundary n w d v hv hcell).sideLabel
        (P.index (P.pairing.edge (P.pairing.face x.val))) =
        (elementaryLiftedBoundary n w d v hv hcell).rev
          ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.face x.val))) at hp
      rw [← hf2,P.mapped.commute,P.mapped.commute,P.mapped.commute] at hp
      change (elementaryLiftedBoundary n w d v hv hcell).sideLabel
        ((elementaryLiftedBoundary n w d v hv hcell).next
          ((elementaryLiftedBoundary n w d v hv hcell).next (P.index y.val))) =
        (elementaryLiftedBoundary n w d v hv hcell).rev
          ((elementaryLiftedBoundary n w d v hv hcell).sideLabel
            ((elementaryLiftedBoundary n w d v hv hcell).next (P.index x.val))) at hp
      rw [elementary_outgoing n w d v hv hcell (P.index y.val) y.property k b f hy,
        elementary_incoming n w d v hv hcell (P.index x.val) x.property g a e hx] at hp
      change (k,Sum.inr (b,f.fst),true) =
        (g * macroPotential n w v a e.snd * (macroPotential n w v a e.snd)⁻¹,Sum.inr (a,e.snd),true) at hp
      rw [mul_inv_cancel_right] at hp
      have hg : k = g := congrArg Prod.fst hp
      have hab : (b,f.fst) = (a,e.snd) := Sum.inr.inj (congrArg (fun z => z.2.1) hp)
      have ha : b = a := congrArg Prod.fst hab
      have hef : f.fst = e.snd := congrArg Prod.snd hab
      subst k; subst b
      exact ⟨g,a,e,f,rfl,rfl,hef⟩
    · have hh : elementaryTop n w d v hv hcell (P.index y.val) = true := hyt
      rw [elementaryTop_walk] at hh
      change walkFree n w d (walkKind n w d (elementaryContractIndex n w d v hv hcell weight P y).2) = true at hh
      rw [hy] at hh
      cases hh
  · have hh : elementaryTop n w d v hv hcell (P.index x.val) = true := ht
    rw [elementaryTop_walk] at hh
    change walkFree n w d (walkKind n w d (elementaryContractIndex n w d v hv hcell weight P x).2) = true at hh
    rw [hx] at hh
    cases hh

lemma elementaryContract_frozen_next (x : ElementaryBases n w d v hv hcell weight P)
    (ht : ¬ (elementaryMarking n w d v hv hcell weight P).free x) :
    ((elementaryMarking n w d v hv hcell weight P).contraction.face x).val = P.pairing.face x.val := by
  have ht' : (elementaryMarking n w d v hv hcell weight P).top x.val = false := Bool.eq_false_iff.mpr ht
  change TriangleMarking.next _ _ = _
  simp only [TriangleMarking.next,ht',Bool.false_eq_true,ite_false]

variable (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

lemma elementaryContract_incidence (x : ElementaryBases n w d v hv hcell weight P) :
    (liftedWalkTarget n w d v hv hcell tc hc fc).kind
      (elementaryContractIndex n w d v hv hcell weight P
        ((elementaryMarking n w d v hv hcell weight P).contraction.face x)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).kind (elementaryContractIndex n w d v hv hcell weight P x) ∧
    (liftedWalkTarget n w d v hv hcell tc hc fc).front
      (elementaryContractIndex n w d v hv hcell weight P
        ((elementaryMarking n w d v hv hcell weight P).contraction.face x)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).back (elementaryContractIndex n w d v hv hcell weight P x) := by
  by_cases ht : (elementaryMarking n w d v hv hcell weight P).free x
  · obtain ⟨g,a,e,f,hx,hy,hf⟩ := elementaryContract_top_next n w d v hv hcell weight P x ht
    rw [hy,hx]
    constructor
    · rfl
    · change (g * macroPotential n w v a f.fst,Sum.inl (a,f.fst)) =
        (g * macroPotential n w v a e.snd,Sum.inl (a,e.snd))
      rw [hf]
  · have ht' : elementaryTop n w d v hv hcell (P.index x.val) = false := Bool.eq_false_iff.mpr ht
    have hf := elementaryContract_frozen_next n w d v hv hcell weight P x ht
    unfold elementaryContractIndex
    rw [hf,P.mapped.commute]
    exact ⟨elementary_frozen_kind n w d v hv hcell tc hc fc _ ht',
      elementary_frozen_closed n w d v hv hcell tc hc fc _ ht'⟩

lemma elementaryContract_paired (x : ElementaryBases n w d v hv hcell weight P) :
    (liftedWalkTarget n w d v hv hcell tc hc fc).label
      (elementaryContractIndex n w d v hv hcell weight P
        ((elementaryMarking n w d v hv hcell weight P).contraction.edge x)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).rev
        ((liftedWalkTarget n w d v hv hcell tc hc fc).label (elementaryContractIndex n w d v hv hcell weight P x)) := by
  let H := elementaryMarking n w d v hv hcell weight P
  have hp := P.respects.2 x.val
  change (elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.edge x.val)) =
    (elementaryLiftedBoundary n w d v hv hcell).rev
    ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index x.val)) at hp
  rw [elementary_old_label n w d v hv hcell _ (H.edge0 _ x.property),
    elementary_old_label n w d v hv hcell _ x.property] at hp
  change ((elementaryWalkIndex n w d v hv hcell (P.index (P.pairing.edge x.val))).1 *
      coverOffset n w d v (elementaryWalkIndex n w d v hv hcell (P.index (P.pairing.edge x.val))).2,
      walkLabel n w d (elementaryWalkIndex n w d v hv hcell (P.index (P.pairing.edge x.val))).2) =
    ((elementaryWalkIndex n w d v hv hcell (P.index x.val)).1 *
      coverOffset n w d v (elementaryWalkIndex n w d v hv hcell (P.index x.val)).2 *
      v (walkLabel n w d (elementaryWalkIndex n w d v hv hcell (P.index x.val)).2),
      rev n w (walkLabel n w d (elementaryWalkIndex n w d v hv hcell (P.index x.val)).2))
  apply Prod.ext
  · exact congrArg (fun z : G × ElementaryDart n w => z.1) hp
  · exact elementaryOld_injective n w (congrArg (fun z : G × ElementaryDart n w => z.2) hp)

/-- A constructed macro picture, not an extra producer hypothesis. Exact
coordinate equality and frozen indexing are proved separately below. -/
def elementaryMacroPicture : WalkPicture (liftedWalkTarget n w d v hv hcell tc hc fc) where
  Dart := ElementaryBases n w d v hv hcell weight P
  pairing := (elementaryMarking n w d v hv hcell weight P).contraction
  index := elementaryContractIndex n w d v hv hcell weight P
  closed x := (elementaryContract_incidence n w d v hv hcell weight P tc hc fc x).2
  kind x := (elementaryContract_incidence n w d v hv hcell weight P tc hc fc x).1
  paired := elementaryContract_paired n w d v hv hcell weight P tc hc fc
  genusZero := elementaryContraction_genusZero n w d v hv hcell weight P

end

/-! The radial contraction preserves every independent lifted elementary-cell
coefficient, not just an augmentation or a projection to the old edges. -/

/-! Every genus-zero picture over the literal elementary lifted-cell boundary
has zero FULL cellular chain, by exact radial contraction. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u v z

end ConeSkeleton

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The original presentation maps to the elementary edge-bouquet group.
No fundamental-group equivalence, asphericity, or infinitude is assumed here. -/
def elementaryComparison : LetterPresentation.Group n w d →* ElementaryPolygonGroup n w d :=
  QuotientGroup.lift (Subgroup.normalClosure
    (show Set (FreeGroup (Fin (n+1))) from Relator n w d))
    (elementaryFreeComparison n w d) (elementaryRelatorClosure_le n w d)

lemma elementaryComparison_letter (a : Alphabet n) :
    elementaryComparison n w d (LetterPresentation.letter n w d a) =
      elementaryPolygonValue n w d (elementaryOld n w (letterDart n w a)) :=
  elementaryFreeComparison_letter n w d a

end

open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch SimpleGraph
attribute [local instance] Classical.propDecidable

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma radial_gauge (f : Fan n w) (v : FanVertex f.val.1) :
    oldGauge n w d (.inr f) * elementaryComparison n w d
      (letterVoltage n w d (.inr ⟨f,v⟩,true)) =
        elementaryOldValue n w d (.inr ⟨f,v⟩,true) := by
  let c := elementaryOldValue n w d
  let l := extendRow n (.inl f.val.1) f.val.2
  let p := CoreWordGraph.toMaster (fan f.val.1) (CoreWordGraph.fanRoute f.val.1 v)
  have he := MasterGraph.Path.eval_potential
    (fanPotential n w c f) ((c ∘ letterDart n w) ∘ l) p (by
      intro k hk
      obtain ⟨e,rfl,hm⟩ := CoreWordGraph.toMaster_fields (fan f.val.1)
        (CoreWordGraph.fanRoute f.val.1 v) k hk
      have hh := fanPotential_edge n w d c (elementaryOldValue_rev n w d)
        (elementaryOldValue_cell n w d) f e hm
      simpa only [Function.comp_apply,l,extendRow,dite_eq_left (show (.inl e : Field) ∈ rowSupport (.inl f.val.1)
        from by simpa [rowSupport] using hm)] using hh)
  rw [MasterGraph.Path.eval_comp] at he
  have hv : elementaryComparison n w d (letterVoltage n w d (.inr ⟨f,v⟩,true)) =
      p.eval l (c ∘ letterDart n w) := by
    change elementaryFreeComparison n w d (FreeGroup.mk (radialWord n w f v)) = _
    rw [radialWord,← CoreWordGraph.toMaster_word, mk_pathWord,MasterGraph.Path.eval_map]
    simp only [elementaryFreeComparison_letter]
    rfl
  rw [hv]
  simpa only [fanPotential,dite_eq_left (base_fanVertex f.val.1),dite_eq_left v.property,
    radialValue,oldGauge,fanBase,c,p] using he

/-- Every old edge equals its prescribed letter voltage, up to endpoint gauge.
This removes the extra free factors of the edge-bouquet only on CLOSED paths. -/
lemma old_gauge (e : Dart n w) :
    elementaryOldValue n w d e = oldGauge n w d (start n w e) *
      elementaryComparison n w d (letterVoltage n w d e) *
        (oldGauge n w d (start n w (rev n w e)))⁻¹ := by
  rcases e with ⟨i|⟨f,v⟩,b⟩
  · have he : (.inl i,b) = letterDart n w (i,b) := rfl
    rw [he,letterVoltage_letter,elementaryComparison_letter]
    simp only [start_letter,rev_letter,oldGauge,one_mul,inv_one,mul_one]
  · cases b with
    | true =>
      simpa only [start,rev,Bool.not_true,oldGauge,inv_one,mul_one] using
        (radial_gauge n w d f v).symm
    | false =>
      have he := congrArg Inv.inv (radial_gauge n w d f v).symm
      have hr := elementaryOldValue_rev n w d (.inr ⟨f,v⟩,true)
      have hv := letterVoltage_rev n w d (.inr ⟨f,v⟩,true)
      change letterVoltage n w d (.inr ⟨f,v⟩,false) = _ at hv
      change elementaryOldValue n w d (.inr ⟨f,v⟩,false) = _ at hr
      rw [hr,hv,map_inv]
      simpa only [start,rev,Bool.not_false,oldGauge,one_mul,mul_inv_rev] using he

lemma macro_old_gauge (a : Top n w) {u v : MacroGraph.Vertex} (p : MacroGraph.graph.Walk u v) :
    GraphGroupWalk.eval (macroValue n w (elementaryOldValue n w d) a) p =
      oldGauge n w d (macroVertex n w a u) *
        elementaryComparison n w d (GraphGroupWalk.eval (macroValue n w (letterVoltage n w d) a) p) *
          (oldGauge n w d (macroVertex n w a v))⁻¹ := by
  induction p with
  | nil => simp only [GraphGroupWalk.eval_nil,map_one,mul_one,mul_inv_cancel]
  | @cons u v z h p ih =>
    simp only [GraphGroupWalk.eval_cons,macroValue]
    change MacroGraph.Adjacent u v at h
    change elementaryOldValue n w d (macroStep n w a h) *
        GraphGroupWalk.eval (macroValue n w (elementaryOldValue n w d) a) p =
      oldGauge n w d (macroVertex n w a u) *
        elementaryComparison n w d (letterVoltage n w d (macroStep n w a h) *
          GraphGroupWalk.eval (macroValue n w (letterVoltage n w d) a) p) *
        (oldGauge n w d (macroVertex n w a z))⁻¹
    rw [old_gauge,macroStep_start,macroStep_end,ih,map_mul]
    group

lemma top_radial_gauge (a : Top n w) (v : MacroGraph.Vertex) :
    elementaryPolygonValue n w d (.inr (a,v),true) =
      elementaryGauge n w d (.inr a) * elementaryComparison n w d
        (elementaryVoltage n w (letterVoltage n w d) (.inr (a,v),true)) *
          (elementaryGauge n w d (.inl (macroVertex n w a v)))⁻¹ := by
  have he := GraphGroupWalk.eval_potential
    (macroValue n w (elementaryOldValue n w d) a)
    (fun v => elementaryPolygonValue n w d (.inr (a,v),true))
    (elementary_radial_relation n w d (elementaryPolygonValue n w d)
      (elementaryPolygonValue_rev n w d) (elementaryPolygonValue_cell n w d) a)
    (MacroGraph.route v)
  rw [macro_old_gauge] at he
  simpa only [elementaryGauge,elementaryVoltage,macroPotential,mul_assoc] using he.symm

/-- The full elementary graph has exactly its prescribed voltages modulo
endpoint gauges, proved using the literal fan and top cone triangles. -/
theorem elementary_gauge (e : ElementaryDart n w) :
    elementaryPolygonValue n w d e = elementaryGauge n w d (elementaryStart n w e) *
      elementaryComparison n w d (elementaryVoltage n w (letterVoltage n w d) e) *
        (elementaryGauge n w d (elementaryStart n w (elementaryRev n w e)))⁻¹ := by
  rcases e with ⟨i|⟨a,v⟩,b⟩
  · exact old_gauge n w d (i,b)
  · cases b with
    | true => exact top_radial_gauge n w d a v
    | false =>
      have he := congrArg Inv.inv (top_radial_gauge n w d a v)
      have hr := elementaryPolygonValue_rev n w d (.inr (a,v),true)
      change elementaryPolygonValue n w d (.inr (a,v),false) = _ at hr
      rw [hr]
      simpa only [elementaryStart,elementaryRev,Bool.not_false,
        elementaryVoltage,map_inv,mul_inv_rev,inv_inv,mul_assoc] using he

end ConeSkeleton

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Positive voltages of the genuine elementary indexed edges. -/
def elementaryPositiveVoltage (e : ElementaryEdge n w) : LetterPresentation.Group n w d :=
  elementaryVoltage n w (letterVoltage n w d) (e,true)

lemma elementaryVoltage_signed (e : ElementaryDart n w) :
    elementaryVoltage n w (letterVoltage n w d) e =
      VoltageWords.voltage (elementaryPositiveVoltage n w d) e := by
  rcases e with ⟨e,b⟩
  cases b with
  | true => rfl
  | false => exact elementaryVoltage_rev n w (letterVoltage n w d) (letterVoltage_rev n w d) (e,true)

lemma elementaryTotal_cell (c : ElementaryCell n w d) :
    VoltageWords.total (elementaryPositiveVoltage n w d) ((elementaryBoundary n w d).attachingWord c) = 1 := by
  simp only [VoltageWords.total,PolygonTarget.Boundary.attachingWord,List.map_ofFn,Function.comp_def,
    ← elementaryVoltage_signed]
  exact elementaryLetterVoltage_cell n w d c

/-- Same individual cells and deck coordinates as `elementaryLetterLiftedBoundary`,
encoded using signed positive lifted edges rather than shifted dart reversal. -/
def elementaryEncodedBoundary := VoltageWords.liftedBoundary (elementaryBoundary n w d)
  (elementaryPositiveVoltage n w d) rfl (elementaryTotal_cell n w d)

end

/-! Signed-edge encoding preserves all individual cell identities and the
closed-picture chain. Sphere vanishing therefore applies to indexed disks. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma elementaryEncoded_label (c : LetterPresentation.Group n w d × ElementaryCell n w d)
    (i : Fin (elementarySize n w d c.2)) :
    (elementaryEncodedBoundary n w d).label c i =
      VoltageWords.encode (elementaryPositiveVoltage n w d)
        ((elementaryLetterLiftedBoundary n w d).label c i) := by
  simp only [elementaryEncodedBoundary,VoltageWords.liftedBoundary,
    elementaryLetterLiftedBoundary,elementaryLiftedBoundary,elementaryOffset,
    elementaryBoundary,elementaryVoltage_signed,Function.comp_def]

lemma elementaryEncoded_rev (e : LetterPresentation.Group n w d × ElementaryDart n w) :
    VoltageWords.encode (elementaryPositiveVoltage n w d)
      ((elementaryLetterLiftedBoundary n w d).rev e) =
      invLetter (VoltageWords.encode (elementaryPositiveVoltage n w d) e) := by
  change VoltageWords.encode _ (e.1 * elementaryVoltage n w (letterVoltage n w d) e.2,
    invLetter e.2) = _
  rw [elementaryVoltage_signed]
  exact VoltageWords.encode_reverse _ _ _

lemma elementaryEncoded_side (s : (elementaryEncodedBoundary n w d).Side) :
    (elementaryEncodedBoundary n w d).sideLabel s =
      VoltageWords.encode (elementaryPositiveVoltage n w d)
        ((elementaryLetterLiftedBoundary n w d).sideLabel s) := by
  rcases s with ⟨c,b,i⟩
  change Fin (elementarySize n w d c.2) at i
  cases b with
  | true => exact elementaryEncoded_label n w d c i
  | false =>
    change invLetter ((elementaryEncodedBoundary n w d).label c i) =
      VoltageWords.encode _ ((elementaryLetterLiftedBoundary n w d).rev
        ((elementaryLetterLiftedBoundary n w d).label c i))
    rw [elementaryEncoded_rev,elementaryEncoded_label]

variable {A : Type*} [AddCommGroup A]
  (weight : (LetterPresentation.Group n w d × ElementaryCell n w d) → A)

/-- Decode only the edge alphabet. Every cell, side, face and coefficient is
unchanged. The geometric incidence conditions follow from the actual target. -/
def elementaryDecodePicture
    (P : CellPicture ((elementaryEncodedBoundary n w d).target weight
      (fun _ => false) (by intro _ h; cases h))) :
    CellPicture (elementaryRawTarget n w d (letterVoltage n w d)
      (letterVoltage_rev n w d) (letterVoltage_cell n w d) weight) where
  Dart := P.Dart
  pairing := P.pairing
  genusZero := P.genusZero
  index := P.index
  mapped := P.mapped
  respects := (elementaryRawTarget n w d (letterVoltage n w d)
    (letterVoltage_rev n w d) (letterVoltage_cell n w d) weight).respects_of_edge
      P.pairing P.index P.mapped (by
        intro x
        change (elementaryLetterLiftedBoundary n w d).sideLabel (P.index (P.pairing.edge x)) =
          (elementaryLetterLiftedBoundary n w d).rev
            ((elementaryLetterLiftedBoundary n w d).sideLabel (P.index x))
        apply (VoltageWords.encode (elementaryPositiveVoltage n w d)).injective
        rw [elementaryEncoded_rev,←elementaryEncoded_side,←elementaryEncoded_side]
        exact P.respects.2 x)

end

/-! Actual integral boundaries for the uncompressed cone cells. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch IntegralIncidence

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def letterBoundary₂ : LetterC₂ n w d →ₗ[ℤ] LetterC₁ n w d :=
  (elementaryPolygons n w d).d₂ (elementaryVoltage n w (letterVoltage n w d))

end ConeSkeleton

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

namespace IncidenceTemplate

section
open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
attribute [local instance] Classical.propDecidable

abbrev finalSize (m : ℕ) := (finalDiagramStage m).size
abbrev finalMaster (m : ℕ) := (finalDiagramStage m).master
abbrev finalSix (m : ℕ) := (finalDiagramStage m).six

end

/-! Arbitrary-valued cell cochains of the same chosen arrays extend to edges.
This is the full polygonal obstruction extension, not only a basis-vector
injectivity statement. -/

open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
attribute [local instance] Classical.propDecidable

end IncidenceTemplate

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

namespace ConeSkeleton
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
attribute [local instance] Classical.propDecidable

def elementaryBasepoint : elementaryPolyhedron n w d :=
  vertex (elementarySimplicialComplex n w d) (elementaryBaseVertex n w d)

def elementaryFiniteHomeomorph :
    elementaryPolyhedron n w d ≃ₜ (elementaryFiniteComplex n w d).Carrier :=
  toFiniteComplexHomeomorph (elementarySimplicialComplex n w d)

def elementaryFiniteBasepoint : (elementaryFiniteComplex n w d).Carrier :=
  elementaryFiniteHomeomorph n w d (elementaryBasepoint n w d)

end ConeSkeleton

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

namespace ConeSkeleton

section
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def elementaryLetterToTopology : LetterPresentation.Group n w d →* ElementaryPiOne n w d :=
  (elementaryPolygonToTopology n w d).comp (elementaryComparison n w d)

attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryVertex_1
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryEdge_1
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryCell_1
lemma elementaryLetterToTopology_letter (a : Alphabet n) :
    elementaryLetterToTopology n w d (LetterPresentation.letter n w d a) =
      (elementaryPolygonData n w d).graphTransport (elementaryRootedVoltage n w d)
        (elementaryOld n w (letterDart n w a)) := by
  rw [elementaryLetterToTopology,MonoidHom.comp_apply,elementaryComparison_letter,
    elementaryPolygonToTopology_value]

lemma elementaryLetterToTopology_surjective : Function.Surjective (elementaryLetterToTopology n w d) := by
  apply MonoidHom.range_eq_top.mp
  apply (elementaryPolygonData n w d).rooted_group_generated
    (elementaryRoot n w) (elementaryOldRoutes n w d)
  · intro e
    refine ⟨elementaryVoltage n w (letterVoltage n w d) e,?_⟩
    have he := congrArg (elementaryPolygonToTopology n w d) (elementary_gauge n w d e)
    rw [elementaryPolygonToTopology_value,map_mul,map_mul,map_inv,
      elementary_gauge_toTopology,elementary_gauge_toTopology,one_mul,inv_one,mul_one] at he
    exact he.symm
  · rfl

end

/-! Injectivity of the actual pi1 comparison, detected by the genuine
voltage covering. -/

open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma elementarySignedVoltage (e : ElementaryDart n w) :
    Data.signed (fun e => elementaryVoltage n w (letterVoltage n w d) (e,true)) e =
      elementaryVoltage n w (letterVoltage n w d) e := by
  rcases e with ⟨e,b⟩
  cases b
  · exact (elementaryVoltage_rev n w (letterVoltage n w d)
      (letterVoltage_rev n w d) (e,true)).symm
  · rfl

attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryVertex_2
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryEdge_2
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryCell_2
def elementarySourceVoltage : Voltage (elementarySimplicialComplex n w d) (LetterPresentation.Group n w d) :=
  (elementaryPolygonData n w d).voltage
    (fun e => elementaryVoltage n w (letterVoltage n w d) (e,true)) (by
      intro c
      simpa only [elementarySignedVoltage, elementaryPolygonData] using elementaryLetterVoltage_cell n w d c)

attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instTopologicalSpaceGroup
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDiscreteTopologyGroup
def elementaryTopologyToLetter : ElementaryPiOne n w d →* LetterPresentation.Group n w d :=
  (elementarySourceVoltage n w d).detect (elementaryBaseVertex n w d)

lemma elementaryLetterToTopology_loop (i : Fin (n+1)) :
    elementaryLetterToTopology n w d (LetterPresentation.letter n w d (i,true)) =
      MulOpposite.op ((elementaryPolygonData n w d).graphChain
        (elementaryOld n w (letterDart n w (i,true)))).pathClass := by
  rw [elementaryLetterToTopology_letter,Data.rooted_graphChain]
  exact RootedPaths.based_loop _ _ rfl _

lemma elementaryTopologyToLetter_letter (i : Fin (n+1)) :
    elementaryTopologyToLetter n w d
      (elementaryLetterToTopology n w d (LetterPresentation.letter n w d (i,true))) =
        LetterPresentation.letter n w d (i,true) := by
  rw [elementaryLetterToTopology_loop]
  change (elementarySourceVoltage n w d).detect _ (MulOpposite.op _) = _
  refine (Voltage.detect_chain (elementarySourceVoltage n w d) (elementaryBaseVertex n w d)
    ((elementaryPolygonData n w d).graphChain (elementaryOld n w (letterDart n w (i,true))))).trans ?_
  refine (Data.graphChain_eval (elementaryPolygonData n w d) (elementarySourceVoltage n w d)
    (elementaryOld n w (letterDart n w (i,true)))).trans ?_
  change (elementaryPolygonData n w d).graphTransport ((elementaryPolygonData n w d).voltage _ _) _ = _
  rw [Data.graphTransport_voltage,elementarySignedVoltage]
  exact letterVoltage_letter n w d (i,true)

lemma elementaryTopology_leftInverse :
    (elementaryTopologyToLetter n w d).comp (elementaryLetterToTopology n w d) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  exact elementaryTopologyToLetter_letter n w d i

lemma elementaryLetterToTopology_injective : Function.Injective (elementaryLetterToTopology n w d) := by
  apply Function.LeftInverse.injective (f := elementaryLetterToTopology n w d)
    (g := elementaryTopologyToLetter n w d)
  intro x
  exact DFunLike.congr_fun (elementaryTopology_leftInverse n w d) x

/-- The actual letter group equals the actual topological pi1-op of the finite
literal elementary polygon realization. -/
def elementaryTopologyEquiv : LetterPresentation.Group n w d ≃* ElementaryPiOne n w d :=
  MulEquiv.ofBijective (elementaryLetterToTopology n w d)
    ⟨elementaryLetterToTopology_injective n w d,elementaryLetterToTopology_surjective n w d⟩

end ConeSkeleton

section

/-! The arbitrary obstruction cochain on the literal collar triangles of the
SAME chosen arrays extends to their literal directed lifted edges. -/

namespace IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (m : ℕ) (B : Type) [AddCommGroup B]
variable (T : (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) → Data.Position (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)) → Fin 3 → B)

def finalTrianglePolygonWeight (x : (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) × ElementaryCell (finalSize m) (finalMaster m) (finalSix m)) : B :=
  ∑ i : Fin ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).size x.2), ∑ j : Fin 3,
    (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).triangleWeight T (x.1 * (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).cornerOffset (fun e => elementaryVoltage (finalSize m) (finalMaster m) (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) ⟨x.2,(i,j)⟩) ⟨x.2,(i,j)⟩

def finalTriangleEdgeWeight (x : (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) × ElementaryEdge (finalSize m) (finalMaster m)) : B :=
  IndexedFilling.leftInverse (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m))
    (finalTrianglePolygonWeight m B T) (Finsupp.single x 1)

end IncidenceTemplate
end

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

namespace ConeSkeleton
attribute [local instance] Classical.propDecidable
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instTopologicalSpaceGroup_2
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDiscreteTopologyGroup_2
abbrev elementaryUniversalBasepoint : (elementarySourceVoltage n w d).TotalSpace :=
  ((elementarySourceVoltage n w d).vertexFiber (elementaryBaseVertex n w d) 1).val

/-- This is the literal cover already proved simply connected, not an abstract
cover named in a premise. -/
def elementaryHigherCoverEquiv (k : ℕ) :
    HomotopyGroup.Pi (k+2) (elementarySourceVoltage n w d).TotalSpace
      (elementaryUniversalBasepoint n w d) ≃
    HomotopyGroup.Pi (k+2) (elementaryFiniteComplex n w d).Carrier
      (elementaryFiniteBasepoint n w d) :=
  HigherCovering.homotopyEquiv
    ((elementarySourceVoltage n w d).isCoveringMap.homeomorph_comp
      (elementaryFiniteHomeomorph n w d)) (elementaryUniversalBasepoint n w d)

end ConeSkeleton

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

namespace FinitePolyhedron.EdgePresentation
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

def chainWord {a b : V} : EdgeChain K a b → WordPictures.Word (Generator K)
  | .nil _ => []
  | .cons (a := a) (b := b) h p => (⟨(a,b),h⟩,true) :: chainWord p

variable (o : V) (R : ∀ a, EdgeChain K o a)
inductive WordRelation : WordPictures.Word (Generator K) → Prop
  | self (a : V) : WordRelation [(⟨(a,a),edge_self K a⟩,true)]
  | triangle {a b c : V} (h : {a,b,c} ∈ K.faces)
      (hab : {a,b} ∈ K.faces) (hbc : {b,c} ∈ K.faces) (hac : {a,c} ∈ K.faces) :
      WordRelation [(⟨(a,b),hab⟩,true),(⟨(b,c),hbc⟩,true),(⟨(a,c),hac⟩,false)]
  | route (a : V) : WordRelation (chainWord K (R a))

def wordToTopology (hR : R o = .nil o) : FreeGroup (Generator K) →* RootedPaths.PiOne (K := K) o :=
  (toTopology K o R hR).comp (PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R))

end FinitePolyhedron.EdgePresentation

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

namespace FiniteComplex

section
open FinitePolyhedron FinitePolyhedron.EdgeChain
variable (K : FiniteComplex) (o : K.Vertex) (R : ∀ a, K.Chain o a)
abbrev EdgeGenerator := EdgePresentation.Generator K.complex

def generatorChain (e : K.EdgeGenerator) : K.Chain o o := based o R (single e.property)
def signedChain (e : K.EdgeGenerator × Bool) : K.Chain o o :=
  if e.2 then generatorChain K o R e.1 else (generatorChain K o R e.1).reverse

def wordChain : WordPictures.Word K.EdgeGenerator → K.Chain o o
  | [] => .nil o
  | e::z => (signedChain K o R e).append (wordChain z)

end

/-! The challenge's literal disk moves preserve every triangular voltage.
This is valid even for the untyped intermediate lists in DiskHomotopy. -/
open FinitePolyhedron

end FiniteComplex

/-! Group-isomorphism transport for geometric actions. -/

section

/-! Transfer of linear word filling to literal triangular disk filling.
All disk-null loops are handled,
with the same list length convention `length - 1`. -/

namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}

def ofListEnd (a b : K.Vertex) (t : List K.Vertex)
    (h : K.EdgePath (a :: (t ++ [b]))) : K.Chain a b :=
  match t with
  | [] => single h.1
  | c :: t => .cons h.1 (ofListEnd c b t h.2)

end FinitePolyhedron.EdgeChain

end

/-! Actual homotopy-equivalence invariance of the fundamental group. -/

/-! The literal finite barycentric complex has exactly the original letter group,
not a conditional presentation of it. -/

namespace ConeSkeleton

section
universe u
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def elementaryFinitePiOneEquiv : LetterPresentation.Group n w d ≃*
    FundamentalGroup (elementaryFiniteComplex n w d).Carrier (elementaryFiniteBasepoint n w d) :=
  (elementaryTopologyEquiv n w d).trans ((groupOppositeEquiv _).trans
    (fundamentalGroupHomotopyEquiv (elementaryFiniteHomeomorph n w d).toHomotopyEquiv
      (elementaryBasepoint n w d)))

end

/-! Infinitude can be obtained without a topological Euler theorem: the many
six-letter cells alone inject into the original letter-edge module of any
finite cover. Their cardinality exceeds the number of original generators. -/

open IncidenceTemplate CoreGeometry LetterPresentation IntegralIncidence
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def sixFaceBoundary (c : LetterPresentation.Group n w d × Six n d) : OriginalEdgeChain n w d :=
  ∑ i : Fin 6, edgeChain (fun a : Alphabet n =>
    elementaryVoltage n w (letterVoltage n w d) ((.inl (.inl a.1)),a.2))
      (c.1 * elementaryOffset n w d (letterVoltage n w d) (sixCellIndex n w d c).2 i,
        c.2.val i)

def sixBoundary : SixChain n w d →ₗ[ℤ] OriginalEdgeChain n w d :=
  Finsupp.linearCombination ℤ (sixFaceBoundary n w d)

end ConeSkeleton

/-! The same supplied final arrays yield infinite groups unconditionally.
This discharges the last group-action-side hypothesis; the finite-polyhedron
realization and group-to-topology consequences are still separate obligations. -/
namespace IncidenceTemplate

section
open CoreGeometry LetterPresentation ConeSkeleton

/-! The selected presentations give actual connected finite polyhedra
whose fundamental groups admit no geometric CAT(0) action. -/
open CoreGeometry LetterPresentation ConeSkeleton
universe u

def finalFiniteComplex (m : ℕ) : FiniteComplex :=
  elementaryFiniteComplex (finalSize m) (finalMaster m) (finalSix m)

def finalFiniteBasepoint (m : ℕ) : (finalFiniteComplex m).Carrier :=
  elementaryFiniteBasepoint (finalSize m) (finalMaster m) (finalSix m)

def finalFinitePiOneEquiv (m : ℕ) : SamplingStage.LetterGroup finalDiagramStage m ≃*
    FundamentalGroup (finalFiniteComplex m).Carrier (finalFiniteBasepoint m) :=
  elementaryFinitePiOneEquiv (finalSize m) (finalMaster m) (finalSix m)

end

/-! The very same selected finite complex now satisfies the original main's
literal triangular linear disk inequality, in addition to its pi1 obstruction.
No picture-producer or filling-transfer hypothesis remains. -/

/-! The SAME selected arrays give a literal basepoint-fixing contraction of
 their actual universal cover. In particular the full higher-homotopy clause
 of the unchanged finite-model theorem is discharged, unconditionally. -/

open CoreGeometry LetterPresentation ConeSkeleton FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
universe u
variable (m : ℕ)
local instance instDecidableEqElementaryVertexFinalSizeFinalMaster_1 : DecidableEq (ElementaryVertex (finalSize m) (finalMaster m)) := Classical.decEq _
local instance instDecidableEqElementaryEdgeFinalSizeFinalMaster_1 : DecidableEq (ElementaryEdge (finalSize m) (finalMaster m)) := Classical.decEq _
local instance instDecidableEqElementaryCellFinalSizeFinalMasterFinalSix_1 : DecidableEq (ElementaryCell (finalSize m) (finalMaster m) (finalSix m)) := Classical.decEq _
local instance instTopologicalSpaceGroupFinalSizeFinalMasterFinalSix : TopologicalSpace (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) := ⊥
local instance instDiscreteTopologyGroupFinalSizeFinalMasterFinalSix : DiscreteTopology (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) := ⟨rfl⟩

end IncidenceTemplate

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



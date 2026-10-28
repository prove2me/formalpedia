-- Prove2me | Definitions.Def_OAIQ65Sa012
-- name    : OAIQ65Sa012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T03:20:21.804406+00:00
-- url     : https://prove2.me/theorems/551956d2-ef80-4cc3-886d-f59695fb4252
-- title:
--   Definitions bundle OAIQ65Sa012 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 17 definitions, 7 instances and 16 theorems. The definitions and types are `OAI.SimpleAmenable.InitialCoverSystem.pairCarrierStar`, `OAI.SimpleAmenable.InitialCoverSystem.pairContainer`, `OAI.SimpleAmenable.InitialCoverSystem.pairSplit`, `OAI.SimpleAmenable.InitialCoverSystem.pairStar`, `OAI.SimpleAmenable.PolygonObject.Labelled.drop`, `OAI.SimpleAmenable.PolygonObject.Labelled.fromLadder`, `OAI.SimpleAmenable.PolygonObject.Labelled.refine`, `OAI.SimpleAmenable.PolygonObject.Labelled.refinementLadder`, `OAI.SimpleAmenable.PolygonObject.Labelled.toStrings`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.trajectoryRep`, `OAI.SimpleAmenable.PolygonObject.incrementLadderEquiv`, `OAI.SimpleAmenable.SquareStep.orbitGroupRing`, `OAI.SimpleAmenable.SquareStep.periodizeModule`, `OAI.SimpleAmenable.planeCornerCoordinates`, `OAI.SimpleAmenable.planeCornerEmbedding`, `OAI.SimpleAmenable.planeCornerLinear`, `OAI.SimpleAmenable.primitivePair`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_CentralCovers_FormalCoordinates`, `SimpleAmenable_CentralCovers_GrowthAxisUniform`, `SimpleAmenable_CentralCovers_PairControl`, `SimpleAmenable_Configurations_PolygonStrandReconstruction`, `SimpleAmenable_Configurations_PolygonStringNormalization`, `SimpleAmenable_Configurations_PolygonTrajectoryStrata`, `SimpleAmenable_Configurations_StageRealization`, `SimpleAmenable_Configurations_TrajectoryLabels`, `SimpleAmenable_Configurations_TrajectoryStages`, `SimpleAmenable_Homology_PolygonCoefficientFinite`, `SimpleAmenable_Homology_TorusCoefficientFinite`, `SimpleAmenable_Homology_TrajectoryDifferential`, `SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates`, `SimpleAmenable_PolygonGeometry_PlaneStepFunctions`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa008` and `OAIQ65Sa009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ65Sa019`; the statements `OAI.SimpleAmenable.InitialCoverSystem.pair_formal_quotient` and `OAI_SimpleAmenable_jointBitFieldLaw_transport`; the proofs of `OAI.SimpleAmenable.InitialCoverSystem.pair_formal_quotient`, `OAI_SimpleAmenable_jointBitFieldLaw_transport`, `OAI.SimpleAmenable.primitive_laws_eventually` and `OAI.SimpleAmenable.rectangularAtlas_fixed_radius_eventually`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa008
import Definitions.Def_OAIQ65Sa009

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GrowthAxisUniform
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section PairSectors
noncomputable def primitivePair {ι : Type*}
    (P : ι → Fin 5 × (CutRing × CutRing)) (i j : ι) : Bool → Fin 5 × (CutRing × CutRing) :=
  fun b => if b then P j else P i

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

noncomputable def pairStar : Option ι → TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)
  | none => B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))
  | some i => B.fullGeometricSector hlarge (primitivePair P i i) (h i i)
      (primitiveTests (a := a) (r := r) P i)

noncomputable def pairSplit (i : ι) (j : Option ι) (positive : Bool) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (primitivePair P i (j.getD i)) (h i (j.getD i))
    (primitiveFamilyTests (a := a) (r := r) P j ⊓
      (if positive then primitiveTests (a := a) (r := r) P i
        else (primitiveTests (a := a) (r := r) P i)ᶜ))

omit [Finite ι] in
theorem pairSplit_whole_left (i : ι) :
    B.pairSplit hlarge P h i none true = B.pairStar hlarge P h (some i) := by
  unfold pairSplit pairStar
  congr 1
  ext x
  change (x ∈ Set.univ ∧ x ∈ (primitiveTests (a := a) (r := r) P i).val) ↔ _
  simp

omit [Finite ι] in
theorem pairSplit_mem (i : ι) (j : Option ι) (positive : Bool) (s : TrackStar (Fin (m+1))) :
    B.pairSplit hlarge P h i j positive s ∈
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  have hi := B.smallPrimitive_range_reindex hlarge P (fun b : Bool => if b then j.getD i else i)
  have he : P ∘ (fun b : Bool => if b then j.getD i else i) = primitivePair P i (j.getD i) := by
    funext b; cases b <;> rfl
  rw [he] at hi
  apply hi
  exact B.fullGeometricSector_mem hlarge _ _ _ s

omit [Finite ι] in
theorem pairStar_mem (j : Option ι) (s : TrackStar (Fin (m+1))) :
    B.pairStar hlarge P h j s ∈ (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  cases j with
  | none => exact B.constant_range_full hlarge P ⟨_,rfl⟩
  | some i =>
    rw [← B.pairSplit_whole_left hlarge P h i]
    exact B.pairSplit_mem hlarge P h i none true s

end InitialCoverSystem
end PairSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PairControl
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PairControl
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

noncomputable def pairContainer (i : ι) (positive : Bool) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (primitivePair P i i) (h i i)
    (if positive then primitiveTests (a := a) (r := r) P i
      else (primitiveTests (a := a) (r := r) P i)ᶜ)

end InitialCoverSystem
end PairControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section PairFormalLaw
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Fintype ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

noncomputable def pairCarrierStar (j : Option ι) : TrackStar (Fin (m+1)) →*
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range :=
  (B.pairStar hlarge P h j).codRestrict _ (B.pairStar_mem hlarge P h j)

end InitialCoverSystem
end PairFormalLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonTrajectoryStrata
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonTrajectoryStrata

open Classical _root_.CategoryTheory Set
namespace PolygonObject
variable {a n : ℕ}

theorem pointShift_comp {U V W : PolygonObject a} (f : U ⟶ V) (g : V ⟶ W) (x : U.Point) :
    pointShift (f≫g) x=pointShift g (f.toEquiv x)+pointShift f x := by
  have he := pointShift_unique (f≫g) x (pointShift g (f.toEquiv x)+pointShift f x) (by
    rw [arrow_comp_apply,pointShift_spec g,pointShift_spec f,translate_add])
  simpa only [representative_add,pointShift_reduced] using he

theorem pointShift_fiber_polygon {U V : PolygonObject a} (f : U ⟶ V)
    (i : Fin U.tracks) (u : CutRing × CutRing) :
    {z | ∃hz : z∈(U.cell i).val, pointShift f ⟨(i,z),hz⟩=u}∈polygonAlgebra a := by
  obtain ⟨s,hs,hcover⟩ := f.hasTable
  have he : {z | ∃hz : z∈(U.cell i).val, pointShift f ⟨(i,z),hz⟩=u} =
      ⋃c∈s.filter (fun c => c.source=i ∧ orbitRepresentative c.shift=u),c.domain.val := by
    ext z
    constructor
    · rintro ⟨hz,hu⟩
      obtain ⟨c,hc,hz'⟩ := hcover ⟨(i,z),hz⟩
      exact Set.mem_iUnion₂.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,hz'.1.symm,
        (chart_pointShift f c (hs c hc) ⟨(i,z),hz⟩ hz').symm.trans hu⟩,hz'.2⟩
    · intro hz
      obtain ⟨c,hcf,hcz⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨hcs,hci,hcu⟩ := Finset.mem_filter.mp hcf
      obtain ⟨hz',hf⟩ := hs c hcs z hcz
      subst i
      refine ⟨hz',?_⟩
      exact (chart_pointShift f c (hs c hcs) ⟨(c.source,z),hz'⟩ ⟨rfl,hcz⟩).trans hcu
  rw [he]
  apply BooleanSubalgebra.biSup_mem (Finset.finite_toSet _)
  intro c _
  exact c.domain.property

theorem trajectoryShift_fiber_polygon (F : RawString a n) (j : Fin (F.obj 0).tracks)
    (u : Fin (n+1) → CutRing × CutRing) :
    {z | ∃hz : z∈((F.obj 0).cell j).val, trajectoryShift F ⟨(j,z),hz⟩=u}∈polygonAlgebra a := by
  have he : {z | ∃hz : z∈((F.obj 0).cell j).val, trajectoryShift F ⟨(j,z),hz⟩=u} =
      ⋂i : Fin (n+1),{z | ∃hz : z∈((F.obj 0).cell j).val,
        pointShift (baseArrow F i) ⟨(j,z),hz⟩=u i} := by
    ext z
    constructor
    · rintro ⟨hz,hu⟩
      exact Set.mem_iInter.mpr (fun i => ⟨hz,congrFun hu i⟩)
    · intro hz
      have h := Set.mem_iInter.mp hz
      obtain ⟨hz',_⟩ := h 0
      refine ⟨hz',?_⟩
      funext i
      exact (h i).choose_spec
  rw [he]
  exact BooleanSubalgebra.iInf_mem (fun i => pointShift_fiber_polygon (baseArrow F i) j (u i))

theorem ladder_preserves_trajectoryShift {F G : StringGroupoid a n} (h : F ⟶ G)
    (x : (F.obj.obj 0).Point) :
    trajectoryShift G.obj ((h.hom.app 0).toEquiv x)=trajectoryShift F.obj x := by
  funext i
  have he : translate a (pointShift (baseArrow G.obj i) ((h.hom.app 0).toEquiv x)) x.val.2 =
      translate a (pointShift (baseArrow F.obj i) x) x.val.2 := by
    calc
      _ = translate a (pointShift (baseArrow G.obj i) ((h.hom.app 0).toEquiv x))
          ((h.hom.app 0).toEquiv x).val.2 := congrArg _ (h.property 0 x).symm
      _ = trajectory G.obj ((h.hom.app 0).toEquiv x) i := (pointShift_spec _ _).symm
      _ = trajectory F.obj x i := congrFun (ladder_preserves_trajectory h x) i
      _ = _ := pointShift_spec _ _
  exact (pointShift_reduced _ _).symm.trans
    ((orbitRepresentative_eq_of_translate_eq x.val.2 he).trans (pointShift_reduced _ _))

end PolygonObject
end PolygonTrajectoryStrata

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonStringNormalization
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

open Classical _root_.CategoryTheory Set
namespace PolygonObject
variable {a n m : ℕ}

theorem trajectoryShift_reindex (F : RawString a m)
    (u : Fin (n+1) ⥤ Fin (m+1)) (x : (F.obj 0).Point) (i : Fin (n+1)) :
    trajectoryShift (u⋙F) ((baseArrow F (u.obj 0)).toEquiv x) i =
      trajectoryShift F x (u.obj i)-trajectoryShift F x (u.obj 0) := by
  have he := pointShift_comp (baseArrow F (u.obj 0))
    (F.map (u.map (homOfLE (Fin.zero_le i)))) x
  rw [baseArrow_comp] at he
  exact eq_sub_iff_add_eq.mpr he.symm

theorem increments_reindex (F : RawString a m)
    (u : Fin (n+1) ⥤ Fin (m+1)) (x : (F.obj 0).Point) (i : Fin n) :
    increments (u⋙F) ((baseArrow F (u.obj 0)).toEquiv x) i =
      trajectoryShift F x (u.obj i.succ)-trajectoryShift F x (u.obj i.castSucc) := by
  unfold increments
  rw [trajectoryShift_reindex,trajectoryShift_reindex]
  abel

theorem increments_fiber_polygon (F : RawString a n) (j : Fin (F.obj 0).tracks)
    (u : Fin n → CutRing × CutRing) :
    {z | ∃hz : z∈((F.obj 0).cell j).val,increments F ⟨(j,z),hz⟩=u}∈polygonAlgebra a := by
  let s := (trajectoryShift_finite_range F).toFinset
  have he : {z | ∃hz : z∈((F.obj 0).cell j).val,increments F ⟨(j,z),hz⟩=u} =
      ⋃t∈s.filter (fun t => (fun i : Fin n => t i.succ-t i.castSucc)=u),
        {z | ∃hz : z∈((F.obj 0).cell j).val,trajectoryShift F ⟨(j,z),hz⟩=t} := by
    ext z
    constructor
    · rintro ⟨hz,hu⟩
      refine Set.mem_iUnion₂.mpr ⟨trajectoryShift F ⟨(j,z),hz⟩,
        Finset.mem_filter.mpr ⟨?_,hu⟩,hz,rfl⟩
      exact (Set.Finite.mem_toFinset _).mpr ⟨_,rfl⟩
    · intro hz
      obtain ⟨t,ht,hzt⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨hz',heq⟩ := hzt
      refine ⟨hz',?_⟩
      change (fun i : Fin n => trajectoryShift F ⟨(j,z),hz'⟩ i.succ-
        trajectoryShift F ⟨(j,z),hz'⟩ i.castSucc)=u
      rw [heq]
      exact (Finset.mem_filter.mp ht).2
  rw [he]
  apply BooleanSubalgebra.biSup_mem (Finset.finite_toSet _)
  intro t _
  exact trajectoryShift_fiber_polygon F j t

theorem ladder_preserves_increments {F G : StringGroupoid a n} (h : F ⟶ G)
    (x : (F.obj.obj 0).Point) :
    increments G.obj ((h.hom.app 0).toEquiv x)=increments F.obj x := by
  unfold increments
  rw [ladder_preserves_trajectoryShift]

end PolygonObject

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonStrandReconstruction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section PolygonIncrementFibers

open Classical _root_.CategoryTheory
namespace PolygonObject
variable {a n : ℕ}

noncomputable def incrementLadderEquiv (F G : StringGroupoid a n) :
    (F ⟶ G) ≃ {h : F.obj.obj 0 ⟶ G.obj.obj 0 //
      Positional h ∧ ∀x,increments G.obj (h.toEquiv x)=increments F.obj x} where
  toFun h := ⟨h.hom.app 0,h.property 0,ladder_preserves_increments h⟩
  invFun h := ⟨extendLadder h.val,
    extendLadder_positional_of_increments h.val h.property.1 h.property.2⟩
  left_inv h := by apply WideSubcategory.hom_ext; exact extendLadder_app_zero h.hom
  right_inv h := by apply Subtype.ext; exact extendLadder_zero h.val

end PolygonObject
end PolygonIncrementFibers

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrajectoryLabels
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace Labelled
variable {a n : ℕ}

noncomputable def toStrings : Labelled a n ⥤ StringGroupoid a n where
  obj := string
  map := ladder
  map_id U := by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change (ladder (𝟙 U)).hom.app 0 = 𝟙 _
    rw [ladder_zero]
    change inv (initial U) ≫ (𝟙 _) ≫ initial U = 𝟙 _
    simp
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change (ladder (f ≫ g)).hom.app 0 = (ladder f).hom.app 0 ≫ (ladder g).hom.app 0
    rw [ladder_zero,ladder_zero,ladder_zero]
    change inv _ ≫ (f.arrow ≫ g.arrow) ≫ _ = initialArrow f ≫ initialArrow g
    simp [initialArrow,Category.assoc]

noncomputable def fromLadder {U V : Labelled a n} (f : string U ⟶ string V) : U ⟶ V where
  arrow := initial U ≫ f.hom.app 0 ≫ inv (initial V)
  positional := positional_comp (incrementInitial_positional _ _)
    (positional_comp (f.property 0) (positional_inv (incrementInitial_positional _ _)))
  labelled x := by
    have h := ladder_preserves_increments f ((initial U).toEquiv x)
    rw [incrementString_spec_reduced _ _ U.reduced] at h
    have hv := incrementString_spec_reduced V.polygon V.label V.reduced
      ((initial V).toEquiv.symm ((f.hom.app 0).toEquiv ((initial U).toEquiv x)))
    simp only [Equiv.apply_symm_apply] at hv
    simpa only [arrow_comp_apply,inv_arrow_apply] using hv.symm.trans h

noncomputable instance instFullStringGroupoidToStrings : toStrings (a:=a) (n:=n) |>.Full where
  map_surjective f := ⟨fromLadder f,by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change (ladder (fromLadder f)).hom.app 0 = f.hom.app 0
    rw [ladder_zero]
    simp [initialArrow,fromLadder,Category.assoc]⟩

instance instFaithfulStringGroupoidToStrings : toStrings (a:=a) (n:=n) |>.Faithful where
  map_injective {U V} f g h := by
    have h0 := congrArg (fun h : string U ⟶ string V => h.hom.app 0) h
    change (ladder f).hom.app 0 = (ladder g).hom.app 0 at h0
    rw [ladder_zero,ladder_zero] at h0
    apply Hom.ext
    simpa [initialArrow,Category.assoc] using congrArg (fun h => initial U ≫ h ≫ inv (initial V)) h0

theorem supportLabel_polygon (F : RawString a n) (j : Fin (F.obj 0).tracks) (k : Support F) :
    {z | ∃hz : z∈((F.obj 0).cell j).val,supportLabel F ⟨(j,z),hz⟩=k}∈polygonAlgebra a := by
  simpa only [Subtype.ext_iff,supportLabel] using increments_fiber_polygon F j k.val

noncomputable def refine (F : RawString a n) : Labelled a n where
  polygon := refinement (F.obj 0) (supportLabel F) (supportLabel_polygon F)
  label j := ((Fintype.equivFin (Fin (F.obj 0).tracks × Support F)).symm j).2.val
  reduced j i := by
    obtain ⟨x,hx⟩ := ((Fintype.equivFin (Fin (F.obj 0).tracks × Support F)).symm j).2.property
    rw [←hx]
    exact increments_reduced F x i

noncomputable def drop (F : RawString a n) : (refine F).polygon ⟶ F.obj 0 :=
  refinementArrow (F.obj 0) (supportLabel F) (supportLabel_polygon F)

theorem drop_label (F : RawString a n) (x : (refine F).polygon.Point) :
    increments F ((drop F).toEquiv x) = (refine F).label x.val.1 :=
  congrArg Subtype.val (refinementArrow_label (F.obj 0) (supportLabel F) (supportLabel_polygon F) x)

noncomputable def refinementLadder (F : RawString a n) : string (refine F) ⟶ (⟨F⟩ : StringGroupoid a n) := by
  let h := inv (initial (refine F)) ≫ drop F
  refine (incrementLadderEquiv _ _).symm ⟨h,?_,?_⟩
  · exact positional_comp (positional_inv (incrementInitial_positional _ _))
      (refinementArrow_positional _ _ _)
  · intro x
    obtain ⟨y,rfl⟩ := (initial (refine F)).toEquiv.surjective x
    simp only [h,arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
    rw [incrementString_spec_reduced _ _ (refine F).reduced]
    exact drop_label F y
noncomputable instance instEssSurjStringGroupoidToStrings : toStrings (a:=a) (n:=n) |>.EssSurj where
  mem_essImage F := by
    let e := asIso (refinementLadder F.obj)
    exact ⟨refine F.obj,⟨e⟩⟩

noncomputable instance instIsEquivalenceStringGroupoidToStrings : toStrings (a:=a) (n:=n) |>.IsEquivalence where

end Labelled
end SimpleAmenable.PolygonObject

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrajectoryStages
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.braided _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instCoeFunHomForallFinSize _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.monoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.symmetric _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace LabelledStage
variable {a n s : ℕ} (P : BooleanPartition a)
    (L : Fin s → Fin n → CutRing × CutRing)
    (hL : ∀ j i, orbitRepresentative (L j i)=L j i)

instance instFaithfulObjLabelledFunctor : (functor P L hL).Faithful where
  map_injective {U V} f g h := by
    funext b
    apply Equiv.ext
    intro k
    let j := index P U ⟨b,k⟩
    let x : (object P L hL U).polygon.Point :=
      ⟨(j,P.point b.1),by simp [object,j,BooleanPartition.cell]⟩
    have hx := congrArg (fun f : object P L hL U ⟶ object P L hL V =>
      (f.arrow.toEquiv x).val.1) h
    change indexMap P L hL f j = indexMap P L hL g j at hx
    have hh := (index P V).injective hx
    change trackMap P f ((index P U).symm j) = trackMap P g ((index P U).symm j) at hh
    simp only [j,Equiv.symm_apply_apply] at hh
    exact Sigma.mk.inj_iff.mp hh |>.2 |> eq_of_heq

end LabelledStage
end SimpleAmenable.PolygonObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageRealization
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.braided _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instCoeFunHomForallFinSize _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.monoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.symmetric _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.inclusionBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.inclusionMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace LabelledStage
variable {a n s : ℕ} (P : BooleanPartition a)
    (L : Fin s → Fin n → CutRing × CutRing)
    (hL : ∀ j i, orbitRepresentative (L j i)=L j i)
    (hLi : Function.Injective L)

open UniformObject

instance realize_faithful : (realize P L hL).Faithful where
  map_injective equality := (functor P L hL).map_injective (congrArg Hom.arrow equality)

end LabelledStage
end SimpleAmenable.PolygonObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneStepFunctions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PlaneStepFunctions

instance instIsNoetherianRingPolygonGroupRing : IsNoetherianRing PolygonGroupRing := by
  let : Algebra.FiniteType ℤ PolygonGroupRing :=
    MonoidAlgebra.finiteType_iff_group_fg.mpr inferInstance
  exact Algebra.FiniteType.isNoetherianRing ℤ PolygonGroupRing

end PlaneStepFunctions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PlaneCornerCoordinates
open Classical

theorem planeCorner_coordinates_finite {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (t : PlaneCornerIndex a) :
    (Function.support (fun u => planeCornerValue f (planeVertexPosition a t.1 u)
      (planeDirectionRep a t.2))).Finite := by
  obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
  apply ((planeArrangementVertices a S).finite_toSet.preimage
    (planeVertexPosition_injective a t.1).injOn).subset
  intro u hu
  exact planeCornerValue_mem_vertices ha f hS (planeDirectionRep_transverse a t.2) hu

noncomputable def planeCornerCoordinates {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (t : PlaneCornerIndex a) : PolygonGroupRing :=
  MonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite
    (fun u => planeCornerValue f (planeVertexPosition a t.1 u) (planeDirectionRep a t.2))
    (planeCorner_coordinates_finite ha f t))

@[simp] theorem planeCornerCoordinates_coeff {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (t : PlaneCornerIndex a) (u : Multiplicative (CutRing × CutRing)) :
    (planeCornerCoordinates ha f t).coeff u=
      planeCornerValue f (planeVertexPosition a t.1 u) (planeDirectionRep a t.2) := rfl

end PlaneCornerCoordinates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonCoefficientFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonCoefficientFinite
open Classical

noncomputable def planeCornerLinear {a : ℕ} (ha : 0<a) :
    PlaneStep a →ₗ[ℤ] (PlaneCornerIndex a → PolygonGroupRing) where
  toFun f t := planeCornerCoordinates ha f t
  map_add' f g := by
    funext t
    apply MonoidAlgebra.ext
    ext u
    simp only [planeCornerCoordinates_coeff,Pi.add_apply,MonoidAlgebra.coeff_add,
      Finsupp.add_apply,planeCornerValue_add]
  map_smul' c f := by
    funext t
    apply MonoidAlgebra.ext
    ext u
    simp only [planeCornerCoordinates_coeff,Pi.smul_apply,MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply,planeCornerValue_smul,RingHom.id_apply]

theorem planeCornerCoordinates_translate {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (v : CutRing × CutRing) (t : PlaneCornerIndex a) :
    planeCornerCoordinates ha (PlaneStep.translate v f) t=
      MonoidAlgebra.single (Multiplicative.ofAdd v) 1 * planeCornerCoordinates ha f t := by
  apply MonoidAlgebra.ext
  ext u
  simp only [planeCornerCoordinates_coeff,MonoidAlgebra.coeff_single_mul_apply,
    one_mul,planeCornerValue_translate]
  congr 2
  ext <;> simp [planeVertexPosition,sub_eq_add_neg] <;> ring

noncomputable def planeCornerEmbedding {a : ℕ} (ha : 0<a) :
    (PlaneStep.representation a).asModule →ₗ[PolygonGroupRing]
      (PlaneCornerIndex a → PolygonGroupRing) :=
  MonoidAlgebra.equivariantOfLinearOfComm
    ((planeCornerLinear ha).comp (PlaneStep.representation a).asModuleEquiv.toLinearMap)
    (by
      intro g f
      funext t
      change planeCornerCoordinates ha
        ((PlaneStep.representation a).asModuleEquiv (MonoidAlgebra.single g 1 • f)) t = _
      rw [Representation.asModuleEquiv_map_smul,Representation.asAlgebraHom_single]
      simp only [one_smul]
      exact planeCornerCoordinates_translate ha _ g.toAdd t)

end PolygonCoefficientFinite

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TorusCoefficientFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TorusCoefficientFinite

open Classical
namespace SquareStep

noncomputable def orbitGroupRing : PolygonGroupRing →+* OrbitGroupRing :=
  MonoidAlgebra.mapDomainRingHom ℤ orbitProjection

noncomputable def periodizeModule {a : ℕ} :
    (PlaneStep.representation a).asModule →ₛₗ[orbitGroupRing]
      (orbitRepresentation a).asModule where
  toFun := periodize
  map_add' := periodize.map_add
  map_smul' r x := by
    change PlaneStep a at x
    change periodize ((PlaneStep.representation a).asAlgebraHom r x) =
      (orbitRepresentation a).asAlgebraHom (orbitGroupRing r) (periodize x)
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simp [hr,hs]
    | single g c =>
      simp only [orbitGroupRing,MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single,Representation.asAlgebraHom_single,
        LinearMap.smul_apply,map_smul]
      congr 1
      change periodize (PlaneStep.translate g.toAdd x) =
        orbitRepresentation a (orbitProjection g) (periodize x)
      rw [← representation_reduce]
      exact periodize_translate x g.toAdd

end SquareStep
end TorusCoefficientFinite

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TrajectoryDifferential
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory AlgebraicTopology
open scoped BigOperators TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage
open Labelled IntervalBar.Diagram FreeChains

attribute [local instance 1200] Rep.hV2 Representation.instModuleAsModule TensorProduct.instModule
variable {a n : ℕ} {K : Type} [AddCommGroup K]
noncomputable def trajectoryRep (a j : ℕ) :=
  @SquareStep.coefficientRep a (Stage.K j) inferInstance (AddCommGroup.toIntModule _)
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
end



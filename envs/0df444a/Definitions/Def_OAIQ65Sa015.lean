-- Prove2me | Definitions.Def_OAIQ65Sa015
-- name    : OAIQ65Sa015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:21:52.357707+00:00
-- url     : https://prove2.me/theorems/741200cc-9f74-4c3d-91ed-b1db3f24e11a
-- title:
--   Definitions bundle OAIQ65Sa015 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 18 definitions, 1 inductive type or structure, 1 instance and 36 theorems. The definitions and types are `OAI.SimpleAmenable.InitialCoverSystem.ExactSlotTransport`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.concurrentCoordinates`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.concurrentPrimitives`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.margin`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitiveStar`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.starFamily`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope`, `OAI.SimpleAmenable.InitialCoverSystem.SlotRouting.privateBank`, `OAI.SimpleAmenable.InitialCoverSystem.UniformSlotTransport`, `OAI.SimpleAmenable.InitialCoverSystem.slotGroup`, `OAI.SimpleAmenable.InitialCoverSystem.slotStar`, `OAI.SimpleAmenable.InitialCoverSystem.slotTransportSubgroup`, `OAI.SimpleAmenable.PolygonGrid.strip`, `OAI.SimpleAmenable.PolygonObject.BankEmbedding`, `OAI.SimpleAmenable.PolygonObject.BankEmbedding.full_restrict`, `OAI.SimpleAmenable.PolygonObject.BankEmbedding.imageBank`, `OAI.SimpleAmenable.PolygonObject.BankEmbedding.inclusion`, `OAI.SimpleAmenable.PolygonObject.whole`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.column`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_CentralCovers_CanonicalSlotStars`, `SimpleAmenable_CentralCovers_CommonFrameTransport`, `SimpleAmenable_CentralCovers_ConcurrentCoordinateGates`, `SimpleAmenable_CentralCovers_CrossingCellActions`, `SimpleAmenable_CentralCovers_DistinctSlotFixer`, `SimpleAmenable_CentralCovers_FiniteSlotRefinement`, `SimpleAmenable_CentralCovers_FormalLaws`, `SimpleAmenable_CentralCovers_PrivateBankFixer`, `SimpleAmenable_CentralCovers_RectangularAtlas`, `SimpleAmenable_CentralCovers_ShiftedRouting`, `SimpleAmenable_Configurations_RepeatedTrackRouting`, `SimpleAmenable_Configurations_SlotInputGeneration`, `SimpleAmenable_Homology_HomologyAdditive`, `SimpleAmenable_PolygonGeometry_OffsetFrames`, `SimpleAmenable_PolygonGeometry_PeriodicSlotStars`, `SimpleAmenable_PolygonGeometry_PolygonBankEmbedding`, `SimpleAmenable_PolygonGeometry_PolygonPiecewiseSlots`, `SimpleAmenable_PolygonGeometry_PolygonSmallPartition`, `SimpleAmenable_PolygonGeometry_PrivateBankWord`, `SimpleAmenable_PolygonGeometry_RoutingIndependence`, `SimpleAmenable_RandomFields_CanonicalPolygonCovariance`, `SimpleAmenable_RandomFields_RecoveredConstantCovariance`, `SimpleAmenable_Simplicial_SmallEvenRouting`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa013` and `OAIQ65Sa014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa017`, `OAIQ65Sa018`, `OAIQ65Sa022` and `OAIQ65Sa023`; the statements `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.constant_model_action`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinateGate_control`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinate_control_inward_gate`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinate_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.crossing_cell_actions`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.exterior_clipped_model_action`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.far_grid_action_at_point`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.formalRectangleMasks`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.interior_clipped_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_global_templates`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_local_templates`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_germ_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.refined_clipped_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.selected_active_slope_actions`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.uniform_clipped_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.inactive_near_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action` and `OAI_SimpleAmenable_PolygonTracks_fullH2_finite_of_bar`; the proofs of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.constant_model_action`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinateGate_control`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinate_control_inward_gate`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinate_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.crossing_cell_actions`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.exterior_clipped_model_action`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.far_grid_action_at_point`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.formalRectangleMasks`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.interior_clipped_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_global_templates`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_local_templates`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_germ_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.refined_clipped_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.selected_active_slope_actions`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.uniform_clipped_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.inactive_near_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action` and `OAI.SimpleAmenable.InitialCoverSystem.coverMap_kernel_central`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa013
import Definitions.Def_OAIQ65Sa014

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_RectangularAtlas
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section RectangularAtlas
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

namespace RectangularAtlas
variable {B} (A : B.RectangularAtlas)

noncomputable def slope (hlarge : 15 < m+1) (d : Fin 2) (z : CutRing × CutRing) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.tangentSign hlarge A.k A.p A.u A.charts d z true

end RectangularAtlas
end InitialCoverSystem

end RectangularAtlas

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CrossingCellActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section CrossingCellActions

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2  ≤  m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.PatchAtlas)

noncomputable def concurrentPrimitives (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) :
    Sum (Fin 4) (Fin 2 × Fin (A.geometry.window-1)) → Fin 5 × (CutRing × CutRing) :=
  translatedTemplate (Sum.elim
    (fun j : Fin 4 => (⟨j.val+1,by omega⟩,A.geometry.anchors t j))
    (coordinateWindowPrimitives A.geometry.window A.geometry.start)) u

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrentLaw (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) :
    ∀ I (_ : I.card ≤ 15) b hb, B.PrimitiveFamilyLaw I b hb (A.concurrentPrimitives t u) :=
  fun I _ b hb => A.concurrent t u I b hb

noncomputable def margin (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) :
    polygonAlgebra a := spatialTranslate u
    (coordinateRectangle a (A.geometry.margins t).lower (A.geometry.margins t).upper)

end InitialCoverSystem.PatchAtlas
end CrossingCellActions

section LocalPatchTemplates
namespace InitialCoverSystem

attribute [instance] LocalPatchTemplate.finite_index

end InitialCoverSystem
end LocalPatchTemplates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalLaws
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section CanonicalPrimitiveStars
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι : Type*}

noncomputable def primitiveStar (hlarge : 15 < m+1) (p : Fin 5 × (CutRing × CutRing)) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) p.2)
    (fun I _ b hb => A.initial p.2 I b hb)
    (spatialTranslate p.2 (initialTest a r p.1))

noncomputable def starFamily (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing)) :
    Option ι → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)
  | none => B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))
  | some i => A.primitiveStar hlarge (P i)

end InitialCoverSystem.PatchAtlas
end CanonicalPrimitiveStars

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConcurrentCoordinateGates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ConcurrentCoordinateGates
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

noncomputable def concurrentCoordinates (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) := A.concurrentPrimitives t u ∘ A.concurrentCoordinateEmbedding

end InitialCoverSystem.PatchAtlas
end ConcurrentCoordinateGates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_CanonicalPolygonCovariance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section CanonicalPolygonCovariance
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem polygonStar_frame_zero_commute
    (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (F : CommonFrame a r m hm I 0)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I)) :
    Commute (B.t F.k) (B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s)) := by
  have he := DFunLike.congr_fun (B.polygonStar_common_translate hlarge h hr I hI b hb 0 F V) s
  have hz : spatialTranslate (0 : CutRing × CutRing) V = V := by
    apply Subtype.ext
    ext p
    simp [spatialTranslate,translate_zero]
  rw [hz] at he
  change B.t F.k * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) *
    (B.t F.k)⁻¹ = B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) at he
  have hh := congrArg (fun x => x * B.t F.k) he
  exact show _*_ = _*_ from by simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

end InitialCoverSystem
end CanonicalPolygonCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_OffsetFrames
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem frameStar_independent (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card)
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (u v : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm I u) (G : OffsetFrame a r m hm I v)
    (huv : ∀ i ∈ I, u i = v i) (V : polygonAlgebra a) :
    B.frameStar hlarge h hr I u F V = B.frameStar hlarge h hr I v G V := by
  ext s : 1
  let x := B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s)
  have hc := B.polygonStar_frame_zero_commute hlarge h hr I hI b hb (F.difference G huv) V s
  change Commute (B.t (F.k⁻¹ * G.k)) x at hc
  have he : B.t (F.k⁻¹ * G.k) * x * (B.t (F.k⁻¹ * G.k))⁻¹ = x := by
    rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one]
  change B.t F.k * x * (B.t F.k)⁻¹ = B.t G.k * x * (B.t G.k)⁻¹
  calc
    B.t F.k * x * (B.t F.k)⁻¹ =
        B.t F.k * (B.t (F.k⁻¹ * G.k) * x * (B.t (F.k⁻¹ * G.k))⁻¹) * (B.t F.k)⁻¹ := by rw [he]
    _ = B.t G.k * x * (B.t G.k)⁻¹ := by simp [map_mul,map_inv,mul_assoc]

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CommonFrameTransport
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem distinctSlotStar_uniform_fixer (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1))
    (hb : b ∉ orderedTrackAlphabet ι) (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (v : CutRing × CutRing) (hu : ∀ j, u (ι j)=v) (V : polygonAlgebra a)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hfix : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι j,translate a (u (ι j)) x.val) =
        (ι j,translate a (u (ι j)) x.val))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute z (B.distinctSlotStar hlarge h hr ι u F V s) := by
  apply CentralOn.commute_perfect _ _ (B.polygonStars_central hlarge h hr)
    (B.distinctSlotStar hlarge h hr ι u F V) _ z hz _ s
  · rintro y ⟨s,rfl⟩
    exact B.distinctSlotStar_uniform_mem hlarge h hr ι b hb u F v hu V s
  · intro t
    have hg := B.frameStar_supported hlarge h hr (orderedTrackAlphabet ι) u F V
      (universalMap (orderedTrackHom ι) t)
    have hf : ∀ p ∈ frameDomain (orderedTrackAlphabet ι) u V,
        (coverMap M (alternatingGenerator a r m hm) z).val.val p=p := by
      rintro p ⟨i,hi,x,hx,rfl⟩
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
      exact hfix j ⟨x,hx⟩
    exact show _*_ = _*_ from Subtype.ext (Subtype.ext (supported_fixer_commute hf hg).eq)

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PrivateBankWord
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section PrivateBankWord

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem private_bank_evacuation (e : (Fin 5 × Fin 5) ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ bankAlphabet e)
    (u : Fin (m+1) → CutRing × CutRing) (v : Fin 5 → CutRing × CutRing)
    (hu : ∀ i j, u (e (i,j))=v i) (F : OffsetFrame a r m hm (bankAlphabet e) u)
    (V : polygonAlgebra a) (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hfix : ∀ (i j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (e (i,j),translate a (u (e (i,j))) x.val) =
        (e (i,j),translate a (u (e (i,j))) x.val)) :
    ∃ w : BoundedRelationCover M (alternatingGenerator a r m hm),
      w ∈ B.geometricFrameGroup hlarge h hr F.k ∧ Commute z w ∧
      ∀ (j : Fin 5) (x : V.val),
        (coverMap M (alternatingGenerator a r m hm) w).val.val (e (j,0),translate a (u (e (j,0))) x.val) =
          (e (j,1),translate a (u (e (j,1))) x.val) := by
  classical
  let g : Fin 5 → BoundedRelationCover M (alternatingGenerator a r m hm) := fun j =>
    B.distinctSlotStar hlarge h hr (bankRow e j) u (F.restrict (bankRow_subset e j)) V privateCycleStar
  let l := List.finRange 5
  let w := (l.map g).prod
  refine ⟨w,?_,?_,?_⟩
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact B.distinctSlotStar_mem_geometricFrameGroup hlarge h hr (bankRow e j) u
      (F.restrict (bankRow_subset e j)) V privateCycleStar
  · apply Commute.list_prod_right
    intro t ht
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact B.distinctSlotStar_uniform_fixer hlarge h hr (bankRow e j) b
      (fun hi => hb (bankRow_subset e j hi)) u (F.restrict (bankRow_subset e j)) (v j)
      (hu j) V z hz (hfix j) privateCycleStar
  · intro j x
    let q : BoundedRelationCover M (alternatingGenerator a r m hm) →* Equiv.Perm (TrackPoint a (m+1)) :=
      (polygonFullGroup a (m+1)).subtype.comp
        ((polygonAlternatingGroup a (m+1)).subtype.comp (coverMap M (alternatingGenerator a r m hm)))
    change q w (e (j,0),translate a (u (e (j,0))) x.val) = _
    change q ((l.map g).prod) _ = _
    rw [map_list_prod,List.map_map]
    apply perm_list_prod_transport l (List.nodup_finRange 5) (fun i => q (g i)) j (by simp [l])
    · have he := B.distinctSlotStar_apply hlarge h hr (bankRow e j) u
        (F.restrict (bankRow_subset e j)) V privateCycleStar 0 x
      rw [privateCycleStar_projection,privateCycle_apply_zero] at he
      exact he
    · intro i hi hij
      constructor
      · exact B.frameStar_supported hlarge h hr _ u (F.restrict (bankRow_subset e i)) V
          (universalMap (orderedTrackHom (bankRow e i)) privateCycleStar) _
          (bank_other_frame_notmem e u V i j 0 hij _)
      · exact B.frameStar_supported hlarge h hr _ u (F.restrict (bankRow_subset e i)) V
          (universalMap (orderedTrackHom (bankRow e i)) privateCycleStar) _
          (bank_other_frame_notmem e u V i j 1 hij _)

end InitialCoverSystem
end PrivateBankWord

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_RepeatedTrackRouting
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem privateRoutingWord_properties (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (P : PrivateRoutingBank i) (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (V : polygonAlgebra a)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    B.privateRoutingWord hlarge h hr i u P b hb V ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range ∧
      B.privateRoutingWord hlarge h hr i u P b hb V ∈ sourceAlignedGroup a r m hm M B.t P.alphabet ∧
      ∀ (j : Fin 5) (x : V.val),
        (coverMap M (alternatingGenerator a r m hm) (B.privateRoutingWord hlarge h hr i u P b hb V)).val.val (i j,translate a (u j) x.val) =
          (P.target j,translate a (u j) x.val) := by
  classical
  have hbrow (j : Fin 5) : b ∉ orderedTrackAlphabet (P.row j) :=
    fun ht => hb (P.row_subset j ht)
  let F (j : Fin 5) := balancedOffsetFrame a r m hm (orderedTrackAlphabet (P.row j))
    b (hbrow j) (fun _ => u j)
  let g : Fin 5 → BoundedRelationCover M (alternatingGenerator a r m hm) := fun j =>
    B.distinctSlotStar hlarge h hr (P.row j) (fun _ => u j) (F j) V privateCycleStar
  let l := List.finRange 5
  let w := (l.map g).prod
  change w ∈ _ ∧ w ∈ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact B.distinctSlotStar_uniform_mem hlarge h hr (P.row j) b (hbrow j)
      (fun _ => u j) (F j) (u j) (fun _ => rfl) V privateCycleStar
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact sourceAlignedGroup_mono B.t (P.row_subset j)
      (B.frameStar_alphabet_mem hlarge h hr (orderedTrackAlphabet (P.row j))
        (by simp [orderedTrackAlphabet]) b (hbrow j) (fun _ => u j) (F j) V
        (universalMap (orderedTrackHom (P.row j)) privateCycleStar))
  · intro j x
    let q : BoundedRelationCover M (alternatingGenerator a r m hm) →* Equiv.Perm (TrackPoint a (m+1)) :=
      (polygonFullGroup a (m+1)).subtype.comp
        ((polygonAlternatingGroup a (m+1)).subtype.comp (coverMap M (alternatingGenerator a r m hm)))
    change q w (i j,translate a (u j) x.val) = _
    change q ((l.map g).prod) _ = _
    rw [map_list_prod,List.map_map]
    apply perm_list_prod_transport l (List.nodup_finRange 5) (fun k => q (g k)) j (by simp [l])
    · have he := B.distinctSlotStar_apply hlarge h hr (P.row j) (fun _ => u j)
        (F j) V privateCycleStar 0 x
      rw [privateCycleStar_projection,privateCycle_apply_zero,P.source j] at he
      exact he
    · intro k hk hkj
      constructor
      · exact B.frameStar_supported hlarge h hr _ (fun _ => u k) (F k) V
          (universalMap (orderedTrackHom (P.row k)) privateCycleStar) _
          (P.source_other_frame_notmem V u hinj k j hkj x)
      · apply B.frameStar_supported hlarge h hr _ (fun _ => u k) (F k) V
          (universalMap (orderedTrackHom (P.row k)) privateCycleStar)
        rintro ⟨t,ht,y,hy,he⟩
        have hte : P.target j=t := congrArg Prod.fst he
        exact P.target_other_notmem k j hkj (hte.symm ▸ ht)

theorem repeated_bank_routing (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (P : PrivateRoutingBank i) (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (V : polygonAlgebra a)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    ∃ w : BoundedRelationCover M (alternatingGenerator a r m hm),
      w ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range ∧
      w ∈ sourceAlignedGroup a r m hm M B.t P.alphabet ∧
      ∀ (j : Fin 5) (x : V.val),
        (coverMap M (alternatingGenerator a r m hm) w).val.val (i j,translate a (u j) x.val) =
          (P.target j,translate a (u j) x.val) :=
  ⟨B.privateRoutingWord hlarge h hr i u P b hb V,
    B.privateRoutingWord_properties hlarge h hr i u P b hb V hinj⟩

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrivateBankFixer
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem

section
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem private_bank_fixer (e : (Fin 5 × Fin 5) ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ bankAlphabet e)
    (u : Fin (m+1) → CutRing × CutRing) (v : Fin 5 → CutRing × CutRing)
    (hu : ∀ i j, u (e (i,j))=v i) (F : OffsetFrame a r m hm (bankAlphabet e) u)
    (V : polygonAlgebra a) (J : Finset (Fin (m+1)))
    (hJ : Disjoint J (orderedTrackAlphabet (bankColumn e 1)))
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (hfix : ∀ (i j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (e (i,j),translate a (u (e (i,j))) x.val) =
        (e (i,j),translate a (u (e (i,j))) x.val))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute z (B.distinctSlotStar hlarge h hr (bankColumn e 0) u
      (F.restrict (bankColumn_subset e 0)) V s) := by
  obtain ⟨w,hw,hzw,ht⟩ := B.private_bank_evacuation hlarge h hr e b hb u v hu F V z hz hfix
  have he := DFunLike.congr_fun (B.distinctSlotStar_common_frame_transport hlarge h hr
    (bankColumn e 0) (bankColumn e 1) u u
    (F.restrict (bankColumn_subset e 0)) (F.restrict (bankColumn_subset e 1)) rfl V w hw ht) s
  change w*B.distinctSlotStar hlarge h hr (bankColumn e 0) u
      (F.restrict (bankColumn_subset e 0)) V s*w⁻¹ =
    B.distinctSlotStar hlarge h hr (bankColumn e 1) u
      (F.restrict (bankColumn_subset e 1)) V s at he
  have hc : Commute z (B.distinctSlotStar hlarge h hr (bankColumn e 1) u
      (F.restrict (bankColumn_subset e 1)) V s) := by
    apply B.disjoint_aligned J (orderedTrackAlphabet (bankColumn e 1)) hJ z hzJ
    exact B.frameStar_alphabet_mem hlarge h hr _
      (by rw [orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin])
      b (fun hi => hb (bankColumn_subset e 1 hi)) u
      (F.restrict (bankColumn_subset e 1)) V (universalMap (orderedTrackHom (bankColumn e 1)) s)
  have hh := (hzw.inv_right.mul_right hc).mul_right hzw
  rw [← he] at hh
  have he' : w⁻¹*(w*B.distinctSlotStar hlarge h hr (bankColumn e 0) u
      (F.restrict (bankColumn_subset e 0)) V s*w⁻¹)*w =
    B.distinctSlotStar hlarge h hr (bankColumn e 0) u (F.restrict (bankColumn_subset e 0)) V s := by group
  rwa [he'] at hh

end

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem private_bank_source_fixer (e : (Fin 5 × Fin 5) ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ bankAlphabet e)
    (u : Fin (m+1) → CutRing × CutRing) (v : Fin 5 → CutRing × CutRing)
    (hu : ∀ i j, u (e (i,j))=v i) (F : OffsetFrame a r m hm (bankAlphabet e) u)
    (V : polygonAlgebra a) (J : Finset (Fin (m+1)))
    (hprivate : ∀ i j : Fin 5, j≠0 → e (i,j) ∉ J)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (hfix : ∀ (i : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (e (i,0),translate a (u (e (i,0))) x.val) =
        (e (i,0),translate a (u (e (i,0))) x.val))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute z (B.distinctSlotStar hlarge h hr (bankColumn e 0) u
      (F.restrict (bankColumn_subset e 0)) V s) := by
  apply B.private_bank_fixer hlarge h hr e b hb u v hu F V J _ z hz hzJ _ s
  · apply Finset.disjoint_left.mpr
    intro k hk hk'
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hk'
    exact hprivate j 1 (by decide) hk
  · intro i j x
    by_cases hj : j=0
    · subst j; exact hfix i x
    · exact B.sourceAlignedGroup_supported J z hzJ _ (hprivate i j hj)

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_DistinctSlotFixer
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section DistinctSlotFixer
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem distinct_slot_fixer (ι : Fin 5 ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ orderedTrackAlphabet ι)
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (V : polygonAlgebra a) (J : Finset (Fin (m+1)))
    (hreserve : 20 ≤ ((Finset.univ : Finset (Fin (m+1))) \ (insert b J ∪ orderedTrackAlphabet ι)).card)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (hfix : ∀ (i : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι i,translate a (u (ι i)) x.val) =
        (ι i,translate a (u (ι i)) x.val))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute z (B.distinctSlotStar hlarge h hr ι u F V s) := by
  classical
  obtain ⟨e,he,hprivate⟩ := exists_private_bank ι (insert b J) hreserve
  have heq : bankColumn e 0=ι := Function.Embedding.ext he
  have hb' : b ∉ bankAlphabet e := by
    intro hii
    obtain ⟨⟨i,j⟩,_,hij⟩ := Finset.mem_map.mp hii
    by_cases hj : j=0
    · subst j
      rw [he i] at hij
      exact hb (hij ▸ orderedTrackAlphabet_mem ι i)
    · exact hprivate i j hj (hij.symm ▸ Finset.mem_insert_self b J)
  let v : Fin 5 → CutRing × CutRing := fun i => u (ι i)
  let u' : Fin (m+1) → CutRing × CutRing := Function.extend e (fun p => v p.1) (fun _ => 0)
  have hu : ∀ i j, u' (e (i,j))=v i := fun i j => e.injective.extend_apply _ _ (i,j)
  let G := balancedOffsetFrame a r m hm (bankAlphabet e) b hb' u'
  have hfix' : ∀ (i : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (e (i,0),translate a (u' (e (i,0))) x.val) =
        (e (i,0),translate a (u' (e (i,0))) x.val) := by
    intro i x
    rw [hu i 0,he i]
    exact hfix i x
  have hh := B.private_bank_source_fixer hlarge h hr e b hb' u' v hu G V J
    (fun i j hj hjJ => hprivate i j hj (Finset.mem_insert_of_mem hjJ)) z hz hzJ hfix' s
  let G0 : OffsetFrame a r m hm (orderedTrackAlphabet ι) u' := heq ▸ G.restrict (bankColumn_subset e 0)
  have huv : ∀ k ∈ orderedTrackAlphabet ι, u k=u' k := by
    intro k hk
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hk
    rw [← he i,hu i 0]
    exact congrArg u (he i)
  have hehom : B.distinctSlotStar hlarge h hr ι u F V =
      B.distinctSlotStar hlarge h hr ι u' G0 V := by
    unfold distinctSlotStar
    rw [B.frameStar_independent hlarge h hr (orderedTrackAlphabet ι)
      (by rw [orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin])
      b hb u u' F G0 huv V]
  rw [hehom]
  subst ι
  exact hh

end InitialCoverSystem
end DistinctSlotFixer

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_RecoveredConstantCovariance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem distinctSlotStar_constant_transport
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (ι κ : Fin 5 ↪ Fin (m+1)) (c : alternatingGroup (Fin (m+1)))
    (hc : ∀ j, c.val (ι j) = κ j)
    (b : Fin (m+1)) (hb : b ∉ orderedTrackAlphabet κ)
    (u v : Fin (m+1) → CutRing × CutRing)
    (huv : ∀ j, u (ι j) = v (κ j))
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (G : OffsetFrame a r m hm (orderedTrackAlphabet κ) v) (V : polygonAlgebra a) :
    (MulAut.conj (B.c c)).toMonoidHom.comp (B.distinctSlotStar hlarge h hr ι u F V) =
      B.distinctSlotStar hlarge h hr κ v G V := by
  let H := B.constantReindexedFrame R hR ι κ c hc u F
  have hG : B.distinctSlotStar hlarge h hr κ (fun i => u (c.val.symm i)) H V =
      B.distinctSlotStar hlarge h hr κ v G V := by
    unfold distinctSlotStar
    rw [B.frameStar_independent hlarge h hr (orderedTrackAlphabet κ)
      (by rw [orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin])
      b hb (fun i => u (c.val.symm i)) v H G (by
        intro i hi
        obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
        rw [← hc j,c.val.symm_apply_apply]
        simpa only [hc j] using huv j) V]
  rw [← hG,B.distinctSlotStar_offset_formula hlarge h hr ι u F V,
    B.distinctSlotStar_offset_formula hlarge h hr κ (fun i => u (c.val.symm i)) H V]
  ext s : 1
  have hz := DFunLike.congr_fun (B.distinctSlotStar_zero_constant hlarge h hr ι κ c hc V) s
  change B.c c * B.distinctSlotStar hlarge h hr ι (fun _ => 0) (OffsetFrame.zero _) V s * (B.c c)⁻¹ =
    B.distinctSlotStar hlarge h hr κ (fun _ => 0) (OffsetFrame.zero _) V s at hz
  change B.c c * (B.t F.k * _ * (B.t F.k)⁻¹) * (B.c c)⁻¹ = B.t (R c F.k) * _ * (B.t (R c F.k))⁻¹
  rw [← hR c F.k,← hz]
  group

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_SmallEvenRouting
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SmallEvenRouting

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem distinctSlotStar_aligned_transport_with_reindex
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (ι κ : Fin 5 ↪ Fin (m+1)) (c : alternatingGroup (Fin (m+1)))
    (hc : ∀ j, c.val (ι j)=κ j) (C : Finset (Fin (m+1))) (hcC : c.val.support ⊆ C)
    (b : Fin (m+1)) (hb : b ∉ orderedTrackAlphabet ι) (hb' : b ∉ orderedTrackAlphabet κ)
    (u v : Fin (m+1) → CutRing × CutRing) (huv : ∀ j, u (ι j)=v (κ j))
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (G : OffsetFrame a r m hm (orderedTrackAlphabet κ) v) (V : polygonAlgebra a)
    (J : Finset (Fin (m+1)))
    (hreserve : 20 ≤ ((Finset.univ : Finset (Fin (m+1))) \ (insert b (J ∪ C) ∪ orderedTrackAlphabet ι)).card)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (htransport : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι j,translate a (u (ι j)) x.val) =
        (κ j,translate a (v (κ j)) x.val)) :
    (MulAut.conj z).toMonoidHom.comp (B.distinctSlotStar hlarge h hr ι u F V) =
      B.distinctSlotStar hlarge h hr κ v G V := by
  let S := ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range
  have hcS : B.c c ∈ S := B.constant_mem_polygonStars hlarge h hr c
  have hczS : (B.c c)⁻¹*z ∈ S := S.mul_mem (S.inv_mem hcS) hz
  let K := sourceAlignedGroup a r m hm M B.t (J∪C)
  have hcK : B.c c ∈ K := sourceAlignedGroup_mono B.t Finset.subset_union_right
    (B.constant_mem_sourceAligned c C hcC)
  have hzK : z ∈ K := sourceAlignedGroup_mono B.t Finset.subset_union_left hzJ
  have hfix : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) ((B.c c)⁻¹*z)).val.val
        (ι j,translate a (u (ι j)) x.val) = (ι j,translate a (u (ι j)) x.val) := by
    intro j x
    rw [map_mul,map_inv]
    change (coverMap M (alternatingGenerator a r m hm) (B.c c)).val.val.symm
      ((coverMap M (alternatingGenerator a r m hm) z).val.val _) = _
    rw [htransport j x,
      show coverMap M (alternatingGenerator a r m hm) (B.c c) =
        conditionalAlternatingHom (wholePolygon a) c from DFunLike.congr_fun B.c_projection c]
    change (conditionalPerm (wholePolygon a) c.val).symm
      (κ j,translate a (v (κ j)) x.val) = _
    have hci : c.val.symm (κ j)=ι j := by rw [← hc j]; exact c.val.symm_apply_apply _
    simp [conditionalPerm,wholePolygon,hci,← huv j]
  ext s : 1
  have hh := B.distinct_slot_fixer hlarge h hr ι b hb u F V (J∪C) hreserve
    ((B.c c)⁻¹*z) hczS (K.mul_mem (K.inv_mem hcK) hzK) hfix s
  have he := DFunLike.congr_fun (B.distinctSlotStar_constant_transport hlarge h hr
    R hR ι κ c hc b hb' u v huv F G V) s
  change z * B.distinctSlotStar hlarge h hr ι u F V s * z⁻¹ = _
  change B.c c * B.distinctSlotStar hlarge h hr ι u F V s * (B.c c)⁻¹ =
    B.distinctSlotStar hlarge h hr κ v G V s at he
  rw [← he]
  calc
    z * B.distinctSlotStar hlarge h hr ι u F V s * z⁻¹ =
      B.c c * (((B.c c)⁻¹*z)*B.distinctSlotStar hlarge h hr ι u F V s) * z⁻¹ := by group
    _ = B.c c * (B.distinctSlotStar hlarge h hr ι u F V s*((B.c c)⁻¹*z)) * z⁻¹ := by rw [hh.eq]
    _ = B.c c * B.distinctSlotStar hlarge h hr ι u F V s * (B.c c)⁻¹ := by group

theorem distinctSlotStar_aligned_transport
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (ι κ : Fin 5 ↪ Fin (m+1))
    (u v : Fin (m+1) → CutRing × CutRing) (huv : ∀ j, u (ι j)=v (κ j))
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (G : OffsetFrame a r m hm (orderedTrackAlphabet κ) v) (V : polygonAlgebra a)
    (J : Finset (Fin (m+1))) (hreserve : J.card+38 ≤ m+1)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (htransport : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι j,translate a (u (ι j)) x.val) =
        (κ j,translate a (v (κ j)) x.val)) :
    (MulAut.conj z).toMonoidHom.comp (B.distinctSlotStar hlarge h hr ι u F V) =
      B.distinctSlotStar hlarge h hr κ v G V := by
  classical
  obtain ⟨C,hC,c,hcC,hc⟩ := exists_small_even_reindex (by omega : 12 ≤ m+1) ι κ
  have hcard (e : Fin 5 ↪ Fin (m+1)) : (orderedTrackAlphabet e).card=5 := by
    simp [orderedTrackAlphabet]
  have hab : (orderedTrackAlphabet ι ∪ orderedTrackAlphabet κ).card <
      (Finset.univ : Finset (Fin (m+1))).card := by
    have hh := Finset.card_union_le (orderedTrackAlphabet ι) (orderedTrackAlphabet κ)
    rw [hcard,hcard] at hh
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hab
  have hbι : b ∉ orderedTrackAlphabet ι := fun hh => hb (Finset.mem_union_left _ hh)
  have hbκ : b ∉ orderedTrackAlphabet κ := fun hh => hb (Finset.mem_union_right _ hh)
  apply B.distinctSlotStar_aligned_transport_with_reindex hlarge h hr R hR ι κ c hc C hcC
    b hbι hbκ u v huv F G V J _ z hz hzJ htransport
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
  have h₁ := Finset.card_union_le J C
  have h₂ := Finset.card_insert_le b (J∪C)
  have h₃ := Finset.card_union_le (insert b (J∪C)) (orderedTrackAlphabet ι)
  rw [hC] at h₁
  rw [hcard] at h₃
  omega

end InitialCoverSystem
end SmallEvenRouting

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_RoutingIndependence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem slotRouting_nonempty (hwide : 26 ≤ m+1) (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    Nonempty (B.SlotRouting hlarge h hr V i u) := by
  classical
  have hres : 20 ≤ ((Finset.univ : Finset (Fin (m+1))) \
      (∅ ∪ Finset.univ.image i)).card := by
    rw [Finset.empty_union,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hc := Finset.card_image_le (f := i) (s := Finset.univ)
    simp only [Finset.card_univ,Fintype.card_fin] at hc ⊢
    omega
  obtain ⟨P,_⟩ := exists_privateRoutingBank i ∅ hres
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show P.alphabet.card < (Finset.univ : Finset (Fin (m+1))).card by
      have hc := P.alphabet_card
      simp only [Finset.card_univ,Fintype.card_fin]
      omega)
  have ht (j : Fin 5) : P.target j ∈ P.alphabet :=
    P.row_subset j (orderedTrackAlphabet_mem (P.row j) 1)
  have hbt : b ∉ orderedTrackAlphabet P.target := by
    intro hh
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hh
    exact hb (ht j)
  obtain ⟨w,hw,hwJ,hwt⟩ := B.repeated_bank_routing hlarge h hr i u P b hb V hinj
  exact ⟨{
    alphabet := P.alphabet
    card_le := P.alphabet_card
    source_mem := P.source_mem
    target := P.target
    target_mem := ht
    offsets := orderedOffsets P.target u
    offsets_spec := orderedOffsets_apply P.target u
    frame := balancedOffsetFrame a r m hm _ b hbt (orderedOffsets P.target u)
    word := w
    aligned := hw
    supported := hwJ
    transport := hwt }⟩

namespace SlotRouting
variable {B hlarge h hr}

theorem aligned_transport
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    {V : polygonAlgebra a} {i k : Fin 5 → Fin (m+1)} {u : Fin 5 → CutRing × CutRing}
    (ρ : B.SlotRouting hlarge h hr V i u) (σ : B.SlotRouting hlarge h hr V k u)
    (J : Finset (Fin (m+1))) (hwide : J.card+88 ≤ m+1)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (htransport : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (i j,translate a (u j) x.val) =
        (k j,translate a (u j) x.val)) :
    (MulAut.conj z).toMonoidHom.comp ρ.star = σ.star := by
  classical
  let S := ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range
  let K := σ.alphabet ∪ J ∪ ρ.alphabet
  let L := sourceAlignedGroup a r m hm M B.t K
  let w := σ.word*z*ρ.word⁻¹
  have hwS : w ∈ S := S.mul_mem (S.mul_mem σ.aligned hz) (S.inv_mem ρ.aligned)
  have hσL : σ.word ∈ L := sourceAlignedGroup_mono B.t
    (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left) σ.supported
  have hρL : ρ.word ∈ L := sourceAlignedGroup_mono B.t Finset.subset_union_right ρ.supported
  have hzL : z ∈ L := sourceAlignedGroup_mono B.t
    (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left) hzJ
  have hwL : w ∈ L := L.mul_mem (L.mul_mem hσL hzL) (L.inv_mem hρL)
  have hK : K.card+38 ≤ m+1 := by
    have h₁ := Finset.card_union_le σ.alphabet J
    have h₂ := Finset.card_union_le (σ.alphabet∪J) ρ.alphabet
    have hρ := ρ.card_le
    have hσ := σ.card_le
    dsimp [K]
    omega
  have hwt : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) w).val.val
        (ρ.target j,translate a (ρ.offsets (ρ.target j)) x.val) =
        (σ.target j,translate a (σ.offsets (σ.target j)) x.val) := by
    intro j x
    rw [ρ.offsets_spec j,σ.offsets_spec j]
    change (coverMap M (alternatingGenerator a r m hm) (σ.word*z*ρ.word⁻¹)).val.val _ = _
    rw [map_mul,map_mul,map_inv]
    change (coverMap M (alternatingGenerator a r m hm) σ.word).val.val
      ((coverMap M (alternatingGenerator a r m hm) z).val.val
        ((coverMap M (alternatingGenerator a r m hm) ρ.word).val.val.symm _)) = _
    rw [← ρ.transport j x,Equiv.symm_apply_apply,htransport j x,σ.transport j x]
  have he := B.distinctSlotStar_aligned_transport hlarge h hr R hR ρ.target σ.target
    ρ.offsets σ.offsets (fun j => (ρ.offsets_spec j).trans (σ.offsets_spec j).symm)
    ρ.frame σ.frame V K hK w hwS hwL hwt
  ext s : 1
  have hh := DFunLike.congr_fun he s
  change w*B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s*w⁻¹ =
    B.distinctSlotStar hlarge h hr σ.target σ.offsets σ.frame V s at hh
  change z*(ρ.word⁻¹*B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s*(ρ.word⁻¹)⁻¹)*z⁻¹ =
    σ.word⁻¹*B.distinctSlotStar hlarge h hr σ.target σ.offsets σ.frame V s*(σ.word⁻¹)⁻¹
  simp only [inv_inv]
  rw [← hh]
  dsimp [w]
  group

theorem independent
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 88 ≤ m+1) {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing}
    (ρ σ : B.SlotRouting hlarge h hr V i u) : ρ.star=σ.star := by
  have he := ρ.aligned_transport R hR σ ∅ (by simpa using hwide) 1
    (Subgroup.one_mem _) (Subgroup.one_mem _) (by intro j x; simp)
  ext s : 1
  have hh := DFunLike.congr_fun he s
  change 1*ρ.star s*1⁻¹=σ.star s at hh
  simpa using hh

end SlotRouting
end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CanonicalSlotStars
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

noncomputable def slotStar (hwide : 100 ≤ m+1) (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    UniversalExtension (alternatingGroup (Fin 5)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.slotRouting_nonempty hlarge h hr (by omega) V i u hinj).some.star

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_eq_routing (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (ρ : B.SlotRouting hlarge h hr V i u) :
    B.slotStar hlarge h hr hwide V i u hinj=ρ.star :=
  SlotRouting.independent R hR (by omega) _ ρ

theorem slotStar_union (V W : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) (V ⊔ W) (fun j => (i j,u j))))
    (hd : Disjoint V.val W.val) (s : UniversalExtension (alternatingGroup (Fin 5))) :
    B.slotStar hlarge h hr hwide (V ⊔ W) i u hinj s =
      B.slotStar hlarge h hr hwide V i u (SlotMap_injective_mono _ le_sup_left hinj) s *
      B.slotStar hlarge h hr hwide W i u (SlotMap_injective_mono _ le_sup_right hinj) s := by
  let ρ := (B.slotRouting_nonempty hlarge h hr (by omega) (V ⊔ W) i u hinj).some
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide _ _ _ hinj ρ,
    B.slotStar_eq_routing hlarge h hr R hR hwide _ _ _ _ (ρ.restrict V le_sup_left),
    B.slotStar_eq_routing hlarge h hr R hR hwide _ _ _ _ (ρ.restrict W le_sup_right)]
  exact ρ.star_union hd s

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PeriodicSlotStars
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_reduce (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    B.slotStar hlarge h hr hwide V i u hinj=
      B.slotStar hlarge h hr hwide V i (fun j => orbitRepresentative (u j))
        (by rw [← SlotMap_orbitRepresentative]; exact hinj) := by
  let ρ := (B.slotRouting_nonempty hlarge h hr (by omega) V i u hinj).some
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide V i u hinj ρ,
    B.slotStar_eq_routing hlarge h hr R hR hwide V i _ _ ρ.reduce,ρ.reduce_star]

theorem slotStar_empty (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) (⊥ : polygonAlgebra a) (fun j => (i j,u j)))) :
    B.slotStar hlarge h hr hwide ⊥ i u hinj=1 := by
  let ρ := (B.slotRouting_nonempty hlarge h hr (by omega) ⊥ i u hinj).some
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide ⊥ i u hinj ρ,ρ.star_empty]

theorem slotStar_parameterwise (V : polygonAlgebra a)
    (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (hkinj : Function.Injective (SlotMap a (m+1) V (fun j => (k j,v j))))
    (he : ∀ j, ∀ x : V.val, (i j,translate a (u j) x.val)=(k j,translate a (v j) x.val)) :
    B.slotStar hlarge h hr hwide V i u hinj=B.slotStar hlarge h hr hwide V k v hkinj := by
  by_cases hV : V.val.Nonempty
  · obtain ⟨x,hx⟩ := hV
    have hik : i=k := funext (fun j => congrArg Prod.fst (he j ⟨x,hx⟩))
    have huv : (fun j => orbitRepresentative (u j))=(fun j => orbitRepresentative (v j)) := by
      funext j
      exact orbitRepresentative_eq_of_translate_eq x (congrArg Prod.snd (he j ⟨x,hx⟩))
    rw [B.slotStar_reduce hlarge h hr R hR hwide V i u hinj,
      B.slotStar_reduce hlarge h hr R hR hwide V k v hkinj]
    congr 1
  · have hbot : V=⊥ := Subtype.ext (Set.not_nonempty_iff_eq_empty.mp hV)
    subst V
    rw [B.slotStar_empty hlarge h hr R hR hwide,B.slotStar_empty hlarge h hr R hR hwide]

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FiniteSlotRefinement
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section SlotTransportClosure

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hwide : 100 ≤ m+1)

def ExactSlotTransport (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (V : polygonAlgebra a) (i k : Fin 5 → Fin (m+1))
    (u v : Fin 5 → CutRing × CutRing) : Prop :=
  ∀ (hi : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)) ))
    (hk : Function.Injective (SlotMap a (m+1) V (fun j => (k j,v j)) )),
    (MulAut.conj z).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hi) =
      B.slotStar hlarge h hr hwide V k v hk

def UniformSlotTransport (z : BoundedRelationCover M (alternatingGenerator a r m hm)) : Prop :=
  ∀ (V : polygonAlgebra a) (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing),
    (∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (i j,translate a (u j) x.val)=
        (k j,translate a (v j) x.val)) →
    B.ExactSlotTransport hlarge h hr hwide z V i k u v

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
include R hR

theorem exactSlotTransport_empty (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing) :
    B.ExactSlotTransport hlarge h hr hwide z ⊥ i k u v := by
  intro hi hk
  rw [B.slotStar_empty hlarge h hr R hR hwide,B.slotStar_empty hlarge h hr R hR hwide]
  ext s : 1
  simp

theorem exactSlotTransport_union (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (V W : polygonAlgebra a) (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing)
    (hd : Disjoint V.val W.val)
    (hV : B.ExactSlotTransport hlarge h hr hwide z V i k u v)
    (hW : B.ExactSlotTransport hlarge h hr hwide z W i k u v) :
    B.ExactSlotTransport hlarge h hr hwide z (V ⊔ W) i k u v := by
  intro hi hk
  ext s : 1
  change (MulAut.conj z).toMonoidHom (B.slotStar hlarge h hr hwide (V ⊔ W) i u hi s)=_
  rw [B.slotStar_union hlarge h hr R hR hwide V W i u hi hd,map_mul,
    B.slotStar_union hlarge h hr R hR hwide V W k v hk hd]
  rw [show (MulAut.conj z).toMonoidHom (B.slotStar hlarge h hr hwide V i u
    (SlotMap_injective_mono _ le_sup_left hi) s)=_ from
      DFunLike.congr_fun (hV _ _) s]
  rw [show (MulAut.conj z).toMonoidHom (B.slotStar hlarge h hr hwide W i u
    (SlotMap_injective_mono _ le_sup_right hi) s)=_ from
      DFunLike.congr_fun (hW _ _) s]

theorem exactSlotTransport_cover (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (V : polygonAlgebra a) (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing)
    (s : Finset (polygonAlgebra a)) (hs : V ≤ s.sup id)
    (hl : ∀ W∈s, ∀ Z : polygonAlgebra a, Z≤W → Z≤V →
      B.ExactSlotTransport hlarge h hr hwide z Z i k u v) :
    B.ExactSlotTransport hlarge h hr hwide z V i k u v := by
  have hp : ∀ hV : V≤V, B.ExactSlotTransport hlarge h hr hwide z V i k u v := by
    refine polygon_finite_cover_induction
      (fun W => W≤V → B.ExactSlotTransport hlarge h hr hwide z W i k u v)
      (fun _ => B.exactSlotTransport_empty hlarge h hr hwide R hR z i k u v) ?_ s V hs ?_
    · intro U W hd hU hW he
      exact B.exactSlotTransport_union hlarge h hr hwide R hR z U W i k u v hd
        (hU (le_trans le_sup_left he)) (hW (le_trans le_sup_right he))
    · exact hl
  exact hp le_rfl

theorem uniformSlotTransport_one :
    B.UniformSlotTransport hlarge h hr hwide 1 := by
  intro V i k u v htr hi hk
  have he := B.slotStar_parameterwise hlarge h hr R hR hwide V i k u v hi hk (by
    intro j x
    simpa only [map_one,Subgroup.coe_one,Equiv.Perm.one_apply] using htr j x)
  rw [← he]
  ext s : 1
  simp

omit R hR in
theorem uniformSlotTransport_inv
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : B.UniformSlotTransport hlarge h hr hwide z) :
    B.UniformSlotTransport hlarge h hr hwide z⁻¹ := by
  intro V i k u v htr hi hk
  have htr' : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (k j,translate a (v j) x.val)=
        (i j,translate a (u j) x.val) := by
    intro j x
    have hh := congrArg (coverMap M (alternatingGenerator a r m hm) z).val.val (htr j x)
    simpa only [map_inv,Subgroup.coe_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hh.symm
  have he := hz V k i v u htr' hk hi
  ext s : 1
  have hh := DFunLike.congr_fun he s
  change z*B.slotStar hlarge h hr hwide V k v hk s*z⁻¹=
    B.slotStar hlarge h hr hwide V i u hi s at hh
  change z⁻¹*B.slotStar hlarge h hr hwide V i u hi s*(z⁻¹)⁻¹=_
  rw [← hh]
  group

theorem uniformSlotTransport_mul
    (z y : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : B.UniformSlotTransport hlarge h hr hwide z)
    (hy : B.UniformSlotTransport hlarge h hr hwide y) :
    B.UniformSlotTransport hlarge h hr hwide (z*y) := by
  intro V i k u v htr
  obtain ⟨s,hs,hcharts⟩ := finite_slot_chart_cover
    (coverMap M (alternatingGenerator a r m hm) y).val.val
    (coverMap M (alternatingGenerator a r m hm) y).val.property V i u
  apply B.exactSlotTransport_cover hlarge h hr hwide R hR (z*y) V i k u v s hs
  intro W hW Z hZW hZV hi hk
  obtain ⟨l,b,hl⟩ := hcharts W hW
  have hytr : ∀ (j : Fin 5) (x : Z.val),
      (coverMap M (alternatingGenerator a r m hm) y).val.val (i j,translate a (u j) x.val)=
        (l j,translate a (b j) x.val) := fun j x => hl j ⟨x.val,hZW x.property⟩
  have hl_inj := SlotMap_injective_of_transport Z i l u b _
    (coverMap M (alternatingGenerator a r m hm) y).val.val.injective hi hytr
  have hztr : ∀ (j : Fin 5) (x : Z.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (l j,translate a (b j) x.val)=
        (k j,translate a (v j) x.val) := by
    intro j x
    have hh := htr j ⟨x.val,hZV x.property⟩
    rw [map_mul] at hh
    change (coverMap M (alternatingGenerator a r m hm) z).val.val
      ((coverMap M (alternatingGenerator a r m hm) y).val.val (i j,translate a (u j) x.val))=_ at hh
    rw [hytr j x] at hh
    exact hh
  have he_y := hy Z i l u b hytr hi hl_inj
  have he_z := hz Z l k b v hztr hl_inj hk
  ext t : 1
  have ey := DFunLike.congr_fun he_y t
  have ez := DFunLike.congr_fun he_z t
  change y*B.slotStar hlarge h hr hwide Z i u hi t*y⁻¹=
    B.slotStar hlarge h hr hwide Z l b hl_inj t at ey
  change z*B.slotStar hlarge h hr hwide Z l b hl_inj t*z⁻¹=
    B.slotStar hlarge h hr hwide Z k v hk t at ez
  change (z*y)*B.slotStar hlarge h hr hwide Z i u hi t*(z*y)⁻¹=_
  calc
    _ = z*(y*B.slotStar hlarge h hr hwide Z i u hi t*y⁻¹)*z⁻¹ := by group
    _ = _ := by rw [ey,ez]

def slotTransportSubgroup : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) where
  carrier := B.UniformSlotTransport hlarge h hr hwide
  one_mem' := B.uniformSlotTransport_one hlarge h hr hwide R hR
  mul_mem' := fun {z y} => B.uniformSlotTransport_mul hlarge h hr hwide R hR z y
  inv_mem' := fun {z} => B.uniformSlotTransport_inv hlarge h hr hwide z

end InitialCoverSystem
end SlotTransportClosure

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ShiftedRouting
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ShiftedRouting
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

namespace SlotRouting
variable {B hlarge h hr}

noncomputable def privateBank (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    B.SlotRouting hlarge h hr V i u where
  alphabet := P.alphabet
  card_le := P.alphabet_card
  source_mem := P.source_mem
  target := P.target
  target_mem := fun j => P.row_subset j (orderedTrackAlphabet_mem _ 1)
  offsets := orderedOffsets P.target u
  offsets_spec := orderedOffsets_apply P.target u
  frame := balancedOffsetFrame a r m hm _ b (by
    intro ht
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp ht
    exact hb (P.row_subset j (orderedTrackAlphabet_mem _ 1))) (orderedOffsets P.target u)
  word := B.privateRoutingWord hlarge h hr i u P b hb V
  aligned := (B.privateRoutingWord_properties hlarge h hr i u P b hb V hinj).1
  supported := (B.privateRoutingWord_properties hlarge h hr i u P b hb V hinj).2.1
  transport := (B.privateRoutingWord_properties hlarge h hr i u P b hb V hinj).2.2

end SlotRouting

end InitialCoverSystem
end ShiftedRouting

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SlotInputGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SlotInputGeneration

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

noncomputable def slotGroup : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  Subgroup.closure {z | ∃ (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing)
    (hi : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (s : UniversalExtension (alternatingGroup (Fin 5))), z=B.slotStar hlarge h hr hwide V i u hi s}

end InitialCoverSystem
end SlotInputGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_HomologyAdditive
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

namespace PolygonPlacement.Configuration
attribute [local instance 1200] Rep.hV2
variable {a m p : ℕ}

noncomputable abbrev column (a m p : ℕ) :=
  Rep.of (TransitiveInduction.permutationRep
    (G:=polygonFullGroup a m) (X:=Configuration a m p))

end PolygonPlacement.Configuration
end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonPiecewiseSlots
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonPiecewiseSlots

open Classical Set
namespace PolygonArea

@[simp] theorem val_finset_inf {a : ℕ} {ι : Type*} (s : Finset ι) (f : ι → polygonAlgebra a) :
    (s.inf f).val=⋂i∈s,(f i).val := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.inf_insert,BooleanSubalgebra.val_inf,ih]

end PolygonArea
namespace PolygonObject

noncomputable def whole (a m : ℕ) : PolygonObject a := ⟨m,fun _ => ⊤⟩

theorem intoWhole_hasTable {a : ℕ} {U V : PolygonObject a} {f : U.Point → V.Point}
    (hf : HasTable f) :
    HasTable (fun x => (⟨(f x).val,by trivial⟩ : (whole a V.tracks).Point)) := hf

end PolygonObject
end PolygonPiecewiseSlots

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonBankEmbedding
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonBankEmbedding

open Classical Set
namespace PolygonObject

structure BankEmbedding {a : ℕ} (U : PolygonObject a) (m : ℕ) where
  emb : U.Point ↪ TrackPoint a m
  table : HasTable (fun x => (⟨emb x,by trivial⟩ : (whole a m).Point))

namespace BankEmbedding
variable {a m : ℕ} {U : PolygonObject a}
instance instCoeFunForallPointTrackPoint : CoeFun (BankEmbedding U m) (fun _ => U.Point → TrackPoint a m) := ⟨fun f => f.emb⟩

theorem injective (f : BankEmbedding U m) : Function.Injective f := f.emb.injective

theorem range_fiber_polygon (f : BankEmbedding U m) (i : Fin m) :
    {x | (i,x)∈Set.range f}∈polygonAlgebra a := by
  obtain ⟨S,hS,hcov⟩ := f.table
  change Finset (Chart (a:=a) U.tracks m) at S
  let Q (c : Chart (a:=a) U.tracks m) : polygonAlgebra a :=
    if c.target=i then translatedPolygon c.shift c.domain else ⊥
  have he : {x | (i,x)∈Set.range f}=(S.sup Q).val := by
    rw [PolygonArea.val_finset_sup]
    ext y
    constructor
    · rintro ⟨p,hp⟩
      obtain ⟨c,hc,hs,hx⟩ := hcov p
      obtain ⟨hu,hf⟩ := hS c hc p.val.2 hx
      have he : (⟨(c.source,p.val.2),hu⟩ : U.Point)=p := Subtype.ext (Prod.ext hs.symm rfl)
      change f ⟨(c.source,p.val.2),hu⟩=(c.target,translate a c.shift p.val.2) at hf
      rw [he,hp] at hf
      refine Set.mem_iUnion₂.mpr ⟨c,hc,?_⟩
      have ht : c.target=i := (congrArg Prod.fst hf).symm
      simp only [Q,ht,ite_true]
      exact ⟨p.val.2,hx,(congrArg Prod.snd hf).symm⟩
    · intro hy
      obtain ⟨c,hc,hy⟩ := Set.mem_iUnion₂.mp hy
      by_cases ht : c.target=i
      · simp only [Q,ht,ite_true] at hy
        obtain ⟨x,hx,rfl⟩ := hy
        obtain ⟨hu,he⟩ := hS c hc x hx
        refine ⟨⟨(c.source,x),hu⟩,?_⟩
        change f ⟨(c.source,x),hu⟩=(c.target,translate a c.shift x) at he
        change f ⟨(c.source,x),hu⟩=(i,translate a c.shift x)
        exact he.trans (congrArg (fun j => (j,translate a c.shift x)) ht)
      · simp only [Q,ht,ite_false] at hy
        exact False.elim hy
  rw [he]
  exact (S.sup Q).property

noncomputable def imageBank (f : BankEmbedding U m) (i : Fin m) : polygonAlgebra a :=
  ⟨{x | (i,x)∈Set.range f},range_fiber_polygon f i⟩

theorem exists_into {U V : Fin m → polygonAlgebra a}
    (h : (∑i,PolygonArea.area (U i))<∑i,PolygonArea.area (V i)) :
    ∃f : BankEmbedding (PolygonObject.mk m U) m,∀p,(f p).2∈(V (f p).1).val := by
  obtain ⟨f,hf⟩ := PolygonGrid.strict_comparison U V h
  exact ⟨⟨⟨fun p => (f p).val,fun _ _ he => f.injective (Subtype.ext he)⟩,hf⟩,fun p => (f p).property⟩

end BankEmbedding
end PolygonObject
end PolygonBankEmbedding

section PolygonBankReserve

open Classical Set
namespace PolygonObject
namespace BankEmbedding
variable {a m b : ℕ}

noncomputable def inclusion (U : Fin m → polygonAlgebra a) : BankEmbedding (PolygonObject.mk m U) m :=
  ⟨⟨Subtype.val,Subtype.val_injective⟩,intoWhole_hasTable (identity_hasTable _)⟩

end BankEmbedding
end PolygonObject
end PolygonBankReserve

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonSmallPartition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonSmallPartition

open Classical Set MeasureTheory
namespace PolygonGrid

noncomputable def strip (a : ℕ) (r : CutRing) (i : ℕ) : polygonAlgebra a :=
  ⟨halfPlane a 0 (r*(i+1)) ∩ (halfPlane a 0 (r*i))ᶜ,
    BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _))⟩

theorem mem_strip (a : ℕ) (r : CutRing) (i : ℕ) (x : GenericSquare a) :
    x∈(strip a r i).val ↔ x.val.1∈interval (ordinary r) i := by
  simp only [strip,halfPlane,interval,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_ofPred_eq,
    Set.mem_Ico,cutForm,Matrix.cons_val_zero,map_mul,map_add,map_natCast,map_one,not_lt]
  tauto

theorem strip_area_le (a : ℕ) (r : CutRing) (i : ℕ) :
    PolygonArea.area (strip a r i)≤ENNReal.ofReal (ordinary r) := by
  have hs : Subtype.val '' (strip a r i).val⊆interval (ordinary r) i ×ˢ Ico (0:ℝ) 1 := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨(mem_strip a r i x).mp hx,x.property.2.1⟩
  calc
    _≤(volume : Measure (ℝ×ℝ)) (interval (ordinary r) i ×ˢ Ico (0:ℝ) 1) := measure_mono hs
    _=ENNReal.ofReal (ordinary r) := by
      rw [show (volume : Measure (ℝ×ℝ))=Measure.prod (volume : Measure ℝ) volume from rfl]
      simp only [Measure.prod_prod,interval,Real.volume_Ico,sub_zero,ENNReal.ofReal_one,mul_one]
      congr 1
      ring

theorem small_bank_cover {a m : ℕ} {ε : ℝ} (hε : 0<ε) :
    ∃N : ℕ,∃P : Fin m × Fin N → Fin m → polygonAlgebra a,
      (∀p : TrackPoint a m,∃j,p.2∈(P j p.1).val) ∧
      ∀j,(∑i,PolygonArea.area (P j i))<ENNReal.ofReal ε := by
  obtain ⟨b,hr,hrε⟩ := exists_grid_side hε
  let r := shrinkingLevel b
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ordinary r)
  let P (j : Fin m × Fin N) (i : Fin m) : polygonAlgebra a :=
    if i=j.1 then strip a r j.2.val else ⊥
  refine ⟨N,P,?_,?_⟩
  · intro p
    have hp : (p.1.val,p.2.val.1,p.2.val.2)∈region m :=
      ⟨p.1.isLt,p.2.property.1,p.2.property.2.1⟩
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (region_covered hr hN hp)
    refine ⟨(p.1,j.2.1),?_⟩
    simp only [P,ite_true]
    exact (mem_strip a r _ p.2).mpr hj.2.1
  · intro j
    have he : (∑i,PolygonArea.area (P j i))=PolygonArea.area (strip a r j.2.val) := by
      simp [P,apply_ite,PolygonArea.area_bot]
    rw [he]
    exact (strip_area_le a r j.2.val).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr hrε)

end PolygonGrid
namespace PolygonObject.BankEmbedding
variable {a m : ℕ}

noncomputable def full_restrict (f : polygonFullGroup a m) (U : Fin m → polygonAlgebra a) :
    BankEmbedding (PolygonObject.mk m U) m where
  emb := ⟨fun p => f.val p.val,fun _ _ he => Subtype.ext (f.val.injective he)⟩
  table := by
    obtain ⟨S,hS,hcover⟩ := f.property
    let conv (c : TableChart a m) : PolygonObject.Chart (a:=a) m m :=
      ⟨c.source,c.target,c.shift,U c.source ⊓ c.domain⟩
    refine ⟨S.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      exact ⟨hx.1,hS d hd x hx.2⟩
    · intro p
      obtain ⟨c,hc,hr,hx⟩ := hcover p.val
      refine ⟨conv c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,hr,?_,hx⟩
      simpa only [←hr] using p.property

@[simp] theorem full_restrict_apply (f : polygonFullGroup a m) (U : Fin m → polygonAlgebra a)
    (p : (PolygonObject.mk m U).Point) : full_restrict f U p=f.val p.val := rfl

end PolygonObject.BankEmbedding
end PolygonSmallPartition

end SimpleAmenable
end
end

end OAI
end



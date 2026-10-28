-- Prove2me | Definitions.Def_OAIQ65Sa013
-- name    : OAIQ65Sa013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:17:42.972349+00:00
-- url     : https://prove2.me/theorems/2f75374c-b865-47fa-be4d-861ef318327e
-- title:
--   Definitions bundle OAIQ65Sa013 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 121 declarations of OpenAI's Lean: 40 definitions, 4 inductive types or structures, 5 instances and 72 theorems. The definitions and types are `OAI.RestrictedNerve.diagramTranspose`, `OAI.RestrictedNerve.innerReindexRight`, `OAI.RestrictedNerve.innerResolutionAugmentation`, `OAI.RestrictedNerve.innerResolutionRows`, `OAI.RestrictedNerve.innerRowsMiddle`, `OAI.RestrictedNerve.innerRowsOuter`, `OAI.RestrictedNerve.middleResolutionAugmentation`, `OAI.RestrictedNerve.middleResolutionRows`, `OAI.RestrictedNerve.middleRowsOuter`, `OAI.RestrictedNerve.outerResolutionAugmentation`, `OAI.RestrictedNerve.outerResolutionRows`, `OAI.RestrictedNerve.stringBarAugmentation`, `OAI.RestrictedNerve.stringBarRows`, `OAI.RestrictedNerve.stringBarTotalComponent`, `OAI.RestrictedNerve.stringBarTotalIso`, `OAI.RestrictedNerve.totalStringToBar`, `OAI.RestrictedNerve.transposeReindexHom`, `OAI.RestrictedNerve.tripleDiagramHorizontal`, `OAI.RestrictedNerve.tripleDiagramResolutionHomologyIso`, `OAI.RestrictedNerve.tripleDiagramTranspose`, `OAI.RestrictedNerve.tripleInnerReindex`, `OAI.RestrictedNerve.tripleMiddleReindex`, `OAI.RestrictedNerve.tripleOuterReindex`, `OAI.RestrictedNerve.tripleResolutionAugmentation`, `OAI.SimpleAmenable.ConfigurationChains.boundaryRep`, `OAI.SimpleAmenable.InitialCoverSystem.FinePatchAtlas`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.concurrentCoordinateEmbedding`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas`, `OAI.SimpleAmenable.PolygonPlacement`, `OAI.SimpleAmenable.PolygonPlacement.Apart`, `OAI.SimpleAmenable.PolygonPlacement.Configuration`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.chainEquiv`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.listEquiv`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.standard`, `OAI.SimpleAmenable.PolygonPlacement.bank`, `OAI.SimpleAmenable.PolygonPlacement.familyPerm`, `OAI.SimpleAmenable.PolygonPlacement.imageBank`, `OAI.SimpleAmenable.PolygonPlacement.perm`, `OAI.SimpleAmenable.PolygonPlacement.permHom` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_CentralCovers_CommonFrameTransport`, `SimpleAmenable_CentralCovers_ConcurrentCoordinateGates`, `SimpleAmenable_CentralCovers_LatticeTranslationTransport`, `SimpleAmenable_CentralCovers_RectangularAtlas`, `SimpleAmenable_Configurations_PolygonFixedTrackProgress`, `SimpleAmenable_Configurations_PolygonPlacementAlternating`, `SimpleAmenable_Configurations_PolygonPlacementArea`, `SimpleAmenable_Configurations_PolygonPlacementPermutation`, `SimpleAmenable_Configurations_TransitiveInduction`, `SimpleAmenable_Homology_HomologyAdditive`, `SimpleAmenable_PolygonGeometry_ConcurrentGeometry`, `SimpleAmenable_PolygonGeometry_FinePatchAtlas`, `SimpleAmenable_RandomFields_CanonicalPolygonCovariance`, `SimpleAmenable_RandomFields_PrimitiveCovariance`, `SimpleAmenable_Simplicial_MonoidalCongruence`, `SimpleAmenable_Simplicial_NestedPosReindex`, `SimpleAmenable_Simplicial_PositionalInclusionMonoidal`, `SimpleAmenable_Simplicial_ResolutionAugmentation`, `SimpleAmenable_Simplicial_RestrictedFunctorial`, `SimpleAmenable_Simplicial_RestrictedMonoidalTranspose`, `SimpleAmenable_Simplicial_RestrictedTripleDegree`, `SimpleAmenable_Simplicial_RestrictedTripleMaps`, `SimpleAmenable_Simplicial_StringBarNaturality`, `SimpleAmenable_Simplicial_StringEvaluation`, `SimpleAmenable_Simplicial_Supplemental`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa007`, `OAIQ65Sa010` and `OAIQ65Sa011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa015` and `OAIQ65Sa016`; the statements `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.translated_slope_coordinate_formal_law`, `OAI_SimpleAmenable_PolygonTracks_fullH2_finite_of_bar`, `OAI.SimpleAmenable.finePatchAtlas_eventually` and `OAI.SimpleAmenable.rectangularAtlas_fixed_radius_eventually`; the proofs of `OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_primitive_table_with_coordinates`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.translated_slope_coordinate_formal_law`, `OAI.SimpleAmenable.coordinateWindowLaw_eventually`, `OAI.SimpleAmenable.finePatchAtlas_eventually`, `OAI.SimpleAmenable.fixed_track_polygon_progress`, `OAI_SimpleAmenable_polygon_full_low_homology_finite`, `OAI.SimpleAmenable.rectangularAtlas_fixed_radius_eventually` and `OAI.SimpleAmenable.tangentChartTables_eventually`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa007
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PrimitiveCovariance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PrimitiveCovariance

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem primitiveCopy_conjugate (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (u : CutRing × CutRing)
    (F : CommonFrame a r m hm I u) (p : Fin 5 × (CutRing × CutRing)) :
    B.primitiveCopy I b hb (p.1,u+p.2) =
      (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.primitiveCopy I b hb p) := by
  rw [B.primitiveCopy_frame I b hb _ (F.mul (commonFrame a r m hm I b hb p.2))]
  exact B.translatedAlphabet_mul I p.1 F.k _

theorem initialAlphabet_conjugate_common (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (u : CutRing × CutRing)
    (F : CommonFrame a r m hm I u) :
    (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.initialAlphabet I 0) = B.initialAlphabet I 0 := by
  rw [← B.primitiveCopy_zero I b hb 0,← B.primitiveCopy_conjugate I b hb u F]
  have hz : spatialTranslate (u+0) (initialTest a r 0) =
      spatialTranslate 0 (initialTest a r 0) := by
    change spatialTranslate (u+0) (wholePolygon a) = spatialTranslate 0 (wholePolygon a)
    simp
  rw [B.primitiveCopy_translate_eq I b hb 0 (u+0) 0 hz]

end InitialCoverSystem
end PrimitiveCovariance

section FamilyCovariance

variable {ι E H Q : Type*} [Group E] [Group H] [Group Q]

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem primitiveFamily_conjugate (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (u : CutRing × CutRing) (F : CommonFrame a r m hm I u) :
    B.primitiveFamily I b hb (fun i => ((P i).1,u+(P i).2)) =
      fun i => (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.primitiveFamily I b hb P i) := by
  funext i
  cases i with
  | none => exact (B.initialAlphabet_conjugate_common I b hb u F).symm
  | some i => exact B.primitiveCopy_conjugate I b hb u F (P i)

end InitialCoverSystem
end FamilyCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_RectangularAtlas
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

structure RectangularAtlas where
  k : ℕ
  p : Fin 2 → ℤ
  u : CutRing
  v : CutRing
  inverse : u*v=1
  short : 4*(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) ≤ ordinary r
  labels : ∀ d e j,
    (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
     endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
    (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
     endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k)
  rectangles : ∀ n, B.CoordinateWindowLaw n
  charts : B.TangentChartLaws k p u
  radius : CutRing
  radius_pos : 0 < ordinary radius
  radius_small : ordinary radius < ordinary r/8
  quadrants : B.TangentChartLaws (symmetricWindowLength radius) (symmetricWindowStart radius) u

end InitialCoverSystem

end RectangularAtlas

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section ConcurrentGeometry

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

structure PatchAtlas where
  rectangles : B.RectangularAtlas
  geometry : ConcurrentGeometry a r
  initial : ∀ u I b hb, B.PrimitiveFamilyLaw I b hb
    (translatedTemplate (initialPatchPrimitives r geometry.mesh) u)
  concurrent : ∀ t u I b hb, B.PrimitiveFamilyLaw I b hb
    (translatedTemplate (Sum.elim
      (fun j : Fin 4 => (⟨j.val+1,by omega⟩,geometry.anchors t j))
      (coordinateWindowPrimitives geometry.window geometry.start)) u)

end InitialCoverSystem

end ConcurrentGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FinePatchAtlas
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FinePatchAtlas

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2  ≤  m}
    (B : InitialCoverSystem a r m hm M)

structure FinePatchAtlas extends B.PatchAtlas where
  far_mesh : (1+|ordinary (cutTau^a)|)*(200/(geometry.mesh:ℝ)) < ordinary rectangles.radius/4

end InitialCoverSystem

end FinePatchAtlas

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConcurrentCoordinateGates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

def concurrentCoordinateEmbedding :
    Sum (Fin 2) (Fin 2 × Fin (A.geometry.window-1)) →
      Sum (Fin 4) (Fin 2 × Fin (A.geometry.window-1)) :=
  Sum.map axisDirection id

end InitialCoverSystem.PatchAtlas
end ConcurrentCoordinateGates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_CanonicalPolygonCovariance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem geometricSector_translate {ι : Type*} [Finite ι]
    (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (u : CutRing × CutRing)
    (F : CommonFrame a r m hm I u)
    (g : B.PrimitiveFamilyLaw I b hb (translatedTemplate P u))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.geometricSector I b hb P h V) =
      B.geometricSector I b hb (translatedTemplate P u) g (spatialTranslate u V) := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb (translatedTemplate P u))).range g
  · rintro x ⟨s,rfl⟩
    change ∃ w, copyFamilyEval (B.primitiveFamily I b hb (translatedTemplate P u)) w =
      (MulAut.conj (B.t F.k)).toMonoidHom (B.geometricSector I b hb P h V s)
    change ∃ w, copyFamilyEval (B.primitiveFamily I b hb (fun i => ((P i).1,u+(P i).2))) w = _
    rw [B.primitiveFamily_conjugate I b hb P u F,copyFamilyEval_comp]
    obtain ⟨w,hw⟩ := B.geometricSector_mem I b hb P h V s
    exact ⟨w,congrArg (MulAut.conj (B.t F.k)).toMonoidHom hw⟩
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb _ g _ s
  · ext s : 1
    change coverMap M (alternatingGenerator a r m hm)
      (B.t F.k * B.geometricSector I b hb P h V s * (B.t F.k)⁻¹) =
      coverMap M (alternatingGenerator a r m hm)
        (B.geometricSector I b hb (translatedTemplate P u) g (spatialTranslate u V) s)
    rw [map_mul,map_mul,map_inv,
      show coverMap M (alternatingGenerator a r m hm) (B.t F.k) =
        sourceLatticeMap a r m hm F.k from DFunLike.congr_fun B.t_projection F.k,
      show coverMap M (alternatingGenerator a r m hm) (B.geometricSector I b hb P h V s) =
        conditionalAlternatingHom V (subtypeAlternatingHom I (universalProjection _ s)) from
        DFunLike.congr_fun (B.geometricSector_projection I b hb P h V hV) s,
      show coverMap M (alternatingGenerator a r m hm)
          (B.geometricSector I b hb (translatedTemplate P u) g (spatialTranslate u V) s) =
        conditionalAlternatingHom (spatialTranslate u V)
          (subtypeAlternatingHom I (universalProjection _ s)) from
        DFunLike.congr_fun (B.geometricSector_projection I b hb _ g _
          (translatedTemplate_resolved P V hV u)) s]
    exact F.conditional_projection V _

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem polygonStar_common_translate
    (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (u : CutRing × CutRing)
    (F : CommonFrame a r m hm I u) (V : polygonAlgebra a) :
    (MulAut.conj (B.t F.k)).toMonoidHom.comp
        ((B.polygonStar hlarge h hr V).comp (universalMap (subtypeAlternatingHom I))) =
      (B.polygonStar hlarge h hr (spatialTranslate u V)).comp (universalMap (subtypeAlternatingHom I)) := by
  obtain ⟨S,hS⟩ := polygon_finite_primitive_resolution r hr V
  let P : S → Fin 5 × (CutRing × CutRing) := fun p => p.val
  have hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val := hS
  rw [B.polygonStar_eq hlarge h hr P V hV,
    B.polygonStar_eq hlarge h hr (translatedTemplate P u) (spatialTranslate u V)
      (translatedTemplate_resolved P V hV u),
    B.fullGeometricSector_inclusion hlarge P _ I hI b hb (h S P I b hb) V hV,
    B.fullGeometricSector_inclusion hlarge (translatedTemplate P u) _ I hI b hb
      (h S (translatedTemplate P u) I b hb) (spatialTranslate u V)
      (translatedTemplate_resolved P V hV u)]
  exact B.geometricSector_translate I b hb P _ u F _ V hV

end InitialCoverSystem
end CanonicalPolygonCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CommonFrameTransport
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem frameStar_uniform (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card)
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (v : CutRing × CutRing) (hu : ∀ i ∈ I, u i=v) (V : polygonAlgebra a) :
    B.frameStar hlarge h hr I u F V =
      (B.polygonStar hlarge h hr (spatialTranslate v V)).comp (universalMap (subtypeAlternatingHom I)) := by
  let C : CommonFrame a r m hm I v := {
    k := F.k
    d := F.d
    projection := F.projection
    common := fun i hi => (F.prescribed i hi).trans (hu i hi) }
  exact B.polygonStar_common_translate hlarge h hr I hI b hb v C V

theorem distinctSlotStar_uniform_mem (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1))
    (hb : b ∉ orderedTrackAlphabet ι) (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (v : CutRing × CutRing) (hu : ∀ j, u (ι j)=v) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    B.distinctSlotStar hlarge h hr ι u F V s ∈
      ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range := by
  have hc : 5 ≤ (orderedTrackAlphabet ι).card := by
    rw [orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin]
  have huv : ∀ i ∈ orderedTrackAlphabet ι, u i=v := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
    exact hu j
  change B.frameStar hlarge h hr (orderedTrackAlphabet ι) u F V (universalMap (orderedTrackHom ι) s) ∈ _
  rw [B.frameStar_uniform hlarge h hr _ hc b hb u F v huv V]
  exact (le_iSup (fun W : polygonAlgebra a => (B.polygonStar hlarge h hr W).range) (spatialTranslate v V)) ⟨_,rfl⟩

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_LatticeTranslationTransport
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section LatticeTranslationTransport

noncomputable def sourceGeneratorOffsets (m : ℕ) (j : Fin m × Fin 2) :
    Fin (m+1) → CutRing × CutRing :=
  Pi.single j.1.castSucc (if j.2=0 then (cutTau,0) else (0,cutTau)) -
    Pi.single (Fin.last m) (if j.2=0 then (cutTau,0) else (0,cutTau))

noncomputable def sourceLatticeOffsets (m : ℕ) :
    FreeAbelianGroup (Fin m × Fin 2) →+ (Fin (m+1) → CutRing × CutRing) :=
  FreeAbelianGroup.lift (sourceGeneratorOffsets m)

@[simp] theorem sourceLatticeOffsets_of (m : ℕ) (j : Fin m × Fin 2) :
    sourceLatticeOffsets m (FreeAbelianGroup.of j)=sourceGeneratorOffsets m j :=
  FreeAbelianGroup.lift_apply_of _ _

end LatticeTranslationTransport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonFixedTrackProgress
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonConfigurations
open Classical Set

structure PolygonPlacement (a m : ℕ) where
  toEmbedding : GenericSquare a ↪ TrackPoint a m
  charts : ∃s : Finset (Fin m × (CutRing×CutRing) × polygonAlgebra a),
    (∀c∈s,∀x∈c.2.2.val,toEmbedding x=(c.1,translate a c.2.1 x)) ∧
    ∀x,∃c∈s,x∈c.2.2.val

namespace PolygonPlacement
variable {a m : ℕ}
instance instCoeFunForallGenericSquareTrackPoint : CoeFun (PolygonPlacement a m) (fun _ => GenericSquare a → TrackPoint a m) :=
  ⟨fun f => f.toEmbedding⟩

@[ext] theorem ext {f g : PolygonPlacement a m} (h : ∀x,f x=g x) : f=g := by
  cases f; cases g
  congr
  exact Function.Embedding.ext h

noncomputable def standard (i : Fin m) : PolygonPlacement a m where
  toEmbedding := ⟨fun x => (i,x),fun _ _ h => congrArg Prod.snd h⟩
  charts := by
    refine ⟨{(i,0,⊤)},?_,?_⟩
    · intro c hc x _
      obtain rfl := Finset.mem_singleton.mp hc
      change (i,x)=(i,translate a 0 x)
      rw [translate_zero]
    · intro x
      exact ⟨(i,0,⊤),Finset.mem_singleton_self _,by trivial⟩

@[simp] theorem standard_apply (i : Fin m) (x : GenericSquare a) :
    standard i x=(i,x) := rfl

noncomputable def postcompose (g : polygonFullGroup a m) (f : PolygonPlacement a m) :
    PolygonPlacement a m where
  toEmbedding := ⟨fun x => g.val (f x),g.val.injective.comp f.toEmbedding.injective⟩
  charts := by
    obtain ⟨s,hs,hcover⟩ := g.property
    obtain ⟨t,ht,tcover⟩ := f.charts
    let pairs := (s×ˢt).filter (fun cd => cd.1.source=cd.2.1)
    let conv : TableChart a m × (Fin m × (CutRing×CutRing) × polygonAlgebra a) →
        Fin m × (CutRing×CutRing) × polygonAlgebra a := fun cd =>
      (cd.1.target,cd.1.shift+cd.2.2.1,
        ⟨cd.2.2.2.val ∩ translate a cd.2.2.1 ⁻¹' cd.1.domain.val,
          BooleanSubalgebra.inf_mem cd.2.2.2.property
            (polygon_preimage_translate cd.2.2.1 cd.1.domain.property)⟩)
    refine ⟨pairs.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨⟨d,e⟩,hde,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hde
      obtain ⟨hd,he'⟩ := Finset.mem_product.mp hp
      intro x hx
      change g.val (f x)=(d.target,translate a (d.shift+e.2.1) x)
      rw [ht e he' x hx.1,←he,hs d hd _ hx.2,translate_add]
    · intro x
      obtain ⟨e,he,hx⟩ := tcover x
      obtain ⟨d,hd,hfx⟩ := hcover (f x)
      have hf := ht e he x hx
      have hmatch : d.source=e.1 := hfx.1.symm.trans (congrArg Prod.fst hf)
      refine ⟨conv (d,e),Finset.mem_image.mpr ⟨(d,e),?_,rfl⟩,hx,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hd,he⟩,hmatch⟩
      · change translate a e.2.1 x∈d.domain.val
        simpa only [hf] using hfx.2

@[simp] theorem postcompose_apply (g : polygonFullGroup a m) (f : PolygonPlacement a m)
    (x : GenericSquare a) : postcompose g f x=g.val (f x) := rfl

noncomputable instance instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup : MulAction (polygonFullGroup a m) (PolygonPlacement a m) where
  smul := postcompose
  one_smul _ := by apply PolygonPlacement.ext; intro _; rfl
  mul_smul _ _ _ := by apply PolygonPlacement.ext; intro _; rfl

@[simp] theorem smul_apply (g : polygonFullGroup a m) (f : PolygonPlacement a m)
    (x : GenericSquare a) : (g • f) x=g.val (f x) := rfl

theorem range_fiber_polygon (f : PolygonPlacement a m) (i : Fin m) :
    {x | (i,x)∈Set.range f}∈polygonAlgebra a := by
  obtain ⟨s,hs,hcover⟩ := f.charts
  have he : {x | (i,x)∈Set.range f}=
      ⋃c∈s.filter (fun c => c.1=i),translation a c.2.1 '' c.2.2.val := by
    ext y
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨c,hc,hxc⟩ := hcover x
      have h := (hs c hc x hxc).symm.trans hx
      exact Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨
        Finset.mem_filter.mpr ⟨hc,congrArg Prod.fst h⟩,
        ⟨x,hxc,congrArg Prod.snd h⟩⟩⟩
    · intro hy
      obtain ⟨c,hc,hy⟩ := Set.mem_iUnion₂.mp hy
      obtain ⟨x,hx,hxy⟩ := hy
      refine ⟨x,?_⟩
      rw [hs c (Finset.mem_filter.mp hc).1 x hx,(Finset.mem_filter.mp hc).2]
      exact Prod.ext rfl hxy
  rw [he]
  apply BooleanSubalgebra.biSup_mem (Finset.finite_toSet _)
  intro chart _
  exact polygon_image_translation _ chart.2.2.property

def Apart (f g : PolygonPlacement a m) : Prop := Disjoint (Set.range f) (Set.range g)

theorem apart_iff (f g : PolygonPlacement a m) : Apart f g ↔ ∀x y,f x≠g y := by
  constructor
  · intro h x y he
    exact Set.disjoint_left.mp h ⟨x,rfl⟩ ⟨y,he.symm⟩
  · intro h
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,rfl⟩ ⟨y,he⟩
    exact h x y he.symm

theorem apart_smul_iff (h : polygonFullGroup a m) (f g : PolygonPlacement a m) :
    Apart (h • f) (h • g) ↔ Apart f g := by
  simp only [apart_iff,smul_apply,h.val.injective.ne_iff]

theorem standard_apart {i j : Fin m} (hij : i≠j) :
    Apart (standard (a:=a) i) (standard j) := by
  rw [apart_iff]
  intro _ _ equality
  exact hij (congrArg Prod.fst equality)

noncomputable def bank {n : ℕ} (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) : TrackPoint a n ↪ TrackPoint a m where
  toFun x := f x.1 x.2
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ he
    have hij : i=j := by
      by_contra hn
      exact (apart_iff _ _).mp (hf hn) x y he
    subst j
    exact Prod.ext rfl ((f i).toEmbedding.injective he)

end PolygonPlacement
end PolygonConfigurations

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonPlacementArea
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonPlacementArea

open Classical Set
namespace PolygonArea

@[simp] theorem val_finset_sup {a : ℕ} {ι : Type*} (s : Finset ι) (f : ι → polygonAlgebra a) :
    (s.sup f).val=⋃i∈s,(f i).val := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sup_insert,BooleanSubalgebra.val_sup,ih]

end PolygonArea
namespace PolygonPlacement

noncomputable def imageBank {a m : ℕ} (f : PolygonPlacement a m) (i : Fin m) : polygonAlgebra a :=
  ⟨{x | (i,x)∈Set.range f},range_fiber_polygon f i⟩

end PolygonPlacement
end PolygonPlacementArea

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonPlacementPermutation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonPlacementPermutation

open Classical Set
namespace PolygonPlacement
variable {a m n : ℕ} (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))

noncomputable def perm (σ : Equiv.Perm (Fin n)) : Equiv.Perm (TrackPoint a m) :=
  Equiv.Perm.viaEmbedding (Equiv.prodCongr σ (Equiv.refl _)) (bank f hf)

@[simp] theorem perm_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) (x : GenericSquare a) :
    perm f hf σ (f i x)=f (σ i) x :=
  Equiv.Perm.viaEmbedding_apply _ _ (i,x)

theorem perm_fixed (σ : Equiv.Perm (Fin n)) (p : TrackPoint a m)
    (hp : ∀i,p∉Set.range (f i)) : perm f hf σ p=p := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨⟨i,x⟩,hi⟩
  exact hp i ⟨x,hi⟩

theorem perm_hasTable (σ : Equiv.Perm (Fin n)) : HasTranslationTable (perm f hf σ) := by
  let s (i : Fin n) := (f i).charts.choose
  have hs (i : Fin n) := (f i).charts.choose_spec.1
  have hc (i : Fin n) := (f i).charts.choose_spec.2
  let J := Σi : Fin n, {c // c∈s i} × {d // d∈s (σ i)}
  let chart (j : J) : TableChart a m :=
    ⟨j.2.1.val.1,j.2.2.val.1,j.2.2.val.2.1-j.2.1.val.2.1,
      translatedPolygon j.2.1.val.2.1 (j.2.1.val.2.2 ⊓ j.2.2.val.2.2)⟩
  let V (i : Fin m) : polygonAlgebra a := (Finset.univ.sup (fun j => imageBank (f j) i))ᶜ
  have hV (p : TrackPoint a m) : p.2∈(V p.1).val ↔ ∀i,p∉Set.range (f i) := by
    simp only [V,BooleanSubalgebra.val_compl,PolygonArea.val_finset_sup,
      Set.mem_compl_iff,Set.mem_iUnion,Finset.mem_univ,not_exists,true_implies]
    rfl
  let void (i : Fin m) : TableChart a m := ⟨i,i,0,V i⟩
  refine ⟨Finset.univ.image chart ∪ Finset.univ.image void,?_,?_⟩
  · intro c hc'
    rcases Finset.mem_union.mp hc' with hc'|hc'
    · obtain ⟨j,-,rfl⟩ := Finset.mem_image.mp hc'
      intro y hy
      obtain ⟨x,⟨hx,hd⟩,rfl⟩ := hy
      have hcval := hs j.1 j.2.1.val j.2.1.property x hx
      have hdval := hs (σ j.1) j.2.2.val j.2.2.property x hd
      change perm f hf σ (j.2.1.val.1,translate a j.2.1.val.2.1 x)=
        (j.2.2.val.1,translate a (j.2.2.val.2.1-j.2.1.val.2.1) (translate a j.2.1.val.2.1 x))
      rw [←hcval,perm_apply,hdval,←translate_add,sub_add_cancel]
    · obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hc'
      intro x hx
      change perm f hf σ (i,x)=(i,translate a 0 x)
      rw [translate_zero]
      exact perm_fixed f hf σ (i,x) ((hV (i,x)).mp hx)
  · intro p
    by_cases hp : ∃i,p∈Set.range (f i)
    · obtain ⟨i,x,rfl⟩ := hp
      obtain ⟨c,hcs,hcx⟩ := hc i x
      obtain ⟨d,hds,hdx⟩ := hc (σ i) x
      let j : J := ⟨i,⟨c,hcs⟩,⟨d,hds⟩⟩
      refine ⟨chart j,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩),?_,?_⟩
      · exact congrArg Prod.fst (hs i c hcs x hcx)
      · refine ⟨x,⟨hcx,hdx⟩,?_⟩
        exact (congrArg Prod.snd (hs i c hcs x hcx)).symm
    · exact ⟨void p.1,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.1,Finset.mem_univ _,rfl⟩),
        rfl,(hV p).mpr (by simpa only [not_exists] using hp)⟩

noncomputable def permHom : Equiv.Perm (Fin n) →* polygonFullGroup a m where
  toFun σ := ⟨perm f hf σ,perm_hasTable f hf σ⟩
  map_one' := by
    apply Subtype.ext; apply Equiv.ext
    intro p
    by_cases hp : ∃i,p∈Set.range (f i)
    · obtain ⟨i,x,rfl⟩ := hp
      exact perm_apply f hf 1 i x
    · exact perm_fixed f hf 1 p (by simpa only [not_exists] using hp)
  map_mul' σ ρ := by
    apply Subtype.ext; apply Equiv.ext
    intro p
    change perm f hf (σ*ρ) p=perm f hf σ (perm f hf ρ p)
    by_cases hp : ∃i,p∈Set.range (f i)
    · obtain ⟨i,x,rfl⟩ := hp
      simp only [perm_apply,Equiv.Perm.mul_apply]
    · have h : ∀i,p∉Set.range (f i) := by simpa only [not_exists] using hp
      rw [perm_fixed f hf _ p h,perm_fixed f hf _ p h,perm_fixed f hf _ p h]

@[simp] theorem permHom_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) (x : GenericSquare a) :
    (permHom f hf σ).val (f i x)=f (σ i) x := perm_apply f hf σ i x

end PolygonPlacement
end PolygonPlacementPermutation

section PolygonConfigurationTransitive

open Classical Set
namespace PolygonPlacement
variable {a m n : ℕ}

noncomputable def familyPerm {ι : Type*} [Fintype ι] (f : ι → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) (σ : Equiv.Perm ι) : polygonFullGroup a m :=
  let e := Fintype.equivFin ι
  permHom (fun i => f (e.symm i))
    (fun _ _ h => hf (fun he => h (e.symm.injective he)))
    (e.symm.trans (σ.trans e))

@[simp] theorem familyPerm_apply {ι : Type*} [Fintype ι] (f : ι → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) (σ : Equiv.Perm ι)
    (i : ι) (x : GenericSquare a) : (familyPerm f hf σ).val (f i x)=f (σ i) x := by
  let e := Fintype.equivFin ι
  have h := permHom_apply (fun j => f (e.symm j))
    (fun _ _ h => hf (fun he => h (e.symm.injective he)))
    (e.symm.trans (σ.trans e)) (e i) x
  simpa only [familyPerm,e,Equiv.symm_apply_apply,Equiv.trans_apply,Equiv.apply_symm_apply] using h

end PolygonPlacement
end PolygonConfigurationTransitive

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonPlacementAlternating
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonConfigurationOrbit
open Classical Set
namespace PolygonPlacement

def Configuration (a m p : ℕ) :=
  {f : Fin p → PolygonPlacement a m // Pairwise (fun i j => Apart (f i) (f j))}

namespace Configuration
variable {a m p : ℕ}
instance instCoeFunForallFin : CoeFun (Configuration a m p) (fun _ => Fin p → PolygonPlacement a m) := ⟨Subtype.val⟩

@[ext] theorem ext {f g : Configuration a m p} (h : ∀i,f i=g i) : f=g :=
  Subtype.ext (funext h)

noncomputable instance instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup : MulAction (polygonFullGroup a m) (Configuration a m p) where
  smul g f := ⟨fun i => g • f i,fun i j hij => (apart_smul_iff g _ _).mpr (f.property hij)⟩
  one_smul f := by apply ext; intro i; exact one_smul _ _
  mul_smul g h f := by apply ext; intro i; exact mul_smul g h _

@[simp] theorem smul_apply (g : polygonFullGroup a m) (f : Configuration a m p) (i : Fin p) :
    (g • f) i=g • f i := rfl

noncomputable def standard (a p n : ℕ) : Configuration a (p+n) p :=
  ⟨fun i => PolygonPlacement.standard (i.castAdd n),fun i j hij => standard_apart (by
    intro hh
    apply hij
    have hv := congrArg (fun x : Fin (p+n) => x.val) hh
    exact Fin.ext hv)⟩

@[simp] theorem standard_apply (i : Fin p) (x : GenericSquare a) (n : ℕ) :
    standard a p n i x=(i.castAdd n,x) := rfl

end Configuration
end PolygonPlacement
end PolygonConfigurationOrbit

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TransitiveInduction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonConfigurationModule

open Classical _root_.CategoryTheory Finsupp
namespace PolygonPlacement.Configuration
variable {a m p : ℕ}

noncomputable def listEquiv (a m p : ℕ) : Configuration a m p ≃
    {l : List (PolygonPlacement a m) // l.Pairwise Apart ∧ l.length=p} where
  toFun f := ⟨List.ofFn f.val,List.pairwise_ofFn.mpr (fun _ _ h => f.property (ne_of_lt h)),List.length_ofFn⟩
  invFun l := ⟨fun i => l.val.get ⟨i.val,by rw [l.property.2];exact i.isLt⟩,by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h|h
    · exact l.property.1.rel_get_of_lt h
    · exact (l.property.1.rel_get_of_lt h).symm⟩
  left_inv f := by apply ext; intro i; simp
  right_inv l := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [l.property.2]
    · intro i hi hj
      simp

@[simp] theorem listEquiv_apply_val (f : Configuration a m p) :
    (listEquiv a m p f).val=List.ofFn f.val := rfl

noncomputable def chainEquiv (a m p : ℕ) :
    (Configuration a m p →₀ ℤ) ≃ₗ[ℤ] ConfigurationChains.degree (@Apart a m) p :=
  (Finsupp.domLCongr (listEquiv a m p)).trans (ConfigurationChains.simplexModuleEquiv _ p).symm

@[simp] theorem chainEquiv_single_val (f : Configuration a m p) (z : ℤ) :
    (chainEquiv a m p (Finsupp.single f z)).val=Finsupp.single (List.ofFn f.val) z := by
  unfold chainEquiv
  rw [LinearEquiv.trans_apply,Finsupp.domLCongr_single]
  simp [ConfigurationChains.simplexModuleEquiv]
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

end PolygonPlacement.Configuration
end PolygonConfigurationModule

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

namespace ConfigurationChains
variable {V : Type*}

lemma faceSum_ofFn (n : ℕ) (f : Fin (n+1) → V) :
    faceSum (List.ofFn f) = ∑i : Fin (n+1),
      Finsupp.single (List.ofFn (fun j => f (i.succAbove j))) ((-1:ℤ)^i.val) := by
  induction n with
  | zero => simp [List.ofFn_succ, faceSum]
  | succ n ih =>
    rw [List.ofFn_succ, faceSum, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, Fin.zero_succAbove,
      map_sum, cone_single]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finsupp.single_neg]
    congr 1
    · simp [List.ofFn_succ]
    · ring

noncomputable def boundaryRep {G : Type*} [Monoid G] [MulAction G V]
    {R : V → V → Prop} (hR : ∀g : G,∀v w,R v w → R (g • v) (g • w)) (n : ℕ) :
    Rep.of (representation hR (n+1)) ⟶ Rep.of (representation hR n) :=
  Rep.ofHom ⟨degreeBoundary R n, by
    intro g
    apply LinearMap.ext
    intro x
    exact (representation_boundary hR g n x).symm⟩
end ConfigurationChains

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedMonoidalTranspose
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.IntervalBar.Diagram.reindex_map_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.posReindex_inclusion_monoidal _root_.OAI.RestrictedNerve.stringEvaluationBraided _root_.OAI.RestrictedNerve.stringEvaluationMonoidal _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.RestrictedNerve.triplePosInclusionEquivalence _root_.OAI.RestrictedNerve.tripleTransposeEquivalence _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I : Type} [Preorder I]

lemma transpose_reindex_p1 {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    Diagram.map (I:=I) (reindex W u) ⋙ transposeDiagram W n =
      transposeDiagram W m ⋙ reindex (diagramProperty W I) u := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · apply WideSubcategory.ext
    refine CategoryTheory.Functor.ext (fun t => stringVertex_reindex W u A t) ?_
    intro t s g
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_vertex_app, eqToHom_vertex_app]
    change (A.obj i j h).obj.map (u.map g) =
      𝟙 _ ≫ (A.obj i j h).obj.map (u.map g) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · intro A B g
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    erw [transposed_comp_app, transposed_comp_app,
      eqToHom_transposed_app, eqToHom_transposed_app]
    change (g.app i j h).hom.app (u.obj t) =
      𝟙 _ ≫ (g.app i j h).hom.app (u.obj t) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

noncomputable def diagramTranspose : diagramHorizontal (I:=I) W ⟶ horizontal (diagramProperty W I) where
  app p := (transposeDiagram W p.unop.len).toCatHom
  naturality p q f := by
    apply Cat.ext
    exact transpose_reindex_p1 W f.unop.toOrderHom.toFunctor

end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedTripleMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.IntervalBar.Diagram.reindex_map_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.posReindex_inclusion_monoidal _root_.OAI.RestrictedNerve.stringEvaluationBraided _root_.OAI.RestrictedNerve.stringEvaluationMonoidal _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.RestrictedNerve.triplePosInclusionEquivalence _root_.OAI.RestrictedNerve.tripleTransposeEquivalence _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K : Type} [Preorder I] [Preorder J] [Preorder K]

lemma map₂_strings_reindex_id (n:ℕ) :
    Diagram.map (I:=J) (Diagram.map (I:=I) (reindex W (𝟭 (Fin (n+1)))))=𝟭 _ := by
  have he (A : Diagram (Strings W n) I) :
      Diagram.mapObj (reindex W (𝟭 (Fin (n+1)))) A=A :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_id W n)
  have he₂ (A : Diagram (Diagram (Strings W n) I) J) :
      (Diagram.map (Diagram.map (reindex W (𝟭 (Fin (n+1)))))).obj A=A := by
    refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he _
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₂_reindex_unit_app]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      intro l m h
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₂_reindex_cut_app]
      rfl
  refine CategoryTheory.Functor.hext he₂ ?_
  intro A B f
  apply hom_hext (he₂ A) (he₂ B)
  intro i j h
  apply hom_hext (he _) (he _)
  intro l m hlm
  apply heq_of_eq
  apply WideSubcategory.hom_ext; rfl
lemma map₂_strings_reindex_comp {n m k:ℕ} (u:Fin (n+1) ⥤ Fin (m+1)) (v:Fin (m+1) ⥤ Fin (k+1)) :
    Diagram.map (I:=J) (Diagram.map (I:=I) (reindex W (u⋙v))) =
      Diagram.map (Diagram.map (reindex W v)) ⋙ Diagram.map (Diagram.map (reindex W u)) := by
  have he (A : Diagram (Strings W k) I) :
      Diagram.mapObj (reindex W (u⋙v)) A =
        Diagram.mapObj (reindex W u) (Diagram.mapObj (reindex W v) A) :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_comp W u v)
  have he₂ (A : Diagram (Diagram (Strings W k) I) J) :
      (Diagram.map (Diagram.map (reindex W (u⋙v)))).obj A=
        (Diagram.map (Diagram.map (reindex W u))).obj ((Diagram.map (Diagram.map (reindex W v))).obj A) := by
    refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he _
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₂_reindex_unit_app, map₂_reindex_unit_app, map₂_reindex_unit_app]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      intro l m h
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₂_reindex_cut_app, map₂_reindex_cut_app, map₂_reindex_cut_app]
      rfl
  refine CategoryTheory.Functor.hext he₂ ?_
  intro A B f
  apply hom_hext (he₂ A) (he₂ B)
  intro i j h
  apply hom_hext (he _) (he _)
  intro l m hlm
  apply heq_of_eq
  apply WideSubcategory.hom_ext; rfl
lemma map₃_strings_reindex_id (n q₁ q₂ q₃:ℕ) :
    Diagram.map (I:=(Fin (q₃+1))) (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W (𝟭 (Fin (n+1))))))=𝟭 _ := by
  have he (A : Diagram (Strings W n) (Fin (q₁+1))) :
      Diagram.mapObj (reindex W (𝟭 (Fin (n+1)))) A=A :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_id W n)
  have he₂ (A : Diagram (Diagram (Strings W n) (Fin (q₁+1))) (Fin (q₂+1))) :
      (Diagram.map (Diagram.map (reindex W (𝟭 (Fin (n+1)))))).obj A=A :=
    congrArg (fun F=>F.obj A) (map₂_strings_reindex_id W n)
  have he₃ (A : Diagram (Diagram (Diagram (Strings W n) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) :
      (Diagram.map (Diagram.map (Diagram.map (reindex W (𝟭 (Fin (n+1))))))).obj A=A := by
    refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he₂ _
    · apply hfunext; intro i
      apply iso_hext (he₂ _) rfl
      apply hom_hext (he₂ _) rfl
      intro j k h
      apply hom_hext (he _) rfl
      intro l m hlm
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₃_reindex_unit_app W]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he₂ _) (he₂ _)) (he₂ _)
      apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he₂ _) (he₂ _)) (he₂ _)
      intro l m h
      apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      intro v w hvw
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₃_reindex_cut_app W]
      rfl
  refine CategoryTheory.Functor.hext he₃ ?_
  intro A B f
  apply hom_hext (he₃ A) (he₃ B)
  intro i j h
  apply hom_hext (he₂ _) (he₂ _)
  intro l m hlm
  apply hom_hext (he _) (he _)
  intro v w hvw
  apply heq_of_eq
  apply WideSubcategory.hom_ext; rfl

lemma map₃_strings_reindex_comp_obj (q₁ q₂ q₃ : ℕ) {n m k : ℕ}
    (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1))
    (A : Diagram (Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) :
      (Diagram.map (Diagram.map (Diagram.map (reindex W (u⋙v))))).obj A=
        (Diagram.map (Diagram.map (Diagram.map (reindex W u)))).obj
          ((Diagram.map (Diagram.map (Diagram.map (reindex W v)))).obj A) := by
  have he (A : Diagram (Strings W k) (Fin (q₁+1))) :
      Diagram.mapObj (reindex W (u⋙v)) A =
        Diagram.mapObj (reindex W u) (Diagram.mapObj (reindex W v) A) :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_comp W u v)
  have he₂ (A : Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) :
      (Diagram.map (Diagram.map (reindex W (u⋙v)))).obj A=
        (Diagram.map (Diagram.map (reindex W u))).obj ((Diagram.map (Diagram.map (reindex W v))).obj A) :=
    congrArg (fun F=>F.obj A) (map₂_strings_reindex_comp W u v)
  refine ext_heq ?_ ?_ ?_
  · funext i j h; exact he₂ _
  · apply hfunext; intro i
    apply iso_hext (he₂ _) rfl
    apply hom_hext (he₂ _) rfl
    intro j k h
    apply hom_hext (he _) rfl
    intro l m hlm
    apply heq_of_eq
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    erw [map₃_reindex_unit_app W, map₃_reindex_unit_app W, map₃_reindex_unit_app W]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro k
    apply hfunext; intro hij
    apply hfunext; intro hjk
    apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he₂ _) (he₂ _)) (he₂ _)
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he₂ _) (he₂ _)) (he₂ _)
    intro l m h
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    intro first last ordered
    apply heq_of_eq
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    exact map₃_reindex_comp_cut_app W q₁ q₂ q₃ u v A i j k hij hjk l m h first last ordered t

lemma map₃_strings_reindex_comp (q₁ q₂ q₃:ℕ) {n m k:ℕ} (u:Fin (n+1) ⥤ Fin (m+1)) (v:Fin (m+1) ⥤ Fin (k+1)) :
    Diagram.map (I:=(Fin (q₃+1))) (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W (u⋙v)))) =
      Diagram.map (Diagram.map (Diagram.map (reindex W v))) ⋙ Diagram.map (Diagram.map (Diagram.map (reindex W u))) := by
  have he (A : Diagram (Strings W k) (Fin (q₁+1))) :
      Diagram.mapObj (reindex W (u⋙v)) A =
        Diagram.mapObj (reindex W u) (Diagram.mapObj (reindex W v) A) :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_comp W u v)
  have he₂ (A : Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) :
      (Diagram.map (Diagram.map (reindex W (u⋙v)))).obj A=
        (Diagram.map (Diagram.map (reindex W u))).obj ((Diagram.map (Diagram.map (reindex W v))).obj A) :=
    congrArg (fun F=>F.obj A) (map₂_strings_reindex_comp W u v)
  have he₃ (A : Diagram (Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) :
      (Diagram.map (Diagram.map (Diagram.map (reindex W (u⋙v))))).obj A=
        (Diagram.map (Diagram.map (Diagram.map (reindex W u)))).obj
          ((Diagram.map (Diagram.map (Diagram.map (reindex W v)))).obj A) :=
    map₃_strings_reindex_comp_obj W q₁ q₂ q₃ u v A
  refine CategoryTheory.Functor.hext he₃ ?_
  intro A B f
  apply hom_hext (he₃ A) (he₃ B)
  intro i j h
  apply hom_hext (he₂ _) (he₂ _)
  intro l m hlm
  apply hom_hext (he _) (he _)
  intro v w hvw
  apply heq_of_eq
  apply WideSubcategory.hom_ext; rfl
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedTripleDegree
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.IntervalBar.Diagram.reindex_map_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.posReindex_inclusion_monoidal _root_.OAI.RestrictedNerve.stringEvaluationBraided _root_.OAI.RestrictedNerve.stringEvaluationMonoidal _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable def tripleDiagramHorizontal (p q r:ℕ) : SimplicialObject Cat.{0,0} where
  obj n := Cat.of (Diagram (Diagram (Diagram (Strings W n.unop.len) (Fin (p+1))) (Fin (q+1))) (Fin (r+1)))
  map f := (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1))
    (reindex W f.unop.toOrderHom.toFunctor)))).toCatHom
  map_id n := by apply Cat.ext; exact map₃_strings_reindex_id W n.unop.len p q r
  map_comp f g := by apply Cat.ext; exact map₃_strings_reindex_comp W p q r g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor

end RestrictedNerve

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_MonoidalCongruence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.IntervalBar.Diagram.reindex_map_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.posReindex_inclusion_monoidal _root_.OAI.RestrictedNerve.stringEvaluationBraided _root_.OAI.RestrictedNerve.stringEvaluationMonoidal _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I:Type} [Preorder I]
lemma transpose_reindex {p q:SimplexCategoryᵒᵖ} (f:p⟶q) :
    Diagram.map (I:=I) (reindex W f.unop.toOrderHom.toFunctor) ⋙ transposeDiagram W q.unop.len =
      transposeDiagram W p.unop.len ⋙ reindex (diagramProperty W I) f.unop.toOrderHom.toFunctor :=
  congrArg Cat.Hom.toFunctor ((diagramTranspose (I:=I) W).naturality f)
noncomputable abbrev transposeReindexHom {p q:SimplexCategoryᵒᵖ} (f:p⟶q) :
    transposeReindexLeft (I:=I) W f ⟶ transposeReindexRight (I:=I) W f := (eqToHom (transpose_reindex (I:=I) W f))
lemma transpose_reindex_unit {p q:SimplexCategoryᵒᵖ} (f:p⟶q) :
    Functor.LaxMonoidal.ε (transposeReindexLeft (I:=I) W f) ≫
      (transposeReindexHom (I:=I) W f).app (𝟙_ _) =
    Functor.LaxMonoidal.ε (transposeReindexRight (I:=I) W f) := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  simp only [transposeReindexHom, CategoryTheory.eqToHom_app]
  simp only [Functor.LaxMonoidal.comp_ε,transpose_ε,reindex_ε,map_reindex_ε]
  simp [transposeDiagram,transposeDiagramHom,transposeε,
    Diagram.mapεHom,reindex]
  erw [comp_app, comp_app, eqToHom_transposed_app]
  change (𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp only [Category.id_comp]
lemma transposeReindexHom_app {p q:SimplexCategoryᵒᵖ} (f:p⟶q)
    (A:Diagram (Strings W p.unop.len) I)
    (t:Fin (q.unop.len+1)) (i j:I) (h:i≤j) :
    (((transposeReindexHom (I:=I) W f).app A).hom.app t).hom.app i j h =
      𝟙 ((A.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t)) := by
  simp only [transposeReindexHom, CategoryTheory.eqToHom_app]
  erw [eqToHom_transposed_app]
  rfl
lemma transpose_reindex_tensor {p q:SimplexCategoryᵒᵖ} (f:p⟶q)
    (A B:Diagram (Strings W p.unop.len) I) :
    Functor.LaxMonoidal.μ (transposeReindexLeft (I:=I) W f) A B ≫
      (transposeReindexHom (I:=I) W f).app (A ⊗ B) =
    ((transposeReindexHom (I:=I) W f).app A ⊗ₘ
      (transposeReindexHom (I:=I) W f).app B) ≫
    Functor.LaxMonoidal.μ (transposeReindexRight (I:=I) W f) A B := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  erw [transpose_comp_app W (Functor.LaxMonoidal.μ (transposeReindexLeft (I:=I) W f) A B)
      ((transposeReindexHom (I:=I) W f).app (A ⊗ B))]
  erw [transpose_comp_app W
      ((transposeReindexHom (I:=I) W f).app A ⊗ₘ (transposeReindexHom (I:=I) W f).app B)
      (Functor.LaxMonoidal.μ (transposeReindexRight (I:=I) W f) A B)]
  erw [transpose_tensor_app]
  erw [transposeReindexLeft_μ_app, transposeReindexHom_app]
  erw [transposeReindexHom_app W f A, transposeReindexHom_app W f B]
  change (𝟙 ((A.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t) ⊗
      (B.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t))) ≫ 𝟙 _ =
    (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
  simp only [id_tensorHom_id, Category.comp_id]
noncomputable instance transpose_reindex_monoidal {p q:SimplexCategoryᵒᵖ} (f:p⟶q) :
    NatTrans.IsMonoidal (eqToHom (transpose_reindex (I:=I) W f)) where
  unit := transpose_reindex_unit W f
  tensor A B := transpose_reindex_tensor W f A B
end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma tripleTranspose_reindex (p q r:ℕ) {u v:SimplexCategoryᵒᵖ} (f:u⟶v) :
    Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1))
      (reindex W f.unop.toOrderHom.toFunctor))) ⋙ tripleTranspose W p q r v.unop.len =
      tripleTranspose W p q r u.unop.len ⋙ reindex (property₃ W p q r) f.unop.toOrderHom.toFunctor := by
  have h₁ := map₂_congr (I:=Fin (q+1)) (J:=Fin (r+1))
    (transpose_reindex (I:=Fin (p+1)) W f) (transpose_reindex_monoidal W f)
  rw [map₂_comp,map₂_comp] at h₁
  have h₂ := map_congr (I:=Fin (r+1))
    (transpose_reindex (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) f)
      (transpose_reindex_monoidal (diagramProperty W (Fin (p+1))) f)
  rw [Diagram.map_comp,Diagram.map_comp] at h₂
  have h₃ := transpose_reindex (I:=Fin (r+1)) (property₂ W p q) f
  unfold tripleTranspose
  rw [←Functor.assoc,←Functor.assoc,h₁]
  simp only [Functor.assoc]
  rw [←Functor.assoc
    (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
      (reindex (diagramProperty W (Fin (p+1))) f.unop.toOrderHom.toFunctor)))
    (Diagram.map (I:=Fin (r+1)) (transposeDiagram (I:=Fin (q+1))
      (diagramProperty W (Fin (p+1))) v.unop.len))
    (transposeDiagram (I:=Fin (r+1)) (property₂ W p q) v.unop.len),h₂]
  simp only [Functor.assoc]
  rw [h₃]
noncomputable def tripleDiagramTranspose (p q r:ℕ) :
    tripleDiagramHorizontal W p q r ⟶ horizontal (property₃ W p q r) where
  app n := (tripleTranspose W p q r n.unop.len).toCatHom
  naturality u v f := by apply Cat.ext; exact tripleTranspose_reindex W p q r f

noncomputable def tripleDiagramResolutionHomologyIso (p q r j:ℕ) :
    (SimplicialDiagonal.nerveDiagonal.obj (tripleDiagramHorizontal W p q r)).homology
      DiagonalResolution.Z j ≅
    (nerve (Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1)))).homology
      DiagonalResolution.Z j := by
  haveI := SimplicialDiagonal.nerveDiagonal_isIso (tripleDiagramTranspose W p q r)
    (fun n=>inferInstanceAs (tripleTranspose W p q r n.unop.len).IsEquivalence) j
  exact asIso (SSet.homologyMap
    (SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r))
      DiagonalResolution.Z j) ≪≫ tripleRestrictedHomologyIso W p q r j
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedFunctorial
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.IntervalBar.Diagram.reindex_map_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.posReindex_inclusion_monoidal _root_.OAI.RestrictedNerve.stringEvaluationBraided _root_.OAI.RestrictedNerve.stringEvaluationMonoidal _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.RestrictedNerve.transpose_reindex_monoidal _root_.OAI.RestrictedNerve.triplePosInclusionEquivalence _root_.OAI.RestrictedNerve.tripleTransposeEquivalence _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]

lemma transpose_posReindex (u:I→oJ) (n:ℕ) :
    Diagram.reindex (C:=Strings W n) u ⋙ transposeDiagram (I:=I) W n =
      transposeDiagram (I:=J) W n ⋙ stringsMap (diagramProperty W J) (diagramProperty W I)
        (posReindex W u) (posReindex_property W u) n := by
  refine CategoryTheory.Functor.ext (fun A=>?_) ?_
  · apply WideSubcategory.ext
    refine CategoryTheory.Functor.ext (fun i=>rfl) ?_
    intro i j f
    erw [Category.id_comp, Category.comp_id]
    rfl
  · intro A B f
    erw [Category.id_comp, Category.comp_id]
    rfl
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_NestedPosReindex
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindex_inclusion_monoidal _root_.OAI.RestrictedNerve.stringEvaluationBraided _root_.OAI.RestrictedNerve.stringEvaluationMonoidal _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
noncomputable abbrev innerReindexRight (u:I→oJ) (n:ℕ) :=
    Diagram.map (I:=K) (transposeDiagram (I:=J) W n) ⋙
      transposeDiagram (I:=K) (diagramProperty W J) n ⋙
        stringsMap (diagramProperty (diagramProperty W J) K) (diagramProperty (diagramProperty W I) K)
          (nestedPosReindex W u) (nestedPosReindex_property W u) n

lemma doubleTranspose_innerReindex_vertex (u:I→oJ) (n:ℕ)
    (A:Diagram (Diagram (Strings W n) J) K) (t:Fin (n+1)) :
    (((innerReindexLeft (K:=K) W u n).obj A).obj.obj t) =
      (((innerReindexRight (K:=K) W u n).obj A).obj.obj t) := by
  refine ext_heq rfl ?_ ?_
  · apply heq_of_eq; funext i; apply Iso.ext; apply WideSubcategory.hom_ext
    apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
    simp [stringsMap,nestedPosReindex,transposeDiagramObj,stringVertex,mapObj]
    simp [widePosReindex,posReindex,Diagram.reindex]
    erw [comp_app, transpose_η_app]
    change (((A.unit i).hom.app (u x) (u y) (u.monotone h)).hom.app t ≫ 𝟙 _) ≫ 𝟙 _ =
      (((A.unit i).hom.app (u x) (u y) (u.monotone h)).hom.app t ≫
        ((Functor.OplaxMonoidal.η (transposeDiagram (I:=J) W n)).hom.app t).hom.app
          (u x) (u y) (u.monotone h)) ≫ 𝟙 _
    rw [transpose_η_app]
    rfl
  · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext; apply WideSubcategory.hom_ext
    apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
    simp [stringsMap,nestedPosReindex,transposeDiagramObj,stringVertex,mapObj]
    simp [widePosReindex,posReindex,Diagram.reindex]
    change 𝟙 _ ≫ 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app (u x) (u y) (u.monotone h)).hom.app t =
      𝟙 _ ≫ 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app (u x) (u y) (u.monotone h)).hom.app t
    simp

lemma doubleTranspose_innerReindex_obj (u:I→oJ) (n:ℕ)
    (A:Diagram (Diagram (Strings W n) J) K) :
    (innerReindexLeft (K:=K) W u n).obj A = (innerReindexRight (K:=K) W u n).obj A := by
  apply WideSubcategory.ext
  refine CategoryTheory.Functor.ext (doubleTranspose_innerReindex_vertex W u n A) ?_
  intro t s f
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  apply InducedCategory.hom_ext; apply Hom.ext; intro x y hxy
  erw [nested_comp_app, nested_comp_app, nested_eqToHom_app, nested_eqToHom_app]
  change ((A.obj i j h).obj (u x) (u y) (u.monotone hxy)).obj.map f =
    𝟙 _ ≫ ((A.obj i j h).obj (u x) (u y) (u.monotone hxy)).obj.map f ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

lemma doubleTranspose_innerReindex_eq (u:I→oJ) (n:ℕ) :
    innerReindexLeft (K:=K) W u n = innerReindexRight (K:=K) W u n := by
  refine CategoryTheory.Functor.ext (doubleTranspose_innerReindex_obj W u n) ?_
  intro A B f
  apply twiceTransposed_transport_ext
  intro t i j h x y hxy
  change ((f.app i j h).app (u x) (u y) (u.monotone hxy)).hom.app t =
    𝟙 _ ≫ ((f.app i j h).app (u x) (u y) (u.monotone hxy)).hom.app t ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

lemma doubleTranspose_innerReindex (u:I→oJ) (n:ℕ) :
    Diagram.map (I:=K) (Diagram.reindex (C:=Strings W n) u) ⋙
      Diagram.map (I:=K) (transposeDiagram (I:=I) W n) ⋙
        transposeDiagram (I:=K) (diagramProperty W I) n =
    Diagram.map (I:=K) (transposeDiagram (I:=J) W n) ⋙
      transposeDiagram (I:=K) (diagramProperty W J) n ⋙
        stringsMap (diagramProperty (diagramProperty W J) K) (diagramProperty (diagramProperty W I) K)
          (nestedPosReindex W u) (nestedPosReindex_property W u) n := by
  exact doubleTranspose_innerReindex_eq W u n

end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PositionalInclusionMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.stringEvaluationBraided _root_.OAI.RestrictedNerve.stringEvaluationMonoidal _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
open IntervalBar IntervalBar.Diagram


variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
lemma map_posReindex_inclusion (u:I→oJ) :
    Diagram.map (I:=K) (posReindex W u) ⋙ Diagram.map (posDiagramInclusion W I) =
      Diagram.map (posDiagramInclusion W J) ⋙ Diagram.map (Diagram.reindex u) := by
  have he := map_congr (I:=K) (posReindex_inclusion W u) (posReindex_inclusion_monoidal W u)
  simpa only [Diagram.map_comp] using he
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]

noncomputable def tripleOuterReindex (p q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    tripleDiagramHorizontal W p q s ⟶ tripleDiagramHorizontal W p q r where
  app n := (Diagram.reindex (C:=Diagram (Diagram (Strings W n.unop.len)
    (Fin (p+1))) (Fin (q+1))) u).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    exact (Diagram.reindex_map (Diagram.map (I:=Fin (q+1))
      (Diagram.map (I:=Fin (p+1)) (reindex W f.unop.toOrderHom.toFunctor))) u).symm
lemma tripleTranspose_outerReindex (p q n:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    Diagram.reindex (C:=Diagram (Diagram (Strings W n) (Fin (p+1))) (Fin (q+1))) u ⋙
      tripleTranspose W p q r n =
      tripleTranspose W p q s n ⋙ stringsMap (property₃ W p q s) (property₃ W p q r)
        (posReindex (property₂ W p q) u) (posReindex_property (property₂ W p q) u) n := by
  unfold tripleTranspose
  rw [←Functor.assoc,Diagram.reindex_map]
  simp only [Functor.assoc]
  rw [←Functor.assoc (Diagram.reindex u),Diagram.reindex_map]
  simp only [Functor.assoc]
  rw [transpose_posReindex (property₂ W p q) u n]
lemma tripleDiagramTranspose_outerReindex (p q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    tripleOuterReindex W p q u ≫ tripleDiagramTranspose W p q r =
      tripleDiagramTranspose W p q s ≫ horizontalMap (property₃ W p q s) (property₃ W p q r)
        (posReindex (property₂ W p q) u) (posReindex_property (property₂ W p q) u) := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact tripleTranspose_outerReindex W p q n.unop.len u
noncomputable def tripleMiddleReindex (p r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    tripleDiagramHorizontal W p s r ⟶ tripleDiagramHorizontal W p q r where
  app n := (Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram (Strings W n.unop.len)
    (Fin (p+1))) u)).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    exact (Diagram.map_reindex_map (I:=Fin (q+1)) (J:=Fin (s+1)) (K:=Fin (r+1))
      (Diagram.map (I:=Fin (p+1)) (reindex W f.unop.toOrderHom.toFunctor)) u).symm
lemma tripleTranspose_middleReindex (p r n:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram (Strings W n) (Fin (p+1))) u) ⋙
      tripleTranspose W p q r n =
      tripleTranspose W p s r n ⋙ stringsMap (property₃ W p s r) (property₃ W p q r)
        (nestedPosReindex (diagramProperty W (Fin (p+1))) u)
        (nestedPosReindex_property (diagramProperty W (Fin (p+1))) u) n := by
  have he := Diagram.map_reindex_map (K:=Fin (r+1)) (transposeDiagram (I:=Fin (p+1)) W n) u
  unfold tripleTranspose
  rw [←Functor.assoc,←Functor.assoc,he]
  simp only [Functor.assoc]
  rw [doubleTranspose_innerReindex (K:=Fin (r+1)) (diagramProperty W (Fin (p+1))) u n]
lemma tripleDiagramTranspose_middleReindex (p r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    tripleMiddleReindex W p r u ≫ tripleDiagramTranspose W p q r =
      tripleDiagramTranspose W p s r ≫ horizontalMap (property₃ W p s r) (property₃ W p q r)
        (nestedPosReindex (diagramProperty W (Fin (p+1))) u)
        (nestedPosReindex_property (diagramProperty W (Fin (p+1))) u) := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact tripleTranspose_middleReindex W p r n.unop.len u
lemma triplePosInclusion_middleReindex (p r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    nestedPosReindex (diagramProperty W (Fin (p+1))) u ⋙ triplePosInclusion W p q r =
      triplePosInclusion W p s r ⋙ Diagram.map (Diagram.reindex u) := by
  unfold triplePosInclusion
  rw [←Functor.assoc,←Functor.assoc,nestedPosReindex_inclusion]
  simp only [Functor.assoc]
  rw [←Functor.assoc (Diagram.map (posReindex (diagramProperty W (Fin (p+1))) u)),
    map_posReindex_inclusion]
  simp only [Functor.assoc]
  rw [Diagram.map_reindex_map]
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_ResolutionAugmentation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory SimplicialObject Simplicial Opposite

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C) [W.IsMultiplicative]

variable {D:Type} [Groupoid.{0} D] (V:MorphismProperty D) [V.IsMultiplicative]
  (F:C⥤D) (hF:∀{X Y:C} (f:X⟶Y),W f→V (F.map f))
lemma resolutionAugmentation_natural :
    SimplicialDiagonal.nerveDiagonal.map (horizontalMap W V F hF) ≫ resolutionAugmentation V =
      resolutionAugmentation W ≫ nerveMap F := by
  unfold resolutionAugmentation
  rw [←Category.assoc,diagonalIso_natural]
  simp only [Category.assoc]
  rw [verticalAugmentation_natural]
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]

noncomputable def tripleResolutionAugmentation (p q r:ℕ) :
    SimplicialDiagonal.nerveDiagonal.obj (tripleDiagramHorizontal W p q r) ⟶
      nerve (Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1))) :=
  SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r) ≫
    resolutionAugmentation (property₃ W p q r) ≫ nerveMap (triplePosInclusion W p q r)
lemma tripleResolutionAugmentation_outer_natural (p q:ℕ) {r s:ℕ}
    (u:Fin (r+1)→oFin (s+1)) :
    SimplicialDiagonal.nerveDiagonal.map (tripleOuterReindex W p q u) ≫
      tripleResolutionAugmentation W p q r =
      tripleResolutionAugmentation W p q s ≫ nerveMap (Diagram.reindex u) := by
  have ht := congrArg SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose_outerReindex W p q u)
  simp only [Functor.map_comp] at ht
  unfold tripleResolutionAugmentation
  rw [←Category.assoc _ (SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r)),ht]
  simp only [Category.assoc]
  rw [←Category.assoc _ (resolutionAugmentation (property₃ W p q r)),resolutionAugmentation_natural]
  simp only [Category.assoc]
  have he : nerveMap (posReindex (property₂ W p q) u) ≫ nerveMap (triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p q s) ≫ nerveMap (Diagram.reindex u) := by
    change nerveMap (posReindex (property₂ W p q) u ⋙ triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p q s ⋙ Diagram.reindex u)
    rw [triplePosInclusion_outerReindex]
  rw [he]
lemma tripleResolutionAugmentation_middle_natural (p r:ℕ) {q s:ℕ}
    (u:Fin (q+1)→oFin (s+1)) :
    SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W p r u) ≫
      tripleResolutionAugmentation W p q r =
      tripleResolutionAugmentation W p s r ≫ nerveMap (Diagram.map (Diagram.reindex u)) := by
  have ht := congrArg SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose_middleReindex W p r u)
  simp only [Functor.map_comp] at ht
  unfold tripleResolutionAugmentation
  rw [←Category.assoc _ (SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r)),ht]
  simp only [Category.assoc]
  rw [←Category.assoc _ (resolutionAugmentation (property₃ W p q r)),resolutionAugmentation_natural]
  simp only [Category.assoc]
  have he : nerveMap (nestedPosReindex (diagramProperty W (Fin (p+1))) u) ≫ nerveMap (triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p s r) ≫ nerveMap (Diagram.map (Diagram.reindex u)) := by
    change nerveMap (nestedPosReindex (diagramProperty W (Fin (p+1))) u ⋙ triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p s r ⋙ Diagram.map (Diagram.reindex u))
    rw [triplePosInclusion_middleReindex]
  rw [he]
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StringEvaluation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma tripleTranspose_evaluation (p q r:ℕ) {n:ℕ} (t:Fin (n+1)) :
    tripleTranspose W p q r n ⋙ stringEvaluation (property₃ W p q r) t ⋙
      triplePosInclusion W p q r =
    Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
      (Diagram.map (I:=Fin (p+1)) (stringEvaluation W t))) := by
  have h₁ := Diagram.map₂_congr (I:=Fin (q+1)) (J:=Fin (r+1))
    (transpose_evaluation (I:=Fin (p+1)) W t) (transpose_evaluation_monoidal W t)
  simp only [map₂_comp] at h₁
  have h₂ := Diagram.map_congr (I:=Fin (r+1))
    (transpose_evaluation (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) t)
    (transpose_evaluation_monoidal (diagramProperty W (Fin (p+1))) t)
  simp only [Diagram.map_comp] at h₂
  have h₃ := transpose_evaluation (I:=Fin (r+1)) (property₂ W p q) t
  change Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (transposeDiagram (I:=Fin (p+1)) W n)) ⋙
    Diagram.map (I:=Fin (r+1)) (transposeDiagram (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) n) ⋙
    (transposeDiagram (I:=Fin (r+1)) (property₂ W p q) n ⋙ stringEvaluation (property₃ W p q r) t ⋙
      posDiagramInclusion (property₂ W p q) (Fin (r+1))) ⋙
    Diagram.map (I:=Fin (r+1)) (posDiagramInclusion (diagramProperty W (Fin (p+1))) (Fin (q+1))) ⋙
    Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (posDiagramInclusion W (Fin (p+1)))) = _
  rw [h₃]
  change Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (transposeDiagram (I:=Fin (p+1)) W n)) ⋙
    (Diagram.map (I:=Fin (r+1)) (transposeDiagram (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) n) ⋙
      Diagram.map (I:=Fin (r+1)) (stringEvaluation (property₂ W p q) t) ⋙
      Diagram.map (I:=Fin (r+1)) (posDiagramInclusion (diagramProperty W (Fin (p+1))) (Fin (q+1)))) ⋙
    Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (posDiagramInclusion W (Fin (p+1)))) = _
  rw [h₂]
  exact h₁
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]

noncomputable def tripleInnerReindex (q r:ℕ) {p s:ℕ} (u:Fin (p+1)→oFin (s+1)) :
    tripleDiagramHorizontal W s q r ⟶ tripleDiagramHorizontal W p q r where
  app n := (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
    (Diagram.reindex (C:=Strings W n.unop.len) u))).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    have he := Diagram.map₂_congr (I:=Fin (q+1)) (J:=Fin (r+1))
      (Diagram.reindex_map (reindex W f.unop.toOrderHom.toFunctor) u)
      (Diagram.reindex_map_monoidal (reindex W f.unop.toOrderHom.toFunctor) u)
    simp only [map₂_comp] at he
    exact he.symm
lemma tripleResolutionAugmentation_inner_natural (q r:ℕ) {p s:ℕ}
    (u:Fin (p+1)→oFin (s+1)) :
    SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W q r u) ≫
      tripleResolutionAugmentation W p q r =
      tripleResolutionAugmentation W s q r ≫
        nerveMap (Diagram.map (Diagram.map (Diagram.reindex u))) := by
  ext n A
  refine CategoryTheory.Functor.ext (fun i=> ?_) ?_
  · change ((Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
          (Diagram.reindex (C:=Strings W n.unop.len) u)) ⋙
        tripleTranspose W p q r n.unop.len ⋙ stringEvaluation (property₃ W p q r) i ⋙
          triplePosInclusion W p q r).obj (A.obj i)) =
      ((tripleTranspose W s q r n.unop.len ⋙ stringEvaluation (property₃ W s q r) i ⋙
          triplePosInclusion W s q r ⋙ Diagram.map (I:=Fin (r+1))
            (Diagram.map (I:=Fin (q+1)) (Diagram.reindex (C:=C) u))).obj (A.obj i))
    rw [tripleTranspose_evaluation W p q r i]
    change _ = (((tripleTranspose W s q r n.unop.len ⋙ stringEvaluation (property₃ W s q r) i ⋙
          triplePosInclusion W s q r) ⋙ Diagram.map (I:=Fin (r+1))
            (Diagram.map (I:=Fin (q+1)) (Diagram.reindex (C:=C) u))).obj (A.obj i))
    rw [tripleTranspose_evaluation W s q r i]
    exact congrArg (fun F=>F.obj (A.obj i))
      (Diagram.map_map_map_reindex (K:=Fin (q+1)) (L:=Fin (r+1)) (stringEvaluation W i) u).symm
  · intro i j f
    apply Hom.ext; intro a b h
    apply Hom.ext; intro c d k
    apply Hom.ext; intro e g l
    simp only [Diagram.comp_app,Diagram.eqToHom_app]
    erw [Category.id_comp, Category.comp_id]
    rfl
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_Supplemental
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

section
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma tripleInnerReindex_id (p q r:ℕ) :
    tripleInnerReindex W q r (OrderHom.id (α:=Fin (p+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact Diagram.map_map_reindex_id
lemma tripleInnerReindex_comp (q r:ℕ) {p s t:ℕ}
    (u:Fin (p+1)→oFin (s+1)) (v:Fin (s+1)→oFin (t+1)) :
    tripleInnerReindex W q r (v.comp u) =
      tripleInnerReindex W q r v ≫ tripleInnerReindex W q r u := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact Diagram.map_map_reindex_comp u v

noncomputable def innerResolutionRows (q r:ℕ) : SimplicialObject SSet where
  obj p := SimplicialDiagonal.nerveDiagonal.obj (tripleDiagramHorizontal W p.unop.len q r)
  map f := SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W q r f.unop.toOrderHom)
  map_id p := by
    change SimplicialDiagonal.nerveDiagonal.map
      (tripleInnerReindex W q r (OrderHom.id (α:=Fin (p.unop.len+1)))) = _
    rw [tripleInnerReindex_id,CategoryTheory.Functor.map_id]
  map_comp f g := by rw [show (f ≫ g).unop.toOrderHom = f.unop.toOrderHom.comp g.unop.toOrderHom from rfl,
    tripleInnerReindex_comp,Functor.map_comp]

noncomputable def innerResolutionAugmentation (q r:ℕ) :
    innerResolutionRows W q r ⟶ innerNerveRows (C:=C) q r where
  app p := tripleResolutionAugmentation W p.unop.len q r
  naturality _ _ f := tripleResolutionAugmentation_inner_natural W q r f.unop.toOrderHom

lemma tripleInnerMiddle_commute (r:ℕ) {p s q t:ℕ}
    (u:Fin (p+1)→oFin (s+1)) (v:Fin (q+1)→oFin (t+1)) :
    tripleInnerReindex W t r u ≫ tripleMiddleReindex W p r v =
      tripleMiddleReindex W s r v ≫ tripleInnerReindex W q r u := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact Diagram.map_map_reindex (Diagram.reindex u) v
noncomputable def innerRowsMiddle (r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    innerResolutionRows W s r ⟶ innerResolutionRows W q r where
  app p := SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W p.unop.len r u)
  naturality n m f := by
    change SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W s r f.unop.toOrderHom) ≫
      SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W m.unop.len r u) = _
    rw [←Functor.map_comp,tripleInnerMiddle_commute,Functor.map_comp]
    rfl
lemma innerResolutionAugmentation_middle_natural (r:ℕ) {q s:ℕ}
    (u:Fin (q+1)→oFin (s+1)) :
    innerRowsMiddle W r u ≫ innerResolutionAugmentation W q r =
      innerResolutionAugmentation W s r ≫ innerNerveRowsMiddle (C:=C) r u := by
  apply NatTrans.ext; funext p
  exact tripleResolutionAugmentation_middle_natural W p.unop.len r u
lemma innerRowsMiddle_id (q r:ℕ) : innerRowsMiddle W r (OrderHom.id (α:=Fin (q+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext p
  have he : tripleMiddleReindex W p.unop.len r (OrderHom.id (α:=Fin (q+1))) = 𝟙 _ := by
    apply NatTrans.ext; funext n; apply Cat.ext
    exact Diagram.map_reindex_id
  change SimplicialDiagonal.nerveDiagonal.map _ = _
  rw [he,CategoryTheory.Functor.map_id]
  rfl
lemma innerRowsMiddle_comp (r:ℕ) {p q s:ℕ}
    (u:Fin (p+1)→oFin (q+1)) (v:Fin (q+1)→oFin (s+1)) :
    innerRowsMiddle W r (v.comp u) = innerRowsMiddle W r v ≫ innerRowsMiddle W r u := by
  apply NatTrans.ext; funext n
  have he : tripleMiddleReindex W n.unop.len r (v.comp u) =
      tripleMiddleReindex W n.unop.len r v ≫ tripleMiddleReindex W n.unop.len r u := by
    apply NatTrans.ext; funext k; apply Cat.ext
    exact Diagram.map_reindex_comp u v
  change SimplicialDiagonal.nerveDiagonal.map _ = _
  rw [he,Functor.map_comp]
  rfl
noncomputable def middleResolutionRows (r:ℕ) : SimplicialObject SSet where
  obj q := SimplicialDiagonal.diagonal.obj (innerResolutionRows W q.unop.len r)
  map f := SimplicialDiagonal.diagonal.map (innerRowsMiddle W r f.unop.toOrderHom)
  map_id q := by
    change SimplicialDiagonal.diagonal.map (innerRowsMiddle W r (OrderHom.id (α:=Fin (q.unop.len+1)))) = _
    rw [innerRowsMiddle_id,CategoryTheory.Functor.map_id]
  map_comp f g := by
    change SimplicialDiagonal.diagonal.map (innerRowsMiddle W r (f.unop.toOrderHom.comp g.unop.toOrderHom)) = _
    rw [innerRowsMiddle_comp,Functor.map_comp]

noncomputable def middleResolutionAugmentation (r:ℕ) :
    middleResolutionRows W r ⟶ middleNerveRows (C:=C) r where
  app q := SimplicialDiagonal.diagonal.map (innerResolutionAugmentation W q.unop.len r)
  naturality n m f := by
    change SimplicialDiagonal.diagonal.map (innerRowsMiddle W r f.unop.toOrderHom) ≫
      SimplicialDiagonal.diagonal.map (innerResolutionAugmentation W m.unop.len r) = _
    rw [←Functor.map_comp,innerResolutionAugmentation_middle_natural,Functor.map_comp]
    rfl

lemma tripleInnerOuter_commute (q:ℕ) {p s r t:ℕ}
    (u:Fin (p+1)→oFin (s+1)) (v:Fin (r+1)→oFin (t+1)) :
    tripleInnerReindex W q t u ≫ tripleOuterReindex W p q v =
      tripleOuterReindex W s q v ≫ tripleInnerReindex W q r u := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact (Diagram.reindex_map (Diagram.map (Diagram.reindex u)) v).symm
lemma tripleMiddleOuter_commute (p:ℕ) {q s r t:ℕ}
    (u:Fin (q+1)→oFin (s+1)) (v:Fin (r+1)→oFin (t+1)) :
    tripleMiddleReindex W p t u ≫ tripleOuterReindex W p q v =
      tripleOuterReindex W p s v ≫ tripleMiddleReindex W p r u := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact (Diagram.reindex_map (Diagram.reindex u) v).symm
noncomputable def innerRowsOuter (q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    innerResolutionRows W q s ⟶ innerResolutionRows W q r where
  app p := SimplicialDiagonal.nerveDiagonal.map (tripleOuterReindex W p.unop.len q u)
  naturality n m f := by
    change SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W q s f.unop.toOrderHom) ≫
      SimplicialDiagonal.nerveDiagonal.map (tripleOuterReindex W m.unop.len q u) = _
    rw [←Functor.map_comp,tripleInnerOuter_commute,Functor.map_comp]
    rfl
lemma innerResolutionAugmentation_outer_natural (q:ℕ) {r s:ℕ}
    (u:Fin (r+1)→oFin (s+1)) :
    innerRowsOuter W q u ≫ innerResolutionAugmentation W q r =
      innerResolutionAugmentation W q s ≫ innerNerveRowsOuter (C:=C) q u := by
  apply NatTrans.ext; funext p
  exact tripleResolutionAugmentation_outer_natural W p.unop.len q u
lemma innerRowsMiddleOuter_commute {q s r t:ℕ}
    (u:Fin (q+1)→oFin (s+1)) (v:Fin (r+1)→oFin (t+1)) :
    innerRowsMiddle W t u ≫ innerRowsOuter W q v =
      innerRowsOuter W s v ≫ innerRowsMiddle W r u := by
  apply NatTrans.ext; funext p
  change SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W p.unop.len t u) ≫
      SimplicialDiagonal.nerveDiagonal.map (tripleOuterReindex W p.unop.len q v) = _
  rw [←Functor.map_comp,tripleMiddleOuter_commute,Functor.map_comp]
  rfl
noncomputable def middleRowsOuter {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    middleResolutionRows W s ⟶ middleResolutionRows W r where
  app q := SimplicialDiagonal.diagonal.map (innerRowsOuter W q.unop.len u)
  naturality n m f := by
    change SimplicialDiagonal.diagonal.map (innerRowsMiddle W s f.unop.toOrderHom) ≫
      SimplicialDiagonal.diagonal.map (innerRowsOuter W m.unop.len u) = _
    rw [←Functor.map_comp,innerRowsMiddleOuter_commute,Functor.map_comp]
    rfl
lemma middleResolutionAugmentation_outer_natural {r s:ℕ}
    (u:Fin (r+1)→oFin (s+1)) :
    middleRowsOuter W u ≫ middleResolutionAugmentation W r =
      middleResolutionAugmentation W s ≫ middleNerveRowsOuter (C:=C) u := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerRowsOuter W q.unop.len u) ≫
    SimplicialDiagonal.diagonal.map (innerResolutionAugmentation W q.unop.len r) = _
  rw [←Functor.map_comp,innerResolutionAugmentation_outer_natural,Functor.map_comp]
  rfl

lemma innerRowsOuter_id (q r:ℕ) : innerRowsOuter W q (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext p
  have he : tripleOuterReindex W p.unop.len q (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
    apply NatTrans.ext; funext n; apply Cat.ext
    exact Diagram.reindex_id
  change SimplicialDiagonal.nerveDiagonal.map _ = _
  rw [he,CategoryTheory.Functor.map_id]
  rfl
lemma innerRowsOuter_comp (q:ℕ) {p r s:ℕ}
    (u:Fin (p+1)→oFin (r+1)) (v:Fin (r+1)→oFin (s+1)) :
    innerRowsOuter W q (v.comp u) = innerRowsOuter W q v ≫ innerRowsOuter W q u := by
  apply NatTrans.ext; funext n
  have he : tripleOuterReindex W n.unop.len q (v.comp u) =
      tripleOuterReindex W n.unop.len q v ≫ tripleOuterReindex W n.unop.len q u := by
    apply NatTrans.ext; funext k; apply Cat.ext
    exact Diagram.reindex_comp u v
  change SimplicialDiagonal.nerveDiagonal.map _ = _
  rw [he,Functor.map_comp]
  rfl
lemma middleRowsOuter_id (r:ℕ) : middleRowsOuter W (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerRowsOuter W q.unop.len (OrderHom.id (α:=Fin (r+1)))) = _
  rw [innerRowsOuter_id,CategoryTheory.Functor.map_id]
  rfl
lemma middleRowsOuter_comp {p r s:ℕ}
    (u:Fin (p+1)→oFin (r+1)) (v:Fin (r+1)→oFin (s+1)) :
    middleRowsOuter W (v.comp u) = middleRowsOuter W v ≫ middleRowsOuter W u := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerRowsOuter W q.unop.len (v.comp u)) = _
  rw [innerRowsOuter_comp,Functor.map_comp]
  rfl
noncomputable def outerResolutionRows : SimplicialObject SSet where
  obj r := SimplicialDiagonal.diagonal.obj (middleResolutionRows W r.unop.len)
  map f := SimplicialDiagonal.diagonal.map (middleRowsOuter W f.unop.toOrderHom)
  map_id r := by
    change SimplicialDiagonal.diagonal.map (middleRowsOuter W (OrderHom.id (α:=Fin (r.unop.len+1)))) = _
    rw [middleRowsOuter_id,CategoryTheory.Functor.map_id]
  map_comp f g := by
    change SimplicialDiagonal.diagonal.map (middleRowsOuter W (f.unop.toOrderHom.comp g.unop.toOrderHom)) = _
    rw [middleRowsOuter_comp,Functor.map_comp]
noncomputable def outerResolutionAugmentation :
    outerResolutionRows W ⟶ outerNerveRows (C:=C) where
  app r := SimplicialDiagonal.diagonal.map (middleResolutionAugmentation W r.unop.len)
  naturality n m f := by
    change SimplicialDiagonal.diagonal.map (middleRowsOuter W f.unop.toOrderHom) ≫
      SimplicialDiagonal.diagonal.map (middleResolutionAugmentation W m.unop.len) = _
    rw [←Functor.map_comp,middleResolutionAugmentation_outer_natural,Functor.map_comp]
    rfl

end

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [W.IsStableUnderBraiding]
noncomputable def totalStringToBar :
    SimplicialDiagonal.diagonal.obj (outerResolutionRows W) ⟶ bar₃ (C:=C) :=
  SimplicialDiagonal.diagonal.map (outerResolutionAugmentation W) ≫ totalNerveBarIso.hom
end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable def stringBarRows : SimplicialObject SSet where
  obj n := bar₃ (C:=Strings W n.unop.len)
  map f := bar₃Map (reindex W f.unop.toOrderHom.toFunctor)
  map_id n := by
    ext k x
    exact congrArg (fun F => x ⋙ F)
      (map₃_strings_reindex_id W n.unop.len k.unop.len k.unop.len k.unop.len)
  map_comp f g := by
    ext k x
    exact congrArg (fun F => x ⋙ F)
      (map₃_strings_reindex_comp W k.unop.len k.unop.len k.unop.len
        g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor)

noncomputable def stringBarTotalComponent (n:SimplexCategoryᵒᵖ) :
    (SimplicialDiagonal.diagonal.obj (stringBarRows W)).obj n ≅
      (SimplicialDiagonal.diagonal.obj (outerResolutionRows W)).obj n := Iso.refl _
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StringBarNaturality
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

open IntervalBar IntervalBar.Diagram
variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma stringBarTotal_map_apply {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (SimplicialDiagonal.diagonal.obj (stringBarRows W)).obj n) :
    (SimplicialDiagonal.diagonal.obj (stringBarRows W)).map f x =
      f.unop.toOrderHom.toFunctor ⋙ x ⋙
        Diagram.map₃ (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor) (Fin (n.unop.len+1)) ⋙
          diagonalReindex f.unop.toOrderHom := by
  rfl

lemma outerResolutionTotal_map_apply {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (SimplicialDiagonal.diagonal.obj (outerResolutionRows W)).obj n) :
    (SimplicialDiagonal.diagonal.obj (outerResolutionRows W)).map f x =
      f.unop.toOrderHom.toFunctor ⋙ x ⋙
        Diagram.reindex (C:=Diagram (Diagram (Strings W n.unop.len)
          (Fin (n.unop.len+1))) (Fin (n.unop.len+1))) f.unop.toOrderHom ⋙
        Diagram.map (I:=Fin (m.unop.len+1)) (Diagram.reindex
          (C:=Diagram (Strings W n.unop.len) (Fin (n.unop.len+1))) f.unop.toOrderHom) ⋙
        Diagram.map (I:=Fin (m.unop.len+1)) (Diagram.map (I:=Fin (m.unop.len+1))
          (Diagram.reindex (C:=Strings W n.unop.len) f.unop.toOrderHom)) ⋙
          Diagram.map₃ (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor) (Fin (m.unop.len+1)) := by
  rfl

noncomputable def stringBarTotalIso :
    SimplicialDiagonal.diagonal.obj (stringBarRows W) ≅
      SimplicialDiagonal.diagonal.obj (outerResolutionRows W) :=
  NatIso.ofComponents (stringBarTotalComponent W) (by
    intro n m f
    apply ConcreteCategory.hom_ext
    intro x
    change (SimplicialDiagonal.diagonal.obj (stringBarRows W)).map f x =
      (SimplicialDiagonal.diagonal.obj (outerResolutionRows W)).map f x
    erw [stringBarTotal_map_apply, outerResolutionTotal_map_apply]
    have h := map₃_diagonalReindex (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor)
      f.unop.toOrderHom
    conv_rhs at h => rw [← reverseDiagonalReindex]
    exact congrArg (fun F => f.unop.toOrderHom.toFunctor ⋙ x ⋙ F) h)
noncomputable def stringBarAugmentation :
    SimplicialDiagonal.diagonal.obj (stringBarRows W) ⟶ bar₃ (C:=C) :=
  (stringBarTotalIso W).hom ≫ totalStringToBar W
end RestrictedNerve

end OAI
end



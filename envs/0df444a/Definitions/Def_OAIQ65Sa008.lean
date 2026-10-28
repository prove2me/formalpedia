-- Prove2me | Definitions.Def_OAIQ65Sa008
-- name    : OAIQ65Sa008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:55:11.396009+00:00
-- url     : https://prove2.me/theorems/1b8c9dc1-ca71-4735-a786-c34a8d431260
-- title:
--   Definitions bundle OAIQ65Sa008 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 465 declarations of OpenAI's Lean: 171 definitions, 6 inductive types or structures, 49 instances and 239 theorems. The definitions and types are `OAI.SimpleAmenable.InitialCoverSystem.gridInput`, `OAI.SimpleAmenable.InitialCoverSystem.gridPiece`, `OAI.SimpleAmenable.InitialCoverSystem.marginFamily`, `OAI.SimpleAmenable.InitialCoverSystem.pairCarrierConstant`, `OAI.SimpleAmenable.OldStripPair.firstCenter`, `OAI.SimpleAmenable.PlaneCornerIndex`, `OAI.SimpleAmenable.PlaneStep.representation`, `OAI.SimpleAmenable.PolygonGroupRing`, `OAI.SimpleAmenable.PolygonObject.BooleanPartition`, `OAI.SimpleAmenable.PolygonObject.BooleanPartition.Refines`, `OAI.SimpleAmenable.PolygonObject.BooleanPartition.cell`, `OAI.SimpleAmenable.PolygonObject.BooleanPartition.generated`, `OAI.SimpleAmenable.PolygonObject.BooleanPartition.join`, `OAI.SimpleAmenable.PolygonObject.BooleanPartition.point`, `OAI.SimpleAmenable.PolygonObject.BooleanPartition.signature`, `OAI.SimpleAmenable.PolygonObject.BooleanStep`, `OAI.SimpleAmenable.PolygonObject.BooleanStep.evaluate`, `OAI.SimpleAmenable.PolygonObject.BooleanStep.finiteTensorEquiv`, `OAI.SimpleAmenable.PolygonObject.BooleanStep.inflate`, `OAI.SimpleAmenable.PolygonObject.BooleanStep.multiply`, `OAI.SimpleAmenable.PolygonObject.BooleanStep.refinement`, `OAI.SimpleAmenable.PolygonObject.BooleanStep.tensorEquiv`, `OAI.SimpleAmenable.PolygonObject.BooleanStep.tensorInflate`, `OAI.SimpleAmenable.PolygonObject.BooleanStep.tensorMap`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.assoc`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.empty`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctor`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.left`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.right`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.sum`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.sumEquiv`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.sumHom`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.swap`, `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.toEquiv`, `OAI.SimpleAmenable.PolygonObject.Labelled`, `OAI.SimpleAmenable.PolygonObject.Labelled.ArrowUniform`, `OAI.SimpleAmenable.PolygonObject.Labelled.Cell.arrow`, `OAI.SimpleAmenable.PolygonObject.Labelled.Cell.functor`, `OAI.SimpleAmenable.PolygonObject.Labelled.Cell.object`, `OAI.SimpleAmenable.PolygonObject.Labelled.Cell.pointMap` and 137 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Arithmetic_LatticeRange`, `SimpleAmenable_CentralCovers_CoordinateFamilyCompare`, `SimpleAmenable_CentralCovers_FiniteSlotRefinement`, `SimpleAmenable_CentralCovers_FormalCoordinates`, `SimpleAmenable_CentralCovers_FullAlphabetGeneration`, `SimpleAmenable_CentralCovers_FullSectorCompatibility`, `SimpleAmenable_CentralCovers_GrowthAxisUniform`, `SimpleAmenable_CentralCovers_IndividualGridSplits`, `SimpleAmenable_CentralCovers_InitialCoverSystem`, `SimpleAmenable_CentralCovers_PrimitiveCopies`, `SimpleAmenable_CentralCovers_PrivateBankFixer`, `SimpleAmenable_CentralCovers_TemplateRelators`, `SimpleAmenable_Configurations_BooleanStages`, `SimpleAmenable_Configurations_CellFunctor`, `SimpleAmenable_Configurations_CellRelabel`, `SimpleAmenable_Configurations_DistinctSlotStars`, `SimpleAmenable_Configurations_EmptyStage`, `SimpleAmenable_Configurations_LabelTranslation`, `SimpleAmenable_Configurations_PointFiberEvaluation`, `SimpleAmenable_Configurations_PolygonStrandReconstruction`, `SimpleAmenable_Configurations_PolygonStringNormalization`, `SimpleAmenable_Configurations_PolygonTrackArea`, `SimpleAmenable_Configurations_PolygonTrajectoryStrata`, `SimpleAmenable_Configurations_StageEvaluationEquiv`, `SimpleAmenable_Configurations_StageFiberSum`, `SimpleAmenable_Configurations_StageIteratedMaps2`, `SimpleAmenable_Configurations_StageOrder`, `SimpleAmenable_Configurations_StageRealization`, `SimpleAmenable_Configurations_SymmetricCharts`, `SimpleAmenable_Configurations_TrajectoryLabels`, `SimpleAmenable_Configurations_TrajectoryStages`, `SimpleAmenable_Homology_BooleanStepCoefficients`, `SimpleAmenable_Homology_FilteredHomology`, `SimpleAmenable_Homology_LabelRelabel`, `SimpleAmenable_Homology_StageCoefficients`, `SimpleAmenable_Homology_StageHomologyCoordinates`, `SimpleAmenable_PolygonGeometry_ConcurrentGeometry`, `SimpleAmenable_PolygonGeometry_CoordinateWindowTarget`, `SimpleAmenable_PolygonGeometry_PeriodicSlotStars`, `SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates`, `SimpleAmenable_PolygonGeometry_PlaneStepFunctions`, `SimpleAmenable_PolygonGeometry_PolygonArea`, `SimpleAmenable_PolygonGeometry_PolygonAreaAlgebra`, `SimpleAmenable_PolygonGeometry_PolygonDiagramRefinement`, `SimpleAmenable_PolygonGeometry_PolygonGridEmbedding`, `SimpleAmenable_PolygonGeometry_SectorOffsetCoherence`, `SimpleAmenable_PolygonGeometry_WindowCellPartition`, `SimpleAmenable_PolygonGeometry_WindowIntervals`, `SimpleAmenable_Simplicial_CellMonoidal`, `SimpleAmenable_Simplicial_FiniteSetMonoidal`, `SimpleAmenable_Simplicial_LabelledMonoidal`, `SimpleAmenable_Simplicial_PointFiberMonoidal`, `SimpleAmenable_Simplicial_PowerDiagonal`, `SimpleAmenable_Simplicial_StageMonoidal`, `SimpleAmenable_Simplicial_StageNerveColimit`, `SimpleAmenable_Simplicial_StageSimplicialColimit`, `SimpleAmenable_Simplicial_StageTripleHomology`, `SimpleAmenable_Simplicial_UniformMonoidal`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa004`, `OAIQ65Sa005` and `OAIQ65Sa006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa010` and `OAIQ65Sa011`; the statement `OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa004
import Definitions.Def_OAIQ65Sa005
import Definitions.Def_OAIQ65Sa006

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_LatticeRange
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section SourceLatticeRange

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

theorem sourceLatticeFullMap_translation (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    ∃ d, sourceLatticeFullMap a r m hm k = trackTranslation d := by
  change ∃ d, sourceLatticeFullMap a r m hm
    (Multiplicative.ofAdd (Multiplicative.toAdd k)) = trackTranslation d
  induction Multiplicative.toAdd k using FreeAbelianGroup.induction_on with
  | zero => refine ⟨0,?_⟩; exact (map_one _).trans trackTranslation_zero.symm
  | of i => exact ⟨_,sourceLatticeFullMap_of a r m hm i⟩
  | neg i hi =>
      obtain ⟨d,hd⟩ := hi
      refine ⟨-d,?_⟩
      change sourceLatticeFullMap a r m hm
        ((Multiplicative.ofAdd (FreeAbelianGroup.of i))⁻¹) = _
      rw [map_inv,hd,trackTranslation_neg]
  | add x y hx hy =>
      obtain ⟨d,hd⟩ := hx
      obtain ⟨e,he⟩ := hy
      refine ⟨d+e,?_⟩
      change sourceLatticeFullMap a r m hm
        (Multiplicative.ofAdd x * Multiplicative.ofAdd y) = _
      rw [map_mul,hd,he,trackTranslation_add]

end SourceLatticeRange

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_InitialCoverSystem
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section InitialCoverSystem

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem initialTable_constant :
    B.initialTable.comp (polygonTableInput (initialTest a r) 0) = B.c := by
  apply alternating_hom_ext_small
  intro s hs
  change B.initialTable (polygonTableInput (initialTest a r) 0 s) = B.c s
  exact (B.initialTable_input (0,⟨s.val,s.property,hs⟩)).trans
    (B.c_base ⟨s.val,s.property,hs⟩).symm

end InitialCoverSystem
end InitialCoverSystem

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveCopies
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PrimitiveCopies

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem initialConditional_zero : B.initialConditional 0 = B.c :=
  B.initialTable_constant

end InitialCoverSystem
end PrimitiveCopies

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CoordinateWindowTarget
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section CoordinateWindowTarget

theorem coordinatePrimitive_translate_eq {a : ℕ} (j : Fin 2)
    (u v : CutRing × CutRing) (h : (if j = 0 then u.1 else u.2) =
      (if j = 0 then v.1 else v.2)) :
    spatialTranslate u (coordinatePrimitive a j) = spatialTranslate v (coordinatePrimitive a j) := by
  apply Subtype.ext
  ext p
  fin_cases j
  · change u.1 = v.1 at h
    simp [spatialTranslate,coordinatePrimitive,halfPlane,cutForm,translate_val,h]
  · change u.2 = v.2 at h
    simp [spatialTranslate,coordinatePrimitive,halfPlane,cutForm,translate_val,h]

end CoordinateWindowTarget

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowIntervals
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section EnlargedControl

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]

theorem initialAlphabet_zero (I : Finset (Fin (m+1))) :
    B.initialAlphabet I 0 = B.c.comp (subtypeAlternatingHom I) := by
  rw [initialAlphabet,B.initialConditional_zero]

end InitialCoverSystem
end EnlargedControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullAlphabetGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section FullPrimitiveSectors

variable {α ι Ω : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

omit [Finite ι] in
theorem constant_range_full (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) :
    B.c.range ≤ (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  rw [MonoidHom.range_eq_map,← five_alphabet_generate (by simpa using (by omega : 5 ≤ m+1)),
    Subgroup.map_iSup]
  apply iSup_le
  intro I
  rw [← MonoidHom.range_comp]
  rintro x ⟨s,rfl⟩
  refine ⟨FreeGroup.of ⟨I,none,s⟩,?_⟩
  rw [smallFamilyEval_of]
  change B.initialAlphabet I.val 0 s = B.c (subtypeAlternatingHom I.val s)
  rw [B.initialAlphabet_zero]
  rfl

end InitialCoverSystem
end FullPrimitiveSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullSectorCompatibility
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FullSectorCompatibility
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_whole (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    B.fullGeometricSector hlarge P h (wholePolygon a) =
      B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))) := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range
    (B.fullPrimitiveFamily_central hlarge P h)
  · rintro x ⟨s,rfl⟩
    exact B.fullGeometricSector_mem hlarge P h _ s
  · rintro x ⟨s,rfl⟩
    exact B.constant_range_full hlarge P ⟨universalProjection _ s,rfl⟩
  · rw [B.fullGeometricSector_projection hlarge P h _
      (show ResolvedBy _ (wholePolygon a).val from fun x y he => Iff.rfl),
      ← MonoidHom.comp_assoc,B.c_projection]

end InitialCoverSystem
end FullSectorCompatibility

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorOffsetCoherence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section SectorOffsetCoherence

theorem spatialTranslate_reduce {a : ℕ} (u : CutRing × CutRing) (V : polygonAlgebra a) :
    spatialTranslate u V = spatialTranslate
      ((u.1.im:CutRing)*cutTau,(u.2.im:CutRing)*cutTau) V := by
  apply Subtype.ext
  ext p
  change (translation a u).symm p ∈ V.val ↔
    (translation a ((u.1.im:CutRing)*cutTau,(u.2.im:CutRing)*cutTau)).symm p ∈ V.val
  rw [translation_reduce a u]

theorem coordinatePrimitive_translate_label_eq {a : ℕ} (j : Fin 2)
    (u v : CutRing × CutRing)
    (h : endpointLabel (if j = 0 then u.1 else u.2) =
      endpointLabel (if j = 0 then v.1 else v.2)) :
    spatialTranslate u (coordinatePrimitive a j) = spatialTranslate v (coordinatePrimitive a j) := by
  rw [spatialTranslate_reduce u,spatialTranslate_reduce v]
  apply coordinatePrimitive_translate_eq j
  fin_cases j
  · change u.1.im = v.1.im at h
    change (u.1.im:CutRing)*cutTau = (v.1.im:CutRing)*cutTau
    exact congrArg (fun z : ℤ => (z:CutRing)*cutTau) h
  · change u.2.im = v.2.im at h
    change (u.2.im:CutRing)*cutTau = (v.2.im:CutRing)*cutTau
    exact congrArg (fun z : ℤ => (z:CutRing)*cutTau) h

end SectorOffsetCoherence

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CoordinateFamilyCompare
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section CoordinateFamilyCompare

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

omit [Finite ι] [Finite κ] [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in

theorem coordinateFamily_window_reindex (n : ℕ) (q : Fin 2 → ℤ)
    (j : ι → Fin 2) (u : ι → CutRing × CutRing)
    (hs : ∀ i, q (j i) ≤ endpointLabel (if j i = 0 then (u i).1 else (u i).2))
    (he : ∀ i, endpointLabel (if j i = 0 then (u i).1 else (u i).2) < q (j i)+(n-1:ℕ)) :
    ∃ v : ι → Fin 2 × Fin (n-1),
      (∀ i, (coordinateWindowPrimitives n q (v i)).1 = coordinateTestIndex (j i)) ∧
      ∀ i, spatialTranslate (coordinateWindowPrimitives n q (v i)).2
          (initialTest a r (coordinateWindowPrimitives n q (v i)).1) =
        spatialTranslate (u i) (initialTest a r (coordinateTestIndex (j i))) := by
  let k (i : ι) := (endpointLabel (if j i = 0 then (u i).1 else (u i).2)-q (j i)).toNat
  have hk (i : ι) : (k i:ℤ) = endpointLabel (if j i = 0 then (u i).1 else (u i).2)-q (j i) :=
    Int.toNat_of_nonneg (by have hh := hs i; omega)
  have hk' (i : ι) : k i < n-1 := by have hh := he i; have hh' := hk i; omega
  refine ⟨fun i => (j i,⟨k i,hk' i⟩),fun _ => rfl,?_⟩
  intro i
  simp only [coordinateWindowPrimitives,initialTest_coordinate]
  apply coordinatePrimitive_translate_label_eq
  have hz : endpointLabel (((q (j i)+(k i:ℤ)):CutRing)*cutTau) =
      endpointLabel (if j i = 0 then (u i).1 else (u i).2) := by
    simp [endpointLabel,cutTau]
    have hh := hk i
    change (k i:ℤ) = (if j i = 0 then (u i).1 else (u i).2).im-q (j i) at hh
    omega
  by_cases hji : j i = 0 <;> simpa [coordinateShift,hji] using hz

end InitialCoverSystem
end CoordinateFamilyCompare

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricCharts
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section SymmetricCharts

def symmetricWindowStart (s : CutRing) : Fin 2 → ℤ := fun _ => -(endpointLabel s).natAbs

end SymmetricCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowCellPartition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section SeparatedOldRectangles

namespace OldStripPair
variable {n : ℕ} {d : Fin 2} (P : OldStripPair n d)

noncomputable def firstCenter : CutRing × CutRing := orientedPoint d P.cutLeft P.bottom

end OldStripPair

end SeparatedOldRectangles

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GrowthAxisUniform
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]

omit [Finite ι] [Finite κ] in

theorem smallPrimitive_range_reindex (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (v : κ → ι) :
    (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).range ≤
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  rw [smallFamilyEval_range,smallFamilyEval_range]
  apply iSup_le
  intro I
  apply iSup_le
  intro j
  have he : B.smallPrimitiveInputs hlarge (P ∘ v) I j =
      B.smallPrimitiveInputs hlarge P I (j.map v) := by cases j <;> rfl
  rw [he]
  exact (le_iSup (fun j => (B.smallPrimitiveInputs hlarge P I j).range) (j.map v)).trans
    (le_iSup (fun I => ⨆ j, (B.smallPrimitiveInputs hlarge P I j).range) I)

end InitialCoverSystem
end PairSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_TemplateRelators
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section ActualTemplateRelators

theorem sourceAlignedGroup_mono {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)) :
    Monotone (sourceAlignedGroup a r m hm M t) := by
  intro I J hIJ
  apply Subgroup.closure_mono
  rintro y ⟨b,hb,u,rfl⟩
  exact ⟨b,hb.trans hIJ,u,rfl⟩

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

noncomputable def marginFamily (U : ι → polygonAlgebra a) (V : polygonAlgebra a) :
    Option ι → polygonAlgebra a
  | none => V
  | some i => V ⊓ U i

end InitialCoverSystem
end ActualTemplateRelators

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
variable {a m M : ℕ}
  {r : CutRing}
  {hm : 2 ≤ m}
  (B : InitialCoverSystem a r m hm M)
  {ι : Type*}
  [Fintype ι]
  [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
  (hlarge : 15 < m+1)
  (P : ι → Fin 5 × (CutRing × CutRing))

noncomputable def pairCarrierConstant : alternatingGroup (Fin (m+1)) →*
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range :=
  B.c.codRestrict _ (fun s => B.constant_range_full hlarge P ⟨s,rfl⟩)

end InitialCoverSystem
end PairFormalLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_IndividualGridSplits
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section IndividualGridSplits
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    {ι D : Type*} {κ : ι → Type*} [∀ i, Finite (κ i)]
    (hlarge : 15 < m+1)
    (Q : (i : ι) → κ i → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (Q i))
    (U : ι → polygonAlgebra a) (W : D → polygonAlgebra a)

noncomputable def gridInput (i : ι) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (Q i) (h i) (U i)

noncomputable def gridPiece (d : D) (i : ι) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (Q i) (h i) (U i ⊓ W d)

end InitialCoverSystem
end IndividualGridSplits

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

noncomputable def initialPatchPrimitives (r : CutRing) (n : ℕ) :
    Sum (Fin 5) (Fin 2 × Fin (n-1)) → Fin 5 × (CutRing × CutRing) :=
  Sum.elim (fun j => (j,0)) (coordinateWindowPrimitives n (symmetricWindowStart r))

end ConcurrentGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_DistinctSlotStars
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section DistinctSlotStars

noncomputable def slotAlternatingHom {a m : ℕ} (V : polygonAlgebra a)
    (slots : Fin 5 → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m V slots)) :
    alternatingGroup (Fin 5) →* polygonAlternatingGroup a m :=
  ((slotHom V slots hinj).comp (alternatingGroup (Fin 5)).subtype).codRestrict _
    (fun s => slotHom_alternating_mem V slots hinj s.property)

end DistinctSlotStars

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrivateBankFixer
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem sourceAlignedGroup_supported (J : Finset (Fin (m+1)))
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ sourceAlignedGroup a r m hm M B.t J) :
    SupportedIn (coverMap M (alternatingGenerator a r m hm) z).val.val
      {p : TrackPoint a (m+1) | p.1 ∈ J} := by
  classical
  let q : BoundedRelationCover M (alternatingGenerator a r m hm) →* Equiv.Perm (TrackPoint a (m+1)) :=
    (polygonFullGroup a (m+1)).subtype.comp
      ((polygonAlternatingGroup a (m+1)).subtype.comp (coverMap M (alternatingGenerator a r m hm)))
  let K : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) := {
    carrier := {z | SupportedIn (q z) {p : TrackPoint a (m+1) | p.1 ∈ J}}
    one_mem' := by intro p hp; simp
    mul_mem' := by
      intro x y hx hy p hp
      rw [map_mul,Equiv.Perm.mul_apply,hy p hp,hx p hp]
    inv_mem' := by
      intro x hx
      change SupportedIn (q x⁻¹) _
      rw [map_inv]
      exact supported_inv hx }
  have hK : sourceAlignedGroup a r m hm M B.t J ≤ K := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨c,hc,k,rfl⟩
    change SupportedIn (q (B.t k * PresentedGroup.of (sourceConditionalLabel m c) * (B.t k)⁻¹)) _
    rw [map_mul,map_mul,map_inv]
    obtain ⟨d,hd⟩ := sourceLatticeFullMap_translation a r m hm k
    have ht : q (B.t k) = (trackTranslation (a:=a) d).val := by
      have ht := congrArg Subtype.val (DFunLike.congr_fun B.t_projection k)
      change (coverMap M (alternatingGenerator a r m hm) (B.t k)).val =
        sourceLatticeFullMap a r m hm k at ht
      exact congrArg Subtype.val (ht.trans hd)
    rw [ht]
    have hs : SupportedIn (q (PresentedGroup.of (sourceConditionalLabel m c)))
        {p : TrackPoint a (m+1) | p.1 ∈ J} := by
      intro p hp
      have hf : c.2.val p.1=p.1 := Equiv.Perm.notMem_support.mp (fun hi => hp (hc hi))
      change (conditionalPerm (initialTest a r c.1) c.2.val) p=p
      simp [conditionalPerm,hf]
    apply (supported_conjugate (trackTranslation (a:=a) d).val hs).mono
    rintro p ⟨⟨i,x⟩,hi,rfl⟩
    exact hi
  exact hK hz

end

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PeriodicSlotStars
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

theorem translate_orbitRepresentative (a : ℕ) (u : CutRing × CutRing) (x : GenericSquare a) :
    translate a u x=translate a (orbitRepresentative u) x :=
  congrArg (fun e : Equiv.Perm (GenericSquare a) => e x) (translation_reduce a u)

theorem SlotMap_orbitRepresentative {a m : ℕ} (V : polygonAlgebra a)
    (i : Fin 5 → Fin m) (u : Fin 5 → CutRing × CutRing) :
    SlotMap a m V (fun j => (i j,u j))=
      SlotMap a m V (fun j => (i j,orbitRepresentative (u j))) := by
  funext p
  exact congrArg (fun z => (i p.1,z)) (translate_orbitRepresentative a (u p.1) p.2.val)

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FiniteSlotRefinement
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FiniteSlotRefinement

theorem polygon_finite_cover_induction {a : ℕ} (P : polygonAlgebra a → Prop)
    (hbot : P ⊥)
    (hunion : ∀ U W : polygonAlgebra a, Disjoint U.val W.val → P U → P W → P (U ⊔ W))
    (s : Finset (polygonAlgebra a)) (V : polygonAlgebra a)
    (hcover : V ≤ s.sup id)
    (hlocal : ∀ U ∈ s, ∀ W : polygonAlgebra a, W ≤ U → P W) : P V := by
  classical
  induction s using Finset.induction_on generalizing V with
  | empty =>
    have he : V=⊥ := le_antisymm (by simpa using hcover) bot_le
    simpa only [he] using hbot
  | @insert U s hUs ih =>
    have hleft : P (V ⊓ U) := hlocal U (Finset.mem_insert_self _ _) _ inf_le_right
    have hright : P (V ⊓ Uᶜ) := by
      apply ih (V ⊓ Uᶜ)
      · intro x hx
        have hc := hcover hx.1
        rw [Finset.sup_insert] at hc
        exact hc.resolve_left hx.2
      · intro W hW Z hZ
        exact hlocal W (Finset.mem_insert_of_mem hW) Z hZ
    have hd : Disjoint (V ⊓ U).val (V ⊓ Uᶜ).val := Set.disjoint_left.mpr (by
      intro x hx hy
      exact hy.2 hx.2)
    have he : (V ⊓ U) ⊔ (V ⊓ Uᶜ)=V := by
      ext x
      change (x∈V.val ∧ x∈U.val) ∨ (x∈V.val ∧ x∉U.val) ↔ x∈V.val
      tauto
    rw [← he]
    exact hunion _ _ hd hleft hright

end FiniteSlotRefinement

section SlotTransportClosure

theorem SlotMap_injective_of_transport {a m : ℕ} (V : polygonAlgebra a)
    (i k : Fin 5 → Fin m) (u v : Fin 5 → CutRing × CutRing)
    (f : TrackPoint a m → TrackPoint a m) (hf : Function.Injective f)
    (hi : Function.Injective (SlotMap a m V (fun j => (i j,u j))))
    (htr : ∀ (j : Fin 5) (x : V.val),
      f (i j,translate a (u j) x.val)=(k j,translate a (v j) x.val)) :
    Function.Injective (SlotMap a m V (fun j => (k j,v j))) := by
  have he : SlotMap a m V (fun j => (k j,v j))=f ∘ SlotMap a m V (fun j => (i j,u j)) := by
    funext p
    exact (htr p.1 p.2).symm
  rw [he]
  exact hf.comp hi

end SlotTransportClosure

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonTrajectoryStrata
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem representative_add (u v : CutRing × CutRing) :
    orbitRepresentative (u+v)=orbitRepresentative u+orbitRepresentative v := by
  simp [orbitRepresentative,add_mul]

@[simp] theorem representative_idem (u : CutRing × CutRing) :
    orbitRepresentative (orbitRepresentative u)=orbitRepresentative u := by
  simp [orbitRepresentative,cutTau]

theorem arrow_displacement_exists {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point) :
    ∃u,(f.toEquiv x).val.2=translate a u x.val.2 := by
  obtain ⟨s,hs,hcover⟩ := f.hasTable
  obtain ⟨c,hc,ht,hx⟩ := hcover x
  obtain ⟨hu,he⟩ := hs c hc x.val.2 hx
  have hpoint : (⟨(c.source,x.val.2),hu⟩ : U.Point)=x :=
    Subtype.ext (Prod.ext ht.symm rfl)
  rw [hpoint] at he
  exact ⟨c.shift,congrArg Prod.snd he⟩

noncomputable def pointShift {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point) :
    CutRing × CutRing := orbitRepresentative (arrow_displacement_exists f x).choose

theorem pointShift_spec {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point) :
    (f.toEquiv x).val.2=translate a (pointShift f x) x.val.2 :=
  (arrow_displacement_exists f x).choose_spec.trans (translate_orbitRepresentative _ _ _)

theorem pointShift_unique {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point)
    (u : CutRing × CutRing) (he : (f.toEquiv x).val.2=translate a u x.val.2) :
    pointShift f x=orbitRepresentative u :=
  orbitRepresentative_eq_of_translate_eq x.val.2
    ((arrow_displacement_exists f x).choose_spec.symm.trans he)

@[simp] theorem pointShift_reduced {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point) :
    orbitRepresentative (pointShift f x)=pointShift f x := representative_idem _

@[simp] theorem pointShift_id (U : PolygonObject a) (x : U.Point) : pointShift (𝟙 U) x=0 := by
  change pointShift (𝟙 U) x=(0,0)
  simpa [orbitRepresentative] using pointShift_unique (𝟙 U) x 0 (by simp [arrow_id_apply])

theorem chart_pointShift {U V : PolygonObject a} (f : U ⟶ V)
    (c : Chart (a:=a) U.tracks V.tracks) (hc : c.Holds f.toEquiv) (x : U.Point)
    (hx : c.Contains x) : pointShift f x=orbitRepresentative c.shift := by
  obtain ⟨hu,he⟩ := hc x.val.2 hx.2
  have hpoint : (⟨(c.source,x.val.2),hu⟩ : U.Point)=x :=
    Subtype.ext (Prod.ext hx.1.symm rfl)
  rw [hpoint] at he
  exact pointShift_unique f x _ (congrArg Prod.snd he)

theorem pointShift_finite_range {U V : PolygonObject a} (f : U ⟶ V) :
    (Set.range (pointShift f)).Finite := by
  obtain ⟨s,hs,hcover⟩ := f.hasTable
  apply (s.finite_toSet.image (fun c => orbitRepresentative c.shift)).subset
  rintro _ ⟨x,rfl⟩
  obtain ⟨c,hc,hx⟩ := hcover x
  exact ⟨c,hc,(chart_pointShift f c (hs c hc) x hx).symm⟩

noncomputable def trajectoryShift (F : RawString a n) (x : (F.obj 0).Point) :
    Fin (n+1) → CutRing × CutRing := fun i => pointShift (baseArrow F i) x

theorem trajectoryShift_finite_range (F : RawString a n) :
    (Set.range (trajectoryShift F)).Finite := by
  let S (i : Fin (n+1)) := Set.range (pointShift (baseArrow F i))
  let : ∀ index, Finite (S index) := fun index =>
    (pointShift_finite_range (baseArrow F index)).to_subtype
  let val : (∀i,S i) → (Fin (n+1) → CutRing × CutRing) := fun t i => (t i).val
  apply (Set.finite_range val).subset
  rintro _ ⟨x,rfl⟩
  exact ⟨fun i => ⟨pointShift (baseArrow F i) x,⟨x,rfl⟩⟩,rfl⟩

end PolygonObject
end PolygonTrajectoryStrata

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonStringNormalization
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PolygonStringNormalization

open Classical _root_.CategoryTheory Set
namespace PolygonObject
variable {a n : ℕ}

noncomputable def translationString (U : PolygonObject a)
    (d : Fin (n+1) → Fin U.tracks → CutRing × CutRing) : RawString a n where
  obj i := shifted U (d i)
  map {i j} _ := CategoryTheory.inv (shiftArrow U (d i)) ≫ shiftArrow U (d j)
  map_id i := by simp
  map_comp f g := by simp [Category.assoc]

end PolygonObject
end PolygonStringNormalization

open Classical _root_.CategoryTheory Set
namespace PolygonObject
variable {a n m : ℕ}

@[simp] theorem trajectoryShift_zero (F : RawString a n) (x : (F.obj 0).Point) :
    trajectoryShift F x 0=0 := by
  change pointShift (baseArrow F 0) x=0
  rw [baseArrow_zero,pointShift_id]

noncomputable def increments (F : RawString a n) (x : (F.obj 0).Point) :
    Fin n → CutRing × CutRing := fun i =>
      trajectoryShift F x i.succ - trajectoryShift F x i.castSucc

theorem increments_finite_range (F : RawString a n) : (Set.range (increments F)).Finite := by
  exact (trajectoryShift_finite_range F).image (fun t i => t i.succ-t i.castSucc) |>.subset
    (by rintro _ ⟨x,rfl⟩; exact ⟨trajectoryShift F x,⟨x,rfl⟩,rfl⟩)

end PolygonObject

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonStrandReconstruction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonStrandReconstruction

open Classical _root_.CategoryTheory
namespace PolygonObject
variable {a n : ℕ}

theorem representative_sub (u v : CutRing × CutRing) :
    orbitRepresentative (u-v)=orbitRepresentative u-orbitRepresentative v := by
  simp [orbitRepresentative,sub_mul]

theorem trajectoryShift_translationString (U : PolygonObject a)
    (d : Fin (n+1) → Fin U.tracks → CutRing × CutRing) (x : U.Point) (i : Fin (n+1)) :
    trajectoryShift (translationString U d) ((shiftArrow U (d 0)).toEquiv x) i=
      orbitRepresentative (d i x.val.1-d 0 x.val.1) := by
  apply pointShift_unique
  change ((CategoryTheory.inv (shiftArrow U (d 0)) ≫ shiftArrow U (d i)).toEquiv
    ((shiftArrow U (d 0)).toEquiv x)).val.2 = _
  simp only [arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
  simp only [shiftArrow_apply]
  rw [←translate_add,sub_add_cancel]

theorem increments_translationString (U : PolygonObject a)
    (d : Fin (n+1) → Fin U.tracks → CutRing × CutRing) (x : U.Point) (i : Fin n) :
    increments (translationString U d) ((shiftArrow U (d 0)).toEquiv x) i=
      orbitRepresentative (d i.succ x.val.1-d i.castSucc x.val.1) := by
  unfold increments
  rw [trajectoryShift_translationString,trajectoryShift_translationString,←representative_sub]
  congr 1
  abel

noncomputable def incrementString (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing) : RawString a n :=
  translationString U (fun i j => Fin.partialSum (γ j) i)

noncomputable def incrementInitial (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing) : U ⟶ (incrementString U γ).obj 0 :=
  shiftArrow U (fun j => Fin.partialSum (γ j) 0)

theorem incrementInitial_positional (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing) : Positional (incrementInitial U γ) := by
  intro x
  change translate a (Fin.partialSum (γ x.val.1) 0) x.val.2=x.val.2
  rw [Fin.partialSum_zero,translate_zero]

theorem incrementString_spec (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing) (x : U.Point) (i : Fin n) :
    increments (incrementString U γ) ((incrementInitial U γ).toEquiv x) i=
      orbitRepresentative (γ x.val.1 i) := by
  change increments (translationString U (fun i j => Fin.partialSum (γ j) i))
    ((shiftArrow U (fun j => Fin.partialSum (γ j) 0)).toEquiv x) i=_
  rw [increments_translationString,Fin.partialSum_succ]
  congr 1
  abel

theorem incrementString_spec_reduced (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing)
    (hγ : ∀j i,orbitRepresentative (γ j i)=γ j i) (x : U.Point) :
    increments (incrementString U γ) ((incrementInitial U γ).toEquiv x)=γ x.val.1 := by
  funext i
  rw [incrementString_spec,hγ]

end PolygonObject
end PolygonStrandReconstruction

section PolygonIncrementFibers

open Classical _root_.CategoryTheory
namespace PolygonObject
variable {a n : ℕ}

theorem partialSum_increments (F : RawString a n) (x : (F.obj 0).Point) (i : Fin (n+1)) :
    Fin.partialSum (increments F x) i=trajectoryShift F x i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    rw [Fin.partialSum_succ,hi]
    unfold increments
    abel

theorem trajectory_eq_of_increments {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0)
    (hp : Positional h) (he : ∀x,increments G (h.toEquiv x)=increments F x)
    (x : (F.obj 0).Point) : trajectory G (h.toEquiv x)=trajectory F x := by
  funext i
  unfold trajectory
  rw [pointShift_spec (baseArrow G i),pointShift_spec (baseArrow F i)]
  change translate a (trajectoryShift G (h.toEquiv x) i) (h.toEquiv x).val.2=
    translate a (trajectoryShift F x i) x.val.2
  rw [hp x,←partialSum_increments,←partialSum_increments,he x]

theorem extendLadder_positional_of_increments {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0)
    (hp : Positional h) (he : ∀x,increments G (h.toEquiv x)=increments F x) :
    (ladderProperty a n) (extendLadder h) :=
  extendLadder_positional h (trajectory_eq_of_increments h hp he)

end PolygonObject
end PolygonIncrementFibers

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrajectoryLabels
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

structure Labelled (a n : ℕ) where
  polygon : PolygonObject a
  label : Fin polygon.tracks → Fin n → CutRing × CutRing
  reduced : ∀ j i, orbitRepresentative (label j i) = label j i

namespace Labelled
variable {a n : ℕ}
structure Hom (U V : Labelled a n) where
  arrow : U.polygon ⟶ V.polygon
  positional : Positional arrow
  labelled : ∀ x, V.label (arrow.toEquiv x).val.1 = U.label x.val.1

@[ext] theorem Hom.ext {U V : Labelled a n} (f g : Hom U V) (h : f.arrow = g.arrow) : f=g := by
  cases f; cases g; cases h; rfl

noncomputable instance instCategory : Category (Labelled a n) where
  Hom := Hom
  id object := ⟨𝟙 object.polygon, (fun _ => rfl), fun _ => rfl⟩
  comp f g := ⟨f.arrow ≫ g.arrow, positional_comp f.positional g.positional,
    fun point => (g.labelled (f.arrow.toEquiv point)).trans (f.labelled point)⟩
  id_comp _ := Hom.ext _ _ (Category.id_comp _)
  comp_id _ := Hom.ext _ _ (Category.comp_id _)
  assoc _ _ _ := Hom.ext _ _ (Category.assoc _ _ _)

noncomputable instance instIsIso {U V : Labelled a n} (f : U ⟶ V) : IsIso f := by
  refine ⟨⟨⟨inv f.arrow,positional_inv f.positional,?_⟩,?_,?_⟩⟩
  · intro x
    obtain ⟨y,rfl⟩ := f.arrow.toEquiv.surjective x
    simpa only [inv_arrow_apply,Equiv.symm_apply_apply] using (f.labelled y).symm
  · apply Hom.ext; exact IsIso.hom_inv_id _
  · apply Hom.ext; exact IsIso.inv_hom_id _

noncomputable instance instGroupoid : Groupoid (Labelled a n) := Groupoid.ofIsIso (fun _ => inferInstance)

noncomputable abbrev string (U : Labelled a n) : StringGroupoid a n :=
  ⟨incrementString U.polygon U.label⟩
noncomputable abbrev initial (U : Labelled a n) := incrementInitial U.polygon U.label

noncomputable def initialArrow {U V : Labelled a n} (f : U ⟶ V) :
    (string U).obj.obj 0 ⟶ (string V).obj.obj 0 :=
  inv (initial U) ≫ f.arrow ≫ initial V

theorem initialArrow_positional {U V : Labelled a n} (f : U ⟶ V) :
    Positional (initialArrow f) :=
  positional_comp (positional_inv (incrementInitial_positional _ _))
    (positional_comp f.positional (incrementInitial_positional _ _))

theorem initialArrow_labelled {U V : Labelled a n} (f : U ⟶ V)
    (x : ((string U).obj.obj 0).Point) :
    increments (string V).obj ((initialArrow f).toEquiv x) = increments (string U).obj x := by
  obtain ⟨y,rfl⟩ := (initial U).toEquiv.surjective x
  simp only [initialArrow,arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
  rw [incrementString_spec_reduced _ _ V.reduced,incrementString_spec_reduced _ _ U.reduced]
  exact f.labelled y

noncomputable def ladder {U V : Labelled a n} (f : U ⟶ V) : string U ⟶ string V :=
  ⟨extendLadder (initialArrow f),extendLadder_positional_of_increments _
    (initialArrow_positional f) (initialArrow_labelled f)⟩

@[simp] theorem ladder_zero {U V : Labelled a n} (f : U ⟶ V) :
    (ladder f).hom.app 0 = initialArrow f := extendLadder_zero _

theorem increments_reduced (F : RawString a n) (x : (F.obj 0).Point) (i : Fin n) :
    orbitRepresentative (increments F x i) = increments F x i := by
  simp only [increments,representative_sub,trajectoryShift,pointShift_reduced]

abbrev Support (F : RawString a n) := Set.range (increments F)
noncomputable instance instFintypeElemForallFinProdCutRingSupport (F : RawString a n) : Fintype (Support F) :=
  (increments_finite_range F).fintype
noncomputable def supportLabel (F : RawString a n) (x : (F.obj 0).Point) : Support F :=
  ⟨increments F x,⟨x,rfl⟩⟩

end Labelled
end SimpleAmenable.PolygonObject

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonDiagramRefinement
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonDiagramRefinement

open Classical _root_.CategoryTheory Set
namespace PolygonObject
variable {a : ℕ}

theorem chart_target_track {U V : PolygonObject a} (f : U ⟶ V)
    (c : Chart (a:=a) U.tracks V.tracks) (hc : c.Holds f.toEquiv) (x : U.Point)
    (hx : c.Contains x) : (f.toEquiv x).val.1=c.target := by
  obtain ⟨hu,he⟩ := hc x.val.2 hx.2
  have hpoint : (⟨(c.source,x.val.2),hu⟩ : U.Point)=x :=
    Subtype.ext (Prod.ext hx.1.symm rfl)
  rw [hpoint] at he
  exact congrArg Prod.fst he

theorem targetTrack_fiber_polygon {U V : PolygonObject a} (f : U ⟶ V)
    (i : Fin U.tracks) (j : Fin V.tracks) :
    {z | ∃hz : z∈(U.cell i).val,(f.toEquiv ⟨(i,z),hz⟩).val.1=j}∈polygonAlgebra a := by
  obtain ⟨s,hs,hcover⟩ := f.hasTable
  have he : {z | ∃hz : z∈(U.cell i).val,(f.toEquiv ⟨(i,z),hz⟩).val.1=j} =
      ⋃c∈s.filter (fun c => c.source=i ∧ c.target=j),c.domain.val := by
    ext z
    constructor
    · rintro ⟨hz,hj⟩
      obtain ⟨c,hc,hz'⟩ := hcover ⟨(i,z),hz⟩
      exact Set.mem_iUnion₂.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,hz'.1.symm,
        (chart_target_track f c (hs c hc) ⟨(i,z),hz⟩ hz').symm.trans hj⟩,hz'.2⟩
    · intro hz
      obtain ⟨c,hcf,hcz⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨hcs,hci,hcj⟩ := Finset.mem_filter.mp hcf
      obtain ⟨hz',hf⟩ := hs c hcs z hcz
      subst i
      exact ⟨hz',(chart_target_track f c (hs c hcs) ⟨(c.source,z),hz'⟩ ⟨rfl,hcz⟩).trans hcj⟩
  rw [he]
  apply BooleanSubalgebra.biSup_mem (Finset.finite_toSet _)
  intro c _
  exact c.domain.property

end PolygonObject
end PolygonDiagramRefinement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_BooleanStages
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open Classical Set _root_.CategoryTheory
namespace SimpleAmenable.PolygonObject

structure BooleanPartition (a : ℕ) where
  size : ℕ
  color : GenericSquare a → Fin size
  onto : Function.Surjective color
  polygon : ∀ b, {x | color x=b}∈polygonAlgebra a

namespace BooleanPartition
variable {a : ℕ}
noncomputable def cell (P : BooleanPartition a) (b : Fin P.size) : polygonAlgebra a :=
  ⟨_,P.polygon b⟩
noncomputable def point (P : BooleanPartition a) (b : Fin P.size) : GenericSquare a :=
  (P.onto b).choose
@[simp] theorem color_point (P : BooleanPartition a) (b : Fin P.size) :
    P.color (P.point b)=b := (P.onto b).choose_spec

variable {ι : Type} [Fintype ι] (S : ι → polygonAlgebra a)
noncomputable def signature (x : GenericSquare a) : ι → Bool := fun i => decide (x∈(S i).val)

theorem signature_fiber (b : ι → Bool) : {x | signature S x=b}∈polygonAlgebra a := by
  have he : {x | signature S x=b} = ⋂ i, if b i then (S i).val else (S i).valᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    constructor
    · intro h i
      have hx := congrFun h i
      cases hb : b i <;> simp_all [signature]
    · intro h
      funext i
      have hi := h i
      cases hb : b i <;> simp_all [signature]
  rw [he]
  apply BooleanSubalgebra.iInf_mem
  intro i
  split_ifs
  · exact (S i).property
  · exact (polygonAlgebra a).compl_mem (S i).property

noncomputable def generated : BooleanPartition a where
  size := Fintype.card (Set.range (signature S))
  color x := Fintype.equivFin (Set.range (signature S)) ⟨_,⟨x,rfl⟩⟩
  onto b := by
    obtain ⟨x,hx⟩ := ((Fintype.equivFin (Set.range (signature S))).symm b).property
    refine ⟨x,?_⟩
    apply (Equiv.eq_symm_apply _).mp
    exact Subtype.ext hx
  polygon b := by
    convert signature_fiber S (((Fintype.equivFin (Set.range (signature S))).symm b).val) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← Equiv.eq_symm_apply,Subtype.ext_iff]

theorem generated_constant {x y : GenericSquare a}
    (h : (generated S).color x=(generated S).color y) (i : ι) :
    x∈(S i).val ↔ y∈(S i).val := by
  have h' := congrArg (fun z : Set.range (signature S) => z.val)
    ((Fintype.equivFin (Set.range (signature S))).injective h)
  have hi := congrFun h' i
  by_cases hx : x∈(S i).val <;> by_cases hy : y∈(S i).val <;> simp_all [signature]

theorem exists_common (S : ι → polygonAlgebra a) :
    ∃ P : BooleanPartition a, ∀ i x y, P.color x=P.color y →
      (x∈(S i).val ↔ y∈(S i).val) :=
  ⟨generated S,fun i _ _ h => generated_constant S h i⟩

end BooleanPartition
end SimpleAmenable.PolygonObject

end

section

open Classical Set _root_.CategoryTheory
namespace SimpleAmenable.PolygonObject

namespace Labelled
variable {a n : ℕ}

noncomputable def forget : Labelled a n ⥤ PolygonObject a where
  obj U := U.polygon
  map f := f.arrow

@[simp] lemma inv_arrow {U V : Labelled a n} (f : U ⟶ V) :
    (inv f).arrow=inv f.arrow := (forget (a:=a) (n:=n)).map_inv f

def ObjectUniform (P : BooleanPartition a) (U : Labelled a n) : Prop :=
  ∀ j x y, P.color x=P.color y → (x∈(U.polygon.cell j).val ↔ y∈(U.polygon.cell j).val)

def ArrowUniform (P : BooleanPartition a) {U V : Labelled a n} (f : U ⟶ V) : Prop :=
  ∀ x y, x.val.1=y.val.1 → P.color x.val.2=P.color y.val.2 →
    (f.arrow.toEquiv x).val.1=(f.arrow.toEquiv y).val.1

lemma arrowUniform_id (P : BooleanPartition a) (U : Labelled a n) :
    ArrowUniform P (𝟙 U) := fun _ _ h _ => h

lemma arrowUniform_comp (P : BooleanPartition a) {U V W : Labelled a n}
    {f : U ⟶ V} {g : V ⟶ W} (hf : ArrowUniform P f) (hg : ArrowUniform P g) :
    ArrowUniform P (f≫g) := by
  intro x y h hP
  apply hg
  · exact hf x y h hP
  · rw [f.positional x,f.positional y]
    exact hP

lemma arrowUniform_inv (P : BooleanPartition a) {U V : Labelled a n}
    (hU : ObjectUniform P U) {f : U ⟶ V} (hf : ArrowUniform P f) :
    ArrowUniform P (inv f) := by
  intro x y h hP
  let x' := (inv f).arrow.toEquiv x
  let y' := (inv f).arrow.toEquiv y
  have hx : x'.val.2=x.val.2 := (inv f).positional x
  have hy : y'.val.2=y.val.2 := (inv f).positional y
  have hmem : y.val.2∈(U.polygon.cell x'.val.1).val :=
    (hU x'.val.1 x'.val.2 y.val.2 (by rw [hx]; exact hP)).mp x'.property
  let z : U.polygon.Point := ⟨(x'.val.1,y.val.2),hmem⟩
  have htrack : (f.arrow.toEquiv z).val.1=y.val.1 := by
    have h' := hf z x' rfl (by simp only [z,hx]; exact hP.symm)
    rw [show f.arrow.toEquiv x'=x from by
      dsimp only [x']; rw [inv_arrow,inv_arrow_apply,Equiv.apply_symm_apply]] at h'
    exact h'.trans h
  have hz : f.arrow.toEquiv z=y := by
    apply Subtype.ext
    exact Prod.ext htrack (f.positional z)
  have he : z=y' := by
    apply f.arrow.toEquiv.injective
    rw [hz]
    dsimp only [y']; rw [inv_arrow,inv_arrow_apply,Equiv.apply_symm_apply]
  change x'.val.1=y'.val.1
  have ht := congrArg (fun w : U.polygon.Point => w.val.1) he
  exact ht

variable {κ τ : Type} [Fintype κ] [Fintype τ]
    (U : κ → Labelled a n) (src dst : τ → κ) (f : ∀t,U (src t) ⟶ U (dst t))

theorem exists_uniform_partition :
    ∃ P : BooleanPartition a, (∀ k,ObjectUniform P (U k)) ∧
      (∀ t,ArrowUniform P (f t)) := by
  let I := (Σ k,Fin (U k).polygon.tracks) ⊕
    (Σ t,Fin (U (src t)).polygon.tracks × Fin (U (dst t)).polygon.tracks)
  let S : I → polygonAlgebra a := Sum.elim
    (fun kj => (U kj.1).polygon.cell kj.2)
    (fun tij => ⟨{x | ∃hx : x∈((U (src tij.1)).polygon.cell tij.2.1).val,
      ((f tij.1).arrow.toEquiv ⟨(tij.2.1,x),hx⟩).val.1=tij.2.2},
      targetTrack_fiber_polygon (f tij.1).arrow tij.2.1 tij.2.2⟩)
  obtain ⟨P,hP⟩ := BooleanPartition.exists_common S
  refine ⟨P,?_,?_⟩
  · intro k j x y h
    exact hP (.inl ⟨k,j⟩) x y h
  · intro t x y h hxy
    have h' := hP (.inr ⟨t,x.val.1,(f t).arrow.toEquiv x |>.val.1⟩) x.val.2 y.val.2 hxy
    have hx : x.val.2∈(S (.inr ⟨t,x.val.1,(f t).arrow.toEquiv x |>.val.1⟩)).val :=
      ⟨x.property,rfl⟩
    obtain ⟨hy,he⟩ := h'.mp hx
    have hpt : (⟨(x.val.1,y.val.2),hy⟩ : (U (src t)).polygon.Point)=y := by
      apply Subtype.ext
      exact Prod.ext h rfl
    rw [hpt] at he
    exact he.symm

end Labelled
end SimpleAmenable.PolygonObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrajectoryStages
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

abbrev Obj := (Fin P.size × Fin s) → FiniteSetGroupoid
abbrev Track (U : Obj P (s:=s)) := Σ b : Fin P.size × Fin s, Fin (U b).size
noncomputable abbrev index (U : Obj P (s:=s)) := Fintype.equivFin (Track P U)
noncomputable def object (U : Obj P (s:=s)) : Labelled a n where
  polygon := ⟨Fintype.card (Track P U), fun j => P.cell (((index P U).symm j).1.1)⟩
  label j := L (((index P U).symm j).1.2)
  reduced track := hL (((index P U).symm track).1.2)

noncomputable def trackMap {U V : Obj P (s:=s)} (f : U ⟶ V) : Track P U ≃ Track P V :=
  Equiv.sigmaCongrRight f
noncomputable def indexMap {U V : Obj P (s:=s)} (f : U ⟶ V) :
    Fin (object P L hL U).polygon.tracks ≃ Fin (object P L hL V).polygon.tracks :=
  (index P U).symm.trans ((trackMap P f).trans (index P V))

@[simp] theorem indexMap_atom {U V : Obj P (s:=s)} (f : U ⟶ V)
    (j : Fin (object P L hL U).polygon.tracks) :
    ((index P V).symm (indexMap P L hL f j)).1 = ((index P U).symm j).1 := by
  change ((index P V).symm ((index P V) ((trackMap P f) ((index P U).symm j)))).1 = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem indexMap_id (U : Obj P (s:=s)) (j : Fin (object P L hL U).polygon.tracks) :
    indexMap P L hL (𝟙 U) j=j := by
  change (index P U) ((index P U).symm j)=j
  exact Equiv.apply_symm_apply _ _

@[simp] theorem indexMap_comp {U V W : Obj P (s:=s)} (f : U ⟶ V) (g : V ⟶ W)
    (j : Fin (object P L hL U).polygon.tracks) :
    indexMap P L hL (f≫g) j = indexMap P L hL g (indexMap P L hL f j) := by
  change (index P W) ((trackMap P (f≫g)) ((index P U).symm j)) =
    (index P W) ((trackMap P g) ((index P V).symm
      ((index P V) ((trackMap P f) ((index P U).symm j)))))
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def pointMap {U V : Obj P (s:=s)} (f : U ⟶ V) :
    (object P L hL U).polygon.Point ≃ (object P L hL V).polygon.Point where
  toFun x := ⟨(indexMap P L hL f x.val.1,x.val.2), by
    change P.color x.val.2 = ((index P V).symm (indexMap P L hL f x.val.1)).1.1
    rw [indexMap_atom]
    exact x.property⟩
  invFun x := ⟨((indexMap P L hL f).symm x.val.1,x.val.2),by
    have h := indexMap_atom P L hL f ((indexMap P L hL f).symm x.val.1)
    rw [Equiv.apply_symm_apply] at h
    change P.color x.val.2 = ((index P U).symm ((indexMap P L hL f).symm x.val.1)).1.1
    rw [←h]
    exact x.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

noncomputable def arrow {U V : Obj P (s:=s)} (f : U ⟶ V) : object P L hL U ⟶ object P L hL V where
  arrow := relabelArrow (pointMap P L hL f) (indexMap P L hL f) (fun _ => rfl)
  positional _ := rfl
  labelled x := by
    change L (((index P V).symm (indexMap P L hL f x.val.1)).1.2) = _
    rw [indexMap_atom]
    rfl

@[simp] theorem arrow_apply {U V : Obj P (s:=s)} (f : U ⟶ V)
    (x : (object P L hL U).polygon.Point) :
    ((arrow P L hL f).arrow.toEquiv x).val = (indexMap P L hL f x.val.1,x.val.2) := rfl

noncomputable def functor : Obj P (s:=s) ⥤ Labelled a n where
  obj := object P L hL
  map := arrow P L hL
  map_id U := by
    apply Labelled.Hom.ext
    apply Arrow.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [arrow_apply]
    change (indexMap P L hL (𝟙 U) x.val.1,x.val.2) = x.val
    rw [indexMap_id]
  map_comp f g := by
    apply Labelled.Hom.ext
    apply Arrow.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change _ = ((arrow P L hL g).arrow.toEquiv ((arrow P L hL f).arrow.toEquiv x)).val
    rw [arrow_apply,arrow_apply,arrow_apply,indexMap_comp]

end LabelledStage
end SimpleAmenable.PolygonObject

end

section

open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace LabelledStage
variable {a n s : ℕ} (P : BooleanPartition a)
    (L : Fin s → Fin n → CutRing × CutRing)

structure UniformObject where
  obj : Labelled a n
  uniform : Labelled.ObjectUniform P obj
  supported : ∀ j,∃ l,L l=obj.label j

namespace UniformObject
variable {P L}
structure Hom (U V : UniformObject P L) where
  arrow : U.obj ⟶ V.obj
  uniform : Labelled.ArrowUniform P arrow
@[ext] theorem Hom.ext {U V : UniformObject P L} (f g : Hom U V) (h : f.arrow=g.arrow) : f=g := by
  cases f; cases g; cases h; rfl
noncomputable instance instCategory : Category (UniformObject P L) where
  Hom := Hom
  id U := ⟨𝟙 _,Labelled.arrowUniform_id P U.obj⟩
  comp f g := ⟨f.arrow≫g.arrow,Labelled.arrowUniform_comp P f.uniform g.uniform⟩
  id_comp _ := Hom.ext _ _ (Category.id_comp _)
  comp_id _ := Hom.ext _ _ (Category.comp_id _)
  assoc _ _ _ := Hom.ext _ _ (Category.assoc _ _ _)
noncomputable instance instIsIso {U V : UniformObject P L} (f : U ⟶ V) : IsIso f := by
  refine ⟨⟨⟨inv f.arrow,Labelled.arrowUniform_inv P U.uniform f.uniform⟩,?_,?_⟩⟩
  · exact Hom.ext _ _ (IsIso.hom_inv_id _)
  · exact Hom.ext _ _ (IsIso.inv_hom_id _)
noncomputable instance instGroupoid : Groupoid (UniformObject P L) := Groupoid.ofIsIso (fun _ => inferInstance)

noncomputable def forget : UniformObject P L ⥤ Labelled a n where
  obj U := U.obj
  map f := f.arrow
instance instFaithfulLabelledForget : (forget (P:=P) (L:=L)).Faithful where
  map_injective h := Hom.ext _ _ h

abbrev Fiber (U : UniformObject P L) (b : Fin P.size × Fin s) :=
  {x : U.obj.polygon.Point // x.val.2=P.point b.1 ∧ U.obj.label x.val.1=L b.2}

noncomputable instance instFintypeFiber (U : UniformObject P L) (b : Fin P.size × Fin s) : Fintype (Fiber U b) :=
  Fintype.ofInjective (fun x : Fiber U b => x.val.val.1) (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext h (x.property.1.trans y.property.1.symm))

noncomputable def fiberMap {U V : UniformObject P L} (f : U ⟶ V) (b : Fin P.size × Fin s) :
    Fiber U b ≃ Fiber V b where
  toFun x := ⟨f.arrow.arrow.toEquiv x.val,
    (f.arrow.positional x.val).trans x.property.1,
    (f.arrow.labelled x.val).trans x.property.2⟩
  invFun y := ⟨f.arrow.arrow.toEquiv.symm y.val,by
    have h := f.arrow.positional (f.arrow.arrow.toEquiv.symm y.val)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans y.property.1,by
    have h := f.arrow.labelled (f.arrow.arrow.toEquiv.symm y.val)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans y.property.2⟩
  left_inv _ := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (Equiv.apply_symm_apply _ _)

noncomputable def evaluation : UniformObject P L ⥤ Obj P (s:=s) where
  obj U b := ⟨Fintype.card (Fiber U b)⟩
  map {U V} f b := (Fintype.equivFin (Fiber U b)).symm.trans
    ((fiberMap f b).trans (Fintype.equivFin (Fiber V b)))
  map_id U := by
    funext b
    apply Equiv.ext
    intro j
    change (Fintype.equivFin (Fiber U b)) ((fiberMap (𝟙 U) b)
      ((Fintype.equivFin (Fiber U b)).symm j))=j
    change (Fintype.equivFin (Fiber U b)) ((Fintype.equivFin (Fiber U b)).symm j)=j
    exact Equiv.apply_symm_apply _ _
  map_comp {U V W} f g := by
    funext b
    apply Equiv.ext
    intro j
    change (Fintype.equivFin (Fiber W b)) ((fiberMap (f≫g) b) _)=
      (Fintype.equivFin (Fiber W b)) ((fiberMap g b)
        ((Fintype.equivFin (Fiber V b)).symm ((Fintype.equivFin (Fiber V b)) _)))
    rw [Equiv.symm_apply_apply]
    rfl

instance instFaithfulObjEvaluation : (evaluation (P:=P) (L:=L)).Faithful where
  map_injective {U V} f g h := by
    apply Hom.ext
    apply Labelled.Hom.ext
    apply Arrow.ext
    apply Equiv.ext
    intro x
    obtain ⟨l,hl⟩ := U.supported x.val.1
    let b := (P.color x.val.2,l)
    have hm : P.point b.1∈(U.obj.polygon.cell x.val.1).val :=
      (U.uniform x.val.1 x.val.2 (P.point b.1) (by simp [b])).mp x.property
    let y : Fiber U b := ⟨⟨(x.val.1,P.point b.1),hm⟩,rfl,hl.symm⟩
    have hh := congrFun h b
    have hy := congrArg (fun e : Fin (Fintype.card (Fiber U b)) ≃
        Fin (Fintype.card (Fiber V b)) => e (Fintype.equivFin (Fiber U b) y)) hh
    change (Fintype.equivFin (Fiber V b)) ((fiberMap f b)
        ((Fintype.equivFin (Fiber U b)).symm ((Fintype.equivFin (Fiber U b)) y)))=
      (Fintype.equivFin (Fiber V b)) ((fiberMap g b)
        ((Fintype.equivFin (Fiber U b)).symm ((Fintype.equivFin (Fiber U b)) y))) at hy
    simp only [Equiv.symm_apply_apply] at hy
    have he := (Fintype.equivFin (Fiber V b)).injective hy
    apply Subtype.ext
    apply Prod.ext
    · exact (f.uniform x y.val rfl (by simp [y,b])).trans
        ((congrArg (fun z : Fiber V b => z.val.val.1) he).trans
          (g.uniform x y.val rfl (by simp [y,b])).symm)
    · exact (f.arrow.positional x).trans (g.arrow.positional x).symm

end UniformObject
end LabelledStage
end SimpleAmenable.PolygonObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_LabelledMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject

namespace Labelled
variable {a n : ℕ}

noncomputable abbrev sum (U V : Labelled a n) : Labelled a n where
  polygon := PolygonObject.sum U.polygon V.polygon
  label := Fin.addCases U.label V.label
  reduced j i := by
    refine Fin.addCases ?_ ?_ j
    · intro k; simpa only [Fin.addCases_left] using U.reduced k i
    · intro k; simpa only [Fin.addCases_right] using V.reduced k i

noncomputable abbrev empty : Labelled a n where
  polygon := PolygonObject.empty
  label := Fin.elim0
  reduced := fun j => Fin.elim0 j

@[simp] lemma sum_label_left (U V : Labelled a n) (x : U.polygon.Point) :
    (sum U V).label (sumPointEquiv U.polygon V.polygon (.inl x)).val.1=U.label x.val.1 := by
  simp [sumPointEquiv_inl]
@[simp] lemma sum_label_right (U V : Labelled a n) (x : V.polygon.Point) :
    (sum U V).label (sumPointEquiv U.polygon V.polygon (.inr x)).val.1=V.label x.val.1 := by
  simp [sumPointEquiv_inr]

noncomputable def sumHom {U V W Z : Labelled a n} (f : U ⟶ W) (g : V ⟶ Z) :
    sum U V ⟶ sum W Z where
  arrow := sumArrow f.arrow g.arrow
  positional := sumArrow_positional f.positional g.positional
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
    cases y with
    | inl y => simpa only [sumArrow_inl,sumPointEquiv_inl,Fin.addCases_left] using f.labelled y
    | inr y => simpa only [sumArrow_inr,sumPointEquiv_inr,Fin.addCases_right] using g.labelled y

noncomputable def assocHom (U V W : Labelled a n) : sum (sum U V) W ⟶ sum U (sum V W) where
  arrow := sumAssoc U.polygon V.polygon W.polygon
  positional := sumAssoc_positional _ _ _
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V).polygon W.polygon).surjective x
    cases y with
    | inl y =>
      obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
      cases z <;> simp only [sumAssoc_apply,sumAssocEquiv_left,sumAssocEquiv_mid,
        sumPointEquiv_inl,sumPointEquiv_inr] <;>
        simp only [PolygonObject.sum,Fin.addCases_left,Fin.addCases_right]
    | inr y =>
      simp only [sumAssoc_apply,sumAssocEquiv_right,sumPointEquiv_inr]
      simp only [PolygonObject.sum,Fin.addCases_right]

noncomputable def leftHom (U : Labelled a n) : sum empty U ⟶ U where
  arrow := leftUnit U.polygon
  positional := leftUnit_positional _
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv PolygonObject.empty U.polygon).surjective x
    cases y with
    | inl y => exact isEmptyElim y
    | inr y =>
      simp only [leftUnit_apply,leftUnitEquiv_apply,sumPointEquiv_inr]
      simp only [PolygonObject.empty,Fin.addCases_right]

noncomputable def rightHom (U : Labelled a n) : sum U empty ⟶ U where
  arrow := rightUnit U.polygon
  positional := rightUnit_positional _
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon PolygonObject.empty).surjective x
    cases y with
    | inl y =>
      simp only [rightUnit_apply,rightUnitEquiv_apply,sumPointEquiv_inl]
      simp only [PolygonObject.empty,Fin.addCases_left]
    | inr y => exact isEmptyElim y

noncomputable def swapHom (U V : Labelled a n) : sum U V ⟶ sum V U where
  arrow := sumSwap U.polygon V.polygon
  positional := sumSwap_positional _ _
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
    cases y <;> simp only [sumSwap_apply,sumSwapEquiv_inl,sumSwapEquiv_inr,
      sumPointEquiv_inl,sumPointEquiv_inr,Fin.addCases_left,Fin.addCases_right]

instance instFaithfulForget : (forget (a:=a) (n:=n)).Faithful where
  map_injective h := Hom.ext _ _ h

noncomputable instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Labelled a n) where
  tensorObj := sum
  tensorHom := sumHom
  whiskerLeft U _ _ f := sumHom (𝟙 U) f
  whiskerRight f U := sumHom f (𝟙 U)
  tensorUnit := empty
  associator U V W := asIso (assocHom U V W)
  leftUnitor U := asIso (leftHom U)
  rightUnitor U := asIso (rightHom U)

noncomputable def inducing : Monoidal.InducingFunctorData (forget (a:=a) (n:=n)) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  whiskerRight_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  tensorHom_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  associator_eq := by
    intro U V W
    change sumAssoc U.polygon V.polygon W.polygon =
      (𝟙 _ ≫ sumArrow (𝟙 _) (𝟙 _)) ≫ sumAssoc U.polygon V.polygon W.polygon ≫
        (sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _)
    simp only [sumArrow_id,Category.id_comp,Category.comp_id]
  leftUnitor_eq := by
    intro U
    change leftUnit U.polygon = (𝟙 _ ≫ sumArrow (𝟙 _) (𝟙 _)) ≫ leftUnit U.polygon
    rw [sumArrow_id,Category.id_comp,Category.id_comp]
  rightUnitor_eq := by
    intro U
    change rightUnit U.polygon = (𝟙 _ ≫ sumArrow (𝟙 _) (𝟙 _)) ≫ rightUnit U.polygon
    rw [sumArrow_id,Category.id_comp,Category.id_comp]

noncomputable instance instMonoidalCategory : MonoidalCategory (Labelled a n) := Monoidal.induced forget inducing
noncomputable instance instMonoidalForget : (forget (a:=a) (n:=n)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (Monoidal.fromInducedCoreMonoidal forget inducing)

noncomputable instance instBraidedCategory : BraidedCategory (Labelled a n) where
  braiding U V := asIso (swapHom U V)
  braiding_naturality_left := by
    intro U V f W
    apply forget.map_injective
    exact BraidedCategory.braiding_naturality_left f.arrow W.polygon
  braiding_naturality_right := by
    intro U V W f
    apply forget.map_injective
    exact BraidedCategory.braiding_naturality_right U.polygon f.arrow
  hexagon_forward := by
    intro U V W
    apply forget.map_injective
    exact BraidedCategory.hexagon_forward U.polygon V.polygon W.polygon
  hexagon_reverse := by
    intro U V W
    apply forget.map_injective
    change (inv (assocHom U V W)).arrow ≫ (swapHom (sum U V) W).arrow ≫
      (inv (assocHom W U V)).arrow =
      sumArrow (𝟙 U.polygon) (swapHom V W).arrow ≫ (inv (assocHom U W V)).arrow ≫
      sumArrow (swapHom U W).arrow (𝟙 V.polygon)
    simp only [inv_arrow]
    exact BraidedCategory.hexagon_reverse U.polygon V.polygon W.polygon

noncomputable instance instSymmetricCategory : SymmetricCategory (Labelled a n) where
  symmetry U V := by
    apply forget.map_injective
    exact SymmetricCategory.symmetry U.polygon V.polygon

end Labelled
end SimpleAmenable.PolygonObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_UniformMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject

namespace Labelled
variable {a n : ℕ} (P : BooleanPartition a)

lemma objectUniform_sum {U V : Labelled a n} (hU : ObjectUniform P U) (hV : ObjectUniform P V) :
    ObjectUniform P (sum U V) := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i x y h; simpa only [PolygonObject.sum,Fin.addCases_left] using hU i x y h
  · intro i x y h; simpa only [PolygonObject.sum,Fin.addCases_right] using hV i x y h

lemma arrowUniform_sum {U V W Z : Labelled a n} {f : U ⟶ W} {g : V ⟶ Z}
    (hf : ArrowUniform P f) (hg : ArrowUniform P g) : ArrowUniform P (sumHom f g) := by
  intro x y h hP
  obtain ⟨x,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      simp only [sumPointEquiv_inl] at h
      have h := Fin.castAdd_inj.mp h
      simp only [sumHom,sumArrow_inl,sumPointEquiv_inl]
      simpa only [PolygonObject.sum] using
        congrArg (Fin.castAdd Z.polygon.tracks) (hf x y h hP)
    | inr y =>
      have he := congrArg Fin.val h
      simp only [sumPointEquiv_inl,sumPointEquiv_inr,Fin.val_castAdd,Fin.val_natAdd] at he
      have hx := x.val.1.isLt
      omega
  | inr x =>
    cases y with
    | inl y =>
      have he := congrArg Fin.val h
      simp only [sumPointEquiv_inl,sumPointEquiv_inr,Fin.val_castAdd,Fin.val_natAdd] at he
      have hy := y.val.1.isLt
      omega
    | inr y =>
      simp only [sumPointEquiv_inr] at h
      have h := (Fin.natAdd_inj _).mp h
      simp only [sumHom,sumArrow_inr,sumPointEquiv_inr]
      simpa only [PolygonObject.sum] using
        congrArg (Fin.natAdd W.polygon.tracks) (hg x y h hP)

lemma relabel_uniform {U V : PolygonObject a} (e : U.Point ≃ V.Point)
    (r : Fin U.tracks → Fin V.tracks)
    (he : ∀ x, (e x).val=(r x.val.1,x.val.2)) :
    ∀ x y, x.val.1=y.val.1 → P.color x.val.2=P.color y.val.2 →
      ((relabelArrow e r he).toEquiv x).val.1=((relabelArrow e r he).toEquiv y).val.1 := by
  intro x y h _
  change (e x).val.1=(e y).val.1
  rw [he x,he y,h]

lemma assocHom_uniform (U V W : Labelled a n) : ArrowUniform P (assocHom U V W) := by
  exact relabel_uniform P (sumAssocEquiv U.polygon V.polygon W.polygon)
    (Fin.addCases
      (Fin.addCases (fun i => i.castAdd (V.polygon.tracks+W.polygon.tracks)) (fun i => (i.castAdd W.polygon.tracks).natAdd U.polygon.tracks))
      (fun i => (i.natAdd V.polygon.tracks).natAdd U.polygon.tracks)) (by
      intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (PolygonObject.sum U.polygon V.polygon) W.polygon).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
        cases z <;> simp only [sumAssocEquiv_left,sumAssocEquiv_mid,sumPointEquiv_inl,sumPointEquiv_inr] <;>
          simp only [PolygonObject.sum,Fin.addCases_left,Fin.addCases_right]
      | inr y =>
        simp only [sumAssocEquiv_right,sumPointEquiv_inr]
        simp only [PolygonObject.sum,Fin.addCases_right])
lemma swapHom_uniform (U V : Labelled a n) : ArrowUniform P (swapHom U V) := by
  exact relabel_uniform P (sumSwapEquiv U.polygon V.polygon)
    (Fin.addCases (fun i => i.natAdd V.polygon.tracks) (fun i => i.castAdd U.polygon.tracks)) (by
      intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
      cases y <;> simp only [sumSwapEquiv_inl,sumSwapEquiv_inr,sumPointEquiv_inl,sumPointEquiv_inr] <;>
        simp only [PolygonObject.sum,Fin.addCases_left,Fin.addCases_right])
lemma leftHom_uniform (U : Labelled a n) : ArrowUniform P (leftHom U) := by
  exact relabel_uniform P (leftUnitEquiv U.polygon) (Fin.addCases Fin.elim0 id) (by
    intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv PolygonObject.empty U.polygon).surjective x
    cases y with
    | inl y => exact isEmptyElim y
    | inr y =>
      simp only [leftUnitEquiv_apply,sumPointEquiv_inr]
      simp only [PolygonObject.empty,Fin.addCases_right,id_eq])
lemma rightHom_uniform (U : Labelled a n) : ArrowUniform P (rightHom U) := by
  exact relabel_uniform P (rightUnitEquiv U.polygon) (Fin.addCases id Fin.elim0) (by
    intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon PolygonObject.empty).surjective x
    cases y with
    | inl y =>
      simp only [rightUnitEquiv_apply,sumPointEquiv_inl]
      simp only [PolygonObject.empty,Fin.addCases_left,id_eq]
    | inr y => exact isEmptyElim y)

lemma sumHom_id (U V : Labelled a n) : sumHom (𝟙 U) (𝟙 V)=𝟙 (sum U V) :=
  Hom.ext _ _ (sumArrow_id _ _)
end Labelled

namespace LabelledStage.UniformObject
variable {a n s : ℕ} {P : BooleanPartition a} {L : Fin s → Fin n → CutRing × CutRing}

noncomputable abbrev sum (U V : UniformObject P L) : UniformObject P L where
  obj := Labelled.sum U.obj V.obj
  uniform := Labelled.objectUniform_sum P U.uniform V.uniform
  supported j := by
    refine Fin.addCases ?_ ?_ j
    · intro i; simpa only [Fin.addCases_left] using U.supported i
    · intro i; simpa only [Fin.addCases_right] using V.supported i

noncomputable abbrev empty : UniformObject P L where
  obj := Labelled.empty
  uniform j := Fin.elim0 j
  supported j := Fin.elim0 j

noncomputable def sumHom {U V W Z : UniformObject P L} (f : U ⟶ W) (g : V ⟶ Z) :
    sum U V ⟶ sum W Z :=
  ⟨Labelled.sumHom f.arrow g.arrow,Labelled.arrowUniform_sum P f.uniform g.uniform⟩
noncomputable def assocHom (U V W : UniformObject P L) : sum (sum U V) W ⟶ sum U (sum V W) :=
  ⟨Labelled.assocHom U.obj V.obj W.obj,Labelled.assocHom_uniform P _ _ _⟩
noncomputable def leftHom (U : UniformObject P L) : sum empty U ⟶ U :=
  ⟨Labelled.leftHom U.obj,Labelled.leftHom_uniform P _⟩
noncomputable def rightHom (U : UniformObject P L) : sum U empty ⟶ U :=
  ⟨Labelled.rightHom U.obj,Labelled.rightHom_uniform P _⟩
noncomputable def swapHom (U V : UniformObject P L) : sum U V ⟶ sum V U :=
  ⟨Labelled.swapHom U.obj V.obj,Labelled.swapHom_uniform P _ _⟩

noncomputable instance instMonoidalCategoryStruct : MonoidalCategoryStruct (UniformObject P L) where
  tensorObj := sum
  tensorHom := sumHom
  whiskerLeft U _ _ f := sumHom (𝟙 U) f
  whiskerRight f U := sumHom f (𝟙 U)
  tensorUnit := empty
  associator U V W := asIso (assocHom U V W)
  leftUnitor U := asIso (leftHom U)
  rightUnitor U := asIso (rightHom U)

noncomputable def inducing : Monoidal.InducingFunctorData (forget (P:=P) (L:=L)) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  whiskerRight_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  tensorHom_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  associator_eq := by
    intro U V W
    change Labelled.assocHom U.obj V.obj W.obj =
      (𝟙 _ ≫ Labelled.sumHom (𝟙 _) (𝟙 _)) ≫ Labelled.assocHom U.obj V.obj W.obj ≫
        (Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _)
    simp only [Labelled.sumHom_id,Category.id_comp,Category.comp_id]
  leftUnitor_eq := by
    intro U
    change Labelled.leftHom U.obj = (𝟙 _ ≫ Labelled.sumHom (𝟙 _) (𝟙 _)) ≫ Labelled.leftHom U.obj
    rw [Labelled.sumHom_id,Category.id_comp,Category.id_comp]
  rightUnitor_eq := by
    intro U
    change Labelled.rightHom U.obj = (𝟙 _ ≫ Labelled.sumHom (𝟙 _) (𝟙 _)) ≫ Labelled.rightHom U.obj
    rw [Labelled.sumHom_id,Category.id_comp,Category.id_comp]

noncomputable instance instMonoidalCategory : MonoidalCategory (UniformObject P L) := Monoidal.induced forget inducing
noncomputable instance instMonoidalLabelledForget : (forget (P:=P) (L:=L)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (Monoidal.fromInducedCoreMonoidal forget inducing)

noncomputable instance instBraidedCategory : BraidedCategory (UniformObject P L) :=
  BraidedCategory.ofFaithful forget (fun U V => asIso (swapHom U V)) (by
    intro U V
    change (𝟙 _) ≫ Labelled.swapHom U.obj V.obj = Labelled.swapHom U.obj V.obj ≫ (𝟙 _)
    simp)
noncomputable instance instBraidedLabelledForget : (forget (P:=P) (L:=L)).Braided where
  braided U V := by
    change (𝟙 _) ≫ Labelled.swapHom U.obj V.obj = Labelled.swapHom U.obj V.obj ≫ (𝟙 _)
    simp
noncomputable instance instSymmetricCategory : SymmetricCategory (UniformObject P L) := SymmetricCategory.ofFaithful forget

end LabelledStage.UniformObject
end SimpleAmenable.PolygonObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageOrder
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace BooleanPartition
variable {a : ℕ}
def Refines (P Q : BooleanPartition a) : Prop :=
  ∀x y,Q.color x=Q.color y → P.color x=P.color y
lemma refines_refl (P : BooleanPartition a) : Refines P P := fun _ _ h => h
lemma refines_trans {P Q T : BooleanPartition a} (h : Refines P Q) (k : Refines Q T) :
    Refines P T := fun x y e => h x y (k x y e)
noncomputable def join (P Q : BooleanPartition a) : BooleanPartition a :=
  generated (Sum.elim P.cell Q.cell)
lemma le_join_left (P Q : BooleanPartition a) : Refines P (join P Q) := by
  intro x y h
  have e := generated_constant (Sum.elim P.cell Q.cell) h (Sum.inl (P.color x))
  exact ((e.mp rfl).symm)
lemma le_join_right (P Q : BooleanPartition a) : Refines Q (join P Q) := by
  intro x y h
  have e := generated_constant (Sum.elim P.cell Q.cell) h (Sum.inr (Q.color x))
  exact ((e.mp rfl).symm)
end BooleanPartition
namespace LabelledStage
abbrev ReducedLabel (n : ℕ) := {l : Fin n → CutRing × CutRing // ∀i,orbitRepresentative (l i)=l i}
structure Stage (a n : ℕ) where
  partition : BooleanPartition a
  support : Finset (ReducedLabel n)
namespace Stage
variable {a n : ℕ}
noncomputable def empty : Stage a n := ⟨BooleanPartition.generated (fun x : Fin 0 => Fin.elim0 x),∅⟩
instance instNonempty : Nonempty (Stage a n) := ⟨empty⟩
noncomputable instance instPreorder : Preorder (Stage a n) where
  le S T := S.partition.Refines T.partition ∧ S.support ⊆ T.support
  le_refl S := ⟨BooleanPartition.refines_refl _,Subset.rfl⟩
  le_trans S T U h k := ⟨BooleanPartition.refines_trans h.1 k.1,Subset.trans h.2 k.2⟩
noncomputable def sup (S T : Stage a n) : Stage a n :=
  ⟨S.partition.join T.partition,S.support ∪ T.support⟩
lemma le_sup_left (S T : Stage a n) : S ≤ sup S T :=
  ⟨BooleanPartition.le_join_left _ _,Finset.subset_union_left⟩
lemma le_sup_right (S T : Stage a n) : T ≤ sup S T :=
  ⟨BooleanPartition.le_join_right _ _,Finset.subset_union_right⟩
noncomputable instance instIsDirectedOrder : IsDirectedOrder (Stage a n) where
  directed S T := ⟨sup S T,le_sup_left S T,le_sup_right S T⟩
noncomputable instance instIsFiltered : IsFiltered (Stage a n) := inferInstance
noncomputable abbrev L (S : Stage a n) : Fin S.support.card → Fin n → CutRing × CutRing :=
  fun i => ((Fintype.equivFin S.support).symm (Fin.cast (by simp) i)).val.val
lemma L_reduced (S : Stage a n) : ∀j i,orbitRepresentative (S.L j i)=S.L j i :=
  fun j => ((Fintype.equivFin S.support).symm (Fin.cast (by simp) j)).val.property
lemma L_injective (S : Stage a n) : Function.Injective S.L := by
  intro i j h
  have h' := (Fintype.equivFin S.support).symm.injective (Subtype.ext (Subtype.ext h))
  exact Fin.ext (show i.val=j.val from congrArg (fun x : Fin (Fintype.card S.support) => x.val) h')
lemma label_mem (S : Stage a n) (l : Fin n → CutRing × CutRing) (hl : ∀i,orbitRepresentative (l i)=l i) :
    (∃j,S.L j=l) ↔ (⟨l,hl⟩ : ReducedLabel n)∈S.support := by
  constructor
  · rintro ⟨j,hj⟩
    have hm := ((Fintype.equivFin S.support).symm (Fin.cast (by simp) j)).property
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    exact Subtype.ext hj.symm
  · intro h
    refine ⟨Fin.cast (by simp) (Fintype.equivFin S.support ⟨⟨l,hl⟩,h⟩),?_⟩
    simp [L]
noncomputable abbrev Obj (S : Stage a n) := UniformObject S.partition S.L
noncomputable def inclusion {S T : Stage a n} (h : S≤T) : S.Obj ⥤ T.Obj where
  obj U := {
    obj := U.obj
    uniform := fun j x y hxy => U.uniform j x y (h.1 x y hxy)
    supported := fun j => (label_mem T _ (U.obj.reduced j)).mpr
      (h.2 ((label_mem S _ (U.obj.reduced j)).mp (U.supported j))) }
  map f := ⟨f.arrow,fun x y hxy hP => f.uniform x y hxy (h.1 _ _ hP)⟩
  map_id _ := rfl
  map_comp _ _ := rfl
lemma inclusion_id (S : Stage a n) : inclusion (le_refl S)=𝟭 S.Obj := by
  refine CategoryTheory.Functor.ext (fun U => ?_) ?_
  · cases U; rfl
  · intro X Y f; rfl
lemma inclusion_comp {S T U : Stage a n} (h : S≤T) (k : T≤U) :
    inclusion (h.trans k)=inclusion h ⋙ inclusion k := by
  refine CategoryTheory.Functor.ext (fun X => ?_) ?_
  · cases X; rfl
  · intro X Y f; rfl
end Stage
end LabelledStage
end SimpleAmenable.PolygonObject

end

section
open _root_.CategoryTheory Classical Set MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage

namespace Stage
variable {a n : ℕ}
noncomputable abbrev forget (S : Stage a n) : S.Obj ⥤ Labelled a n := UniformObject.forget
@[simp] lemma forget_ε (S : Stage a n) : Functor.LaxMonoidal.ε S.forget=𝟙 _ := rfl
@[simp] lemma forget_η (S : Stage a n) : Functor.OplaxMonoidal.η S.forget=𝟙 _ := rfl
@[simp] lemma forget_μ (S : Stage a n) (U V : S.Obj) : Functor.LaxMonoidal.μ S.forget U V=𝟙 _ := rfl
lemma forget_injective (S : Stage a n) : Function.Injective S.forget.obj := by
  intro U V h; cases U; cases V; cases h; rfl
lemma inclusion_forget {S T : Stage a n} (h : S≤T) : inclusion h ⋙ T.forget=S.forget := rfl

theorem exists_lift_family {κ τ : Type} [Fintype κ] [Fintype τ]
    (U : κ → Labelled a n) (src dst : τ → κ) (f : ∀t,U (src t) ⟶ U (dst t)) :
    ∃S : Stage a n, (∀k,Labelled.ObjectUniform S.partition (U k)) ∧
      (∀k j,∃l,S.L l=(U k).label j) ∧ (∀t,Labelled.ArrowUniform S.partition (f t)) := by
  obtain ⟨P,hP,hf⟩ := Labelled.exists_uniform_partition U src dst f
  let lab : (Σk,Fin (U k).polygon.tracks) → ReducedLabel n := fun kj =>
    ⟨(U kj.1).label kj.2,(U kj.1).reduced kj.2⟩
  let S : Stage a n := ⟨P,Finset.univ.image lab⟩
  refine ⟨S,hP,?_,hf⟩
  intro k j
  apply (label_mem S _ ((U k).reduced j)).mpr
  exact Finset.mem_image.mpr ⟨⟨k,j⟩,Finset.mem_univ _,rfl⟩

open IntervalBar IntervalBar.Diagram
end Stage
end SimpleAmenable.PolygonObject.LabelledStage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FiniteSetMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.FiniteSetGroupoid

abbrev toEquiv {U V : FiniteSetGroupoid} (f : U ⟶ V) : Fin U.size ≃ Fin V.size := f
instance instCoeFunHomForallFinSize {U V : FiniteSetGroupoid} : CoeFun (U ⟶ V) (fun _ => Fin U.size → Fin V.size) :=
  ⟨fun f => toEquiv f⟩
lemma hom_ext {U V : FiniteSetGroupoid} (f g : U ⟶ V) (h : ∀x,f x=g x) : f=g := Equiv.ext h
abbrev sum (U V : FiniteSetGroupoid) : FiniteSetGroupoid := ⟨U.size+V.size⟩
abbrev empty : FiniteSetGroupoid := ⟨0⟩
def sumEquiv (U V : FiniteSetGroupoid) : Fin U.size ⊕ Fin V.size ≃ Fin (sum U V).size :=
  finSumFinEquiv

def sumHom {U V W Z : FiniteSetGroupoid} (f : U ⟶ W) (g : V ⟶ Z) : sum U V ⟶ sum W Z :=
  (sumEquiv U V).symm.trans ((Equiv.sumCongr f g).trans (sumEquiv W Z))
def assoc (U V W : FiniteSetGroupoid) : sum (sum U V) W ⟶ sum U (sum V W) :=
  (sumEquiv (sum U V) W).symm.trans
    ((Equiv.sumCongr (sumEquiv U V).symm (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (Equiv.refl _) (sumEquiv V W)).trans (sumEquiv U (sum V W)))))
def swap (U V : FiniteSetGroupoid) : sum U V ⟶ sum V U :=
  (sumEquiv U V).symm.trans ((Equiv.sumComm _ _).trans (sumEquiv V U))
def left (U : FiniteSetGroupoid) : sum empty U ⟶ U :=
  (sumEquiv empty U).symm.trans (Equiv.emptySum _ _)
def right (U : FiniteSetGroupoid) : sum U empty ⟶ U :=
  (sumEquiv U empty).symm.trans (Equiv.sumEmpty _ _)
@[simp] lemma comp_eq {U V W : FiniteSetGroupoid} (f : U ⟶ V) (g : V ⟶ W) :
    (f≫g : U ⟶ W) = (toEquiv f).trans (toEquiv g) := rfl
@[simp] lemma id_eq (U : FiniteSetGroupoid) : (𝟙 U : U ⟶ U) = Equiv.refl _ := rfl
@[simp] lemma comp_apply {U V W : FiniteSetGroupoid} (f : U ⟶ V) (g : V ⟶ W) (x : Fin U.size) :
    (f≫g) x=g (f x) := rfl
@[simp] lemma id_apply (U : FiniteSetGroupoid) (x : Fin U.size) : (𝟙 U : U ⟶ U) x=x := rfl
@[simp] lemma sumHom_inl {U V W Z : FiniteSetGroupoid} (f : U ⟶ W) (g : V ⟶ Z) (x : Fin U.size) :
    sumHom f g (sumEquiv U V (.inl x))=sumEquiv W Z (.inl (f x)) := by simp [sumHom]
@[simp] lemma sumHom_inr {U V W Z : FiniteSetGroupoid} (f : U ⟶ W) (g : V ⟶ Z) (x : Fin V.size) :
    sumHom f g (sumEquiv U V (.inr x))=sumEquiv W Z (.inr (g x)) := by simp [sumHom]
@[simp] lemma assoc_left (U V W : FiniteSetGroupoid) (x : Fin U.size) :
    assoc U V W (sumEquiv (sum U V) W (.inl (sumEquiv U V (.inl x))))=
      sumEquiv U (sum V W) (.inl x) := by simp [assoc]
@[simp] lemma assoc_mid (U V W : FiniteSetGroupoid) (x : Fin V.size) :
    assoc U V W (sumEquiv (sum U V) W (.inl (sumEquiv U V (.inr x))))=
      sumEquiv U (sum V W) (.inr (sumEquiv V W (.inl x))) := by simp [assoc]
@[simp] lemma assoc_right (U V W : FiniteSetGroupoid) (x : Fin W.size) :
    assoc U V W (sumEquiv (sum U V) W (.inr x))=
      sumEquiv U (sum V W) (.inr (sumEquiv V W (.inr x))) := by simp [assoc]
@[simp] lemma swap_left (U V : FiniteSetGroupoid) (x : Fin U.size) :
    swap U V (sumEquiv U V (.inl x))=sumEquiv V U (.inr x) := by simp [swap]
@[simp] lemma swap_right (U V : FiniteSetGroupoid) (x : Fin V.size) :
    swap U V (sumEquiv U V (.inr x))=sumEquiv V U (.inl x) := by simp [swap]
@[simp] lemma left_apply (U : FiniteSetGroupoid) (x : Fin U.size) :
    left U (sumEquiv empty U (.inr x))=x := by simp [left]
@[simp] lemma right_apply (U : FiniteSetGroupoid) (x : Fin U.size) :
    right U (sumEquiv U empty (.inl x))=x := by simp [right]
lemma sumHom_id (U V : FiniteSetGroupoid) : sumHom (𝟙 U) (𝟙 V)=𝟙 (sum U V) := by
  apply hom_ext; intro x
  obtain ⟨x,rfl⟩ := (sumEquiv U V).surjective x
  cases x <;> simp [toEquiv,sumHom]
lemma sumHom_comp {U V W X Y Z : FiniteSetGroupoid} (f : U ⟶ V) (f' : V ⟶ W)
    (g : X ⟶ Y) (g' : Y ⟶ Z) : sumHom (f≫f') (g≫g')=sumHom f g ≫ sumHom f' g' := by
  apply hom_ext; intro x
  obtain ⟨x,rfl⟩ := (sumEquiv U X).surjective x
  cases x <;> simp [toEquiv,sumHom]

noncomputable abbrev monoidalStruct : MonoidalCategoryStruct FiniteSetGroupoid where
  tensorObj := sum
  tensorHom := sumHom
  whiskerLeft U _ _ f := sumHom (𝟙 U) f
  whiskerRight f U := sumHom f (𝟙 U)
  tensorUnit := empty
  associator U V W := asIso (assoc U V W)
  leftUnitor U := asIso (left U)
  rightUnitor U := asIso (right U)

attribute [instance] monoidalStruct

noncomputable instance monoidal : MonoidalCategory FiniteSetGroupoid :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := sumHom_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' => (sumHom_comp f f' g g').symm)
    (associator_naturality := by
      intro U V W U' V' W' f g h
      change sumHom (sumHom f g) h ≫ assoc U' V' W' = assoc U V W ≫ sumHom f (sumHom g h)
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv (sum U V) W).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumEquiv U V).surjective y
        cases z <;> simp [toEquiv,sumHom,assoc]
      | inr y => simp [toEquiv,sumHom,assoc])
    (leftUnitor_naturality := by
      intro U V f
      change sumHom (𝟙 empty) f ≫ left V = left U ≫ f
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv empty U).surjective x
      cases y with
      | inl y => exact isEmptyElim y
      | inr y => simp [toEquiv,sumHom,left])
    (rightUnitor_naturality := by
      intro U V f
      change sumHom f (𝟙 empty) ≫ right V = right U ≫ f
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv U empty).surjective x
      cases y with
      | inl y => simp [toEquiv,sumHom,right]
      | inr y => exact isEmptyElim y)
    (pentagon := by
      intro U V W Z
      change sumHom (assoc U V W) (𝟙 Z) ≫ assoc U (sum V W) Z ≫ sumHom (𝟙 U) (assoc V W Z) =
        assoc (sum U V) W Z ≫ assoc U V (sum W Z)
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv (sum (sum U V) W) Z).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumEquiv (sum U V) W).surjective y
        cases z with
        | inl z =>
          obtain ⟨t,rfl⟩ := (sumEquiv U V).surjective z
          cases t <;> simp [toEquiv,sumHom,assoc]
        | inr z => simp [toEquiv,sumHom,assoc]
      | inr y => simp [toEquiv,sumHom,assoc])
    (triangle := by
      intro U V
      change assoc U empty V ≫ sumHom (𝟙 U) (left V) = sumHom (right U) (𝟙 V)
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv (sum U empty) V).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumEquiv U empty).surjective y
        cases z with
        | inl z => simp [toEquiv,sumHom,assoc,left,right]
        | inr z => exact isEmptyElim z
      | inr y => simp [toEquiv,sumHom,assoc,left,right])

@[simp] theorem assoc_symm_left (U V W : FiniteSetGroupoid) (x : Fin U.size) :
    (toEquiv (assoc U V W)).symm (sumEquiv U (sum V W) (.inl x))=
      sumEquiv (sum U V) W (.inl (sumEquiv U V (.inl x))) :=
  (Equiv.symm_apply_eq _).mpr (assoc_left U V W x).symm
@[simp] theorem assoc_symm_mid (U V W : FiniteSetGroupoid) (x : Fin V.size) :
    (toEquiv (assoc U V W)).symm (sumEquiv U (sum V W) (.inr (sumEquiv V W (.inl x))))=
      sumEquiv (sum U V) W (.inl (sumEquiv U V (.inr x))) :=
  (Equiv.symm_apply_eq _).mpr (assoc_mid U V W x).symm
@[simp] theorem assoc_symm_right (U V W : FiniteSetGroupoid) (x : Fin W.size) :
    (toEquiv (assoc U V W)).symm (sumEquiv U (sum V W) (.inr (sumEquiv V W (.inr x))))=
      sumEquiv (sum U V) W (.inr x) :=
  (Equiv.symm_apply_eq _).mpr (assoc_right U V W x).symm

@[simp] theorem associator_inv_apply (U V W : FiniteSetGroupoid) (x : Fin (sum U (sum V W)).size) :
    (monoidalStruct.associator U V W).inv x=(toEquiv (assoc U V W)).symm x := by
  change (CategoryTheory.inv (assoc U V W)) x=_
  rw [← Groupoid.inv_eq_inv]
  rfl

@[simp] theorem inv_arrow_apply {U V : FiniteSetGroupoid} (f : U ⟶ V) (x : Fin V.size) :
    (CategoryTheory.inv f) x = (toEquiv f).symm x := by
  rw [← Groupoid.inv_eq_inv]
  rfl

@[simp] lemma inv_eq {U V : FiniteSetGroupoid} (f : U ⟶ V) :
    (CategoryTheory.inv f : V ⟶ U) = (toEquiv f).symm := by
  rw [← Groupoid.inv_eq_inv]
  rfl

noncomputable instance braided : BraidedCategory FiniteSetGroupoid where
  braiding U V := asIso (swap U V)
  braiding_naturality_right := by
    intro U V W f
    change sumHom (𝟙 U) f ≫ swap U W = swap U V ≫ sumHom f (𝟙 U)
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv U V).surjective x
    cases y <;> simp [toEquiv,sumHom,swap]
  braiding_naturality_left := by
    intro U V f W
    change sumHom f (𝟙 W) ≫ swap V W = swap U W ≫ sumHom (𝟙 W) f
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv U W).surjective x
    cases y <;> simp [toEquiv,sumHom,swap]
  hexagon_forward := by
    intro U V W
    change assoc U V W ≫ swap U (sum V W) ≫ assoc V W U =
      sumHom (swap U V) (𝟙 W) ≫ assoc V U W ≫ sumHom (𝟙 V) (swap U W)
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv (sum U V) W).surjective x
    cases y with
    | inl y =>
      obtain ⟨z,rfl⟩ := (sumEquiv U V).surjective y
      cases z <;> simp [toEquiv,sumHom,assoc,swap]
    | inr y => simp [toEquiv,sumHom,assoc,swap]
  hexagon_reverse := by
    intro U V W
    change (CategoryTheory.inv (assoc U V W)) ≫ swap (sum U V) W ≫ (CategoryTheory.inv (assoc W U V)) =
      sumHom (𝟙 U) (swap V W) ≫ (CategoryTheory.inv (assoc U W V)) ≫ sumHom (swap U W) (𝟙 V)
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv U (sum V W)).surjective x
    cases y with
    | inl y => simp [toEquiv,sumHom,assoc,swap]
    | inr y =>
      obtain ⟨z,rfl⟩ := (sumEquiv V W).surjective y
      cases z <;> simp [toEquiv,sumHom,assoc,swap]

noncomputable instance symmetric : SymmetricCategory FiniteSetGroupoid where
  symmetry U V := by
    change swap U V ≫ swap V U = 𝟙 (sum U V)
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv U V).surjective x
    cases y <;> simp [toEquiv,swap]

end SimpleAmenable.PolygonObject.FiniteSetGroupoid

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_CellFunctor
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.Cell

variable {a n : ℕ} (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n)

noncomputable abbrev object (U : FiniteSetGroupoid) : Labelled a n :=
  ⟨⟨U.size,fun _ => P⟩,fun _ => l.val,fun _ => l.property⟩
noncomputable def pointMap {U V : FiniteSetGroupoid} (f : U ⟶ V) :
    (object P l U).polygon.Point ≃ (object P l V).polygon.Point where
  toFun x := ⟨(f x.val.1,x.val.2),x.property⟩
  invFun y := ⟨(f.symm y.val.1,y.val.2),y.property⟩
  left_inv x := by apply Subtype.ext; exact Prod.ext (f.symm_apply_apply _) rfl
  right_inv y := by apply Subtype.ext; exact Prod.ext (f.apply_symm_apply _) rfl
noncomputable def arrow {U V : FiniteSetGroupoid} (f : U ⟶ V) : object P l U ⟶ object P l V where
  arrow := relabelArrow (pointMap P l f) f (fun _ => rfl)
  positional _ := rfl
  labelled _ := rfl
noncomputable def functor : FiniteSetGroupoid ⥤ Labelled a n where
  obj := object P l
  map := arrow P l
  map_id _ := by apply Hom.ext; apply Arrow.ext; apply Equiv.ext; intro x; rfl
  map_comp _ _ := by apply Hom.ext; apply Arrow.ext; apply Equiv.ext; intro x; rfl
@[simp] lemma arrow_apply {U V : FiniteSetGroupoid} (f : U ⟶ V)
    (x : (object P l U).polygon.Point) :
    ((arrow P l f).arrow.toEquiv x).val = (f x.val.1,x.val.2) := rfl

noncomputable def tensorPoint (U V : FiniteSetGroupoid) :
    (sum (object P l U) (object P l V)).polygon.Point ≃ (object P l (U⊗V)).polygon.Point where
  toFun x := ⟨x.val,by
    obtain ⟨y,rfl⟩ := (sumPointEquiv (object P l U).polygon (object P l V).polygon).surjective x
    cases y with
    | inl y => simpa only [sumPointEquiv_inl,object] using y.property
    | inr y => simpa only [sumPointEquiv_inr,object] using y.property⟩
  invFun x := ⟨x.val,by
    change x.val.2 ∈ (Fin.addCases (motive := fun _ => polygonAlgebra a)
      (fun _ => P) (fun _ => P) x.val.1).val
    refine Fin.addCases (motive := fun i => x.val.2 ∈ (Fin.addCases
      (motive := fun _ => polygonAlgebra a) (fun _ => P) (fun _ => P) i).val)
      (fun i => ?_) (fun i => ?_) x.val.1
    · simpa only [Fin.addCases_left,object] using x.property
    · simpa only [Fin.addCases_right,object] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def tensorArrow (U V : FiniteSetGroupoid) :
    (object P l U) ⊗ (object P l V) ⟶ object P l (U⊗V) where
  arrow := relabelArrow (tensorPoint P l U V) id (fun _ => rfl)
  positional _ := rfl
  labelled x := by
    change l.val = Fin.addCases (fun _ => l.val) (fun _ => l.val) x.val.1
    refine Fin.addCases (motive := fun i => l.val = Fin.addCases
      (motive := fun _ => Fin n → CutRing × CutRing) (fun _ => l.val) (fun _ => l.val) i)
      (fun i => ?_) (fun i => ?_) x.val.1
    · simp only [Fin.addCases_left]
    · simp only [Fin.addCases_right]
@[simp] lemma tensorArrow_apply (U V : FiniteSetGroupoid)
    (x : (sum (object P l U) (object P l V)).polygon.Point) :
    ((tensorArrow P l U V).arrow.toEquiv x).val=x.val := rfl
noncomputable def unitArrow : 𝟙_ (Labelled a n) ⟶ object P l (𝟙_ FiniteSetGroupoid) where
  arrow := relabelArrow {
    toFun x := Fin.elim0 x.val.1
    invFun x := Fin.elim0 x.val.1
    left_inv x := Fin.elim0 x.val.1
    right_inv x := Fin.elim0 x.val.1 } Fin.elim0 (fun x => Fin.elim0 x.val.1)
  positional x := Fin.elim0 x.val.1
  labelled x := Fin.elim0 x.val.1

end SimpleAmenable.PolygonObject.Labelled.Cell

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_LabelRelabel
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled

variable {a n m : ℕ}
abbrev Reduced (g : Fin n → CutRing × CutRing) : Prop :=
  ∀ i, orbitRepresentative (g i)=g i
variable (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
  (hf : ∀g, Reduced g → Reduced (f g))
noncomputable def relabel : Labelled a n ⥤ Labelled a m where
  obj U := ⟨U.polygon,fun k => f (U.label k),fun k => hf _ (U.reduced k)⟩
  map g := ⟨g.arrow,g.positional,fun x => congrArg f (g.labelled x)⟩
  map_id _ := Hom.ext _ _ rfl
  map_comp _ _ := Hom.ext _ _ rfl
noncomputable def relabelUnit : 𝟙_ (Labelled a m) ⟶ (relabel f hf).obj (𝟙_ (Labelled a n)) where
  arrow := 𝟙 _
  positional _ := rfl
  labelled x := by
    change Point PolygonObject.empty at x
    exact isEmptyElim x
noncomputable def relabelTensor (U V : Labelled a n) :
    (relabel f hf).obj U ⊗ (relabel f hf).obj V ⟶ (relabel f hf).obj (U ⊗ V) where
  arrow := 𝟙 _
  positional _ := rfl
  labelled x := by
    change f ((sum U V).label x.val.1) =
      (sum ((relabel f hf).obj U) ((relabel f hf).obj V)).label x.val.1
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
    cases y <;> simp only [relabel,sumPointEquiv_inl,sumPointEquiv_inr,Fin.addCases_left,Fin.addCases_right]
noncomputable instance relabelMonoidal : (relabel (a:=a) f hf).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso (relabelUnit f hf)
    μIso U V := asIso (relabelTensor f hf U V)
    μIso_hom_natural_left := by
      intros; apply Hom.ext
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Category.comp_id]
      rfl
    μIso_hom_natural_right := by
      intros; apply Hom.ext
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Category.comp_id]
      rfl
    associativity := by
      intros; apply Hom.ext
      change sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ _ = _ ≫ sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _
      simp only [sumArrow_id,Category.id_comp,Category.comp_id]
      rfl
    left_unitality := by
      intros; apply Hom.ext
      change _ = sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ _
      simp only [sumArrow_id,Category.id_comp]
      rfl
    right_unitality := by
      intros; apply Hom.ext
      change _ = sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ _
      simp only [sumArrow_id,Category.id_comp]
      rfl }
noncomputable instance relabelBraided : (relabel (a:=a) f hf).Braided where
  braided U V := by
    apply Hom.ext
    change 𝟙 _ ≫ sumSwap U.polygon V.polygon = sumSwap U.polygon V.polygon ≫ 𝟙 _
    simp only [Category.id_comp,Category.comp_id]
@[simp] lemma relabel_map_arrow {U V : Labelled a n} (g:U⟶V) :
    ((relabel f hf).map g).arrow=g.arrow := rfl
@[simp] lemma relabel_ε_arrow : (Functor.LaxMonoidal.ε (relabel (a:=a) f hf)).arrow=𝟙 _ := rfl
@[simp] lemma relabel_μ_arrow (U V : Labelled a n) :
    (Functor.LaxMonoidal.μ (relabel f hf) U V).arrow=𝟙 _ := rfl
end SimpleAmenable.PolygonObject.Labelled

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_CellMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.Cell

variable {a n : ℕ} (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n)
lemma track_ext {U V : Labelled a n} (f g : U ⟶ V)
    (h : ∀x, (f.arrow.toEquiv x).val.1=(g.arrow.toEquiv x).val.1) : f=g := by
  apply Hom.ext; apply Arrow.ext; apply Equiv.ext; intro x
  apply Subtype.ext; exact Prod.ext (h x) ((f.positional x).trans (g.positional x).symm)

@[simp] lemma whiskerRight_arrow {U V : Labelled a n} (f : U ⟶ V) (W : Labelled a n) :
    (f ▷ W).arrow=sumArrow f.arrow (𝟙 W.polygon) := rfl
@[simp] lemma whiskerLeft_arrow (W : Labelled a n) {U V : Labelled a n} (f : U ⟶ V) :
    (W ◁ f).arrow=sumArrow (𝟙 W.polygon) f.arrow := rfl

lemma tensor_natural {U V W X : FiniteSetGroupoid} (f : U ⟶ W) (g : V ⟶ X) :
    sumHom (arrow P l f) (arrow P l g) ≫ tensorArrow P l W X =
      tensorArrow P l U V ≫ arrow P l (FiniteSetGroupoid.sumHom f g) := by
  apply track_ext; intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv (object P l U).polygon (object P l V).polygon).surjective x
  cases y with
  | inl y =>
    change ((sumArrow (arrow P l f).arrow (arrow P l g).arrow).toEquiv (sumPointEquiv _ _ (.inl y))).val.1 =
      FiniteSetGroupoid.sumHom f g (FiniteSetGroupoid.sumEquiv U V (.inl y.val.1))
    erw [sumArrow_inl,sumPointEquiv_inl,FiniteSetGroupoid.sumHom_inl]
    rfl
  | inr y =>
    change ((sumArrow (arrow P l f).arrow (arrow P l g).arrow).toEquiv (sumPointEquiv _ _ (.inr y))).val.1 =
      FiniteSetGroupoid.sumHom f g (FiniteSetGroupoid.sumEquiv U V (.inr y.val.1))
    erw [sumArrow_inr,sumPointEquiv_inr,FiniteSetGroupoid.sumHom_inr]
    rfl

lemma tensor_assoc (U V W : FiniteSetGroupoid) :
    tensorArrow P l U V ▷ object P l W ≫ tensorArrow P l (U⊗V) W ≫
        (functor P l).map (α_ U V W).hom =
      (α_ (object P l U) (object P l V) (object P l W)).hom ≫
        object P l U ◁ tensorArrow P l V W ≫ tensorArrow P l U (V⊗W) := by
  apply track_ext; intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv (sum (object P l U) (object P l V)).polygon (object P l W).polygon).surjective x
  cases y with
  | inl y =>
    obtain ⟨z,rfl⟩ := (sumPointEquiv (object P l U).polygon (object P l V).polygon).surjective y
    cases z with
    | inl z =>
      change FiniteSetGroupoid.assoc U V W _ =
        ((sumArrow (𝟙 (object P l U).polygon) (tensorArrow P l V W).arrow).toEquiv ((sumAssoc (object P l U).polygon (object P l V).polygon (object P l W).polygon).toEquiv _)).val.1
      rw [whiskerRight_arrow,sumAssoc_apply,sumAssocEquiv_left]
      erw [tensorArrow_apply,sumArrow_inl,sumPointEquiv_inl,tensorArrow_apply,
        sumPointEquiv_inl,sumArrow_inl,sumPointEquiv_inl,arrow_id_apply]
      change FiniteSetGroupoid.assoc U V W
        (FiniteSetGroupoid.sumEquiv (U⊗V) W (.inl (FiniteSetGroupoid.sumEquiv U V (.inl z.val.1)))) = _
      erw [FiniteSetGroupoid.assoc_left]
      rfl
    | inr z =>
      change FiniteSetGroupoid.assoc U V W _ =
        ((sumArrow (𝟙 (object P l U).polygon) (tensorArrow P l V W).arrow).toEquiv ((sumAssoc (object P l U).polygon (object P l V).polygon (object P l W).polygon).toEquiv _)).val.1
      rw [whiskerRight_arrow,sumAssoc_apply,sumAssocEquiv_mid]
      erw [tensorArrow_apply,sumArrow_inl,sumPointEquiv_inl,tensorArrow_apply,
        sumPointEquiv_inr,sumArrow_inr,sumPointEquiv_inr,tensorArrow_apply,sumPointEquiv_inl]
      change FiniteSetGroupoid.assoc U V W
        (FiniteSetGroupoid.sumEquiv (U⊗V) W (.inl (FiniteSetGroupoid.sumEquiv U V (.inr z.val.1)))) = _
      erw [FiniteSetGroupoid.assoc_mid]
      rfl
  | inr y =>
    change FiniteSetGroupoid.assoc U V W _ =
      ((sumArrow (𝟙 (object P l U).polygon) (tensorArrow P l V W).arrow).toEquiv ((sumAssoc (object P l U).polygon (object P l V).polygon (object P l W).polygon).toEquiv _)).val.1
    rw [whiskerRight_arrow,sumAssoc_apply,sumAssocEquiv_right]
    erw [tensorArrow_apply,sumArrow_inr,sumPointEquiv_inr,arrow_id_apply,
      sumArrow_inr,sumPointEquiv_inr,tensorArrow_apply,sumPointEquiv_inr]
    change FiniteSetGroupoid.assoc U V W
      (FiniteSetGroupoid.sumEquiv (U⊗V) W (.inr y.val.1)) = _
    erw [FiniteSetGroupoid.assoc_right]
    rfl

lemma unit_left (U : FiniteSetGroupoid) :
    (λ_ (object P l U)).hom = unitArrow P l ▷ object P l U ≫
      tensorArrow P l (𝟙_ _) U ≫ (functor P l).map (λ_ U).hom := by
  apply track_ext; intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv PolygonObject.empty (object P l U).polygon).surjective x
  cases y with
  | inl y => exact isEmptyElim y
  | inr y =>
    change ((leftUnit _).toEquiv (sumPointEquiv _ _ (.inr y))).val.1 = FiniteSetGroupoid.left U _
    simp only [leftUnit_apply,leftUnitEquiv_apply]
    change y.val.1 = FiniteSetGroupoid.left U
      ((sumArrow (unitArrow P l).arrow (𝟙 (object P l U).polygon)).toEquiv
        (sumPointEquiv PolygonObject.empty (object P l U).polygon (.inr y))).val.1
    erw [sumArrow_inr,arrow_id_apply,sumPointEquiv_inr]
    change y.val.1 = FiniteSetGroupoid.left U (FiniteSetGroupoid.sumEquiv _ _ (.inr y.val.1))
    rw [FiniteSetGroupoid.left_apply]
lemma unit_right (U : FiniteSetGroupoid) :
    (ρ_ (object P l U)).hom = object P l U ◁ unitArrow P l ≫
      tensorArrow P l U (𝟙_ _) ≫ (functor P l).map (ρ_ U).hom := by
  apply track_ext; intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv (object P l U).polygon PolygonObject.empty).surjective x
  cases y with
  | inl y =>
    change ((rightUnit _).toEquiv (sumPointEquiv _ _ (.inl y))).val.1 = FiniteSetGroupoid.right U _
    simp only [rightUnit_apply,rightUnitEquiv_apply]
    change y.val.1 = FiniteSetGroupoid.right U
      ((sumArrow (𝟙 (object P l U).polygon) (unitArrow P l).arrow).toEquiv
        (sumPointEquiv (object P l U).polygon PolygonObject.empty (.inl y))).val.1
    erw [sumArrow_inl,arrow_id_apply,sumPointEquiv_inl]
    change y.val.1 = FiniteSetGroupoid.right U (FiniteSetGroupoid.sumEquiv _ _ (.inl y.val.1))
    rw [FiniteSetGroupoid.right_apply]
  | inr y => exact isEmptyElim y

noncomputable instance cellMonoidal : (functor P l).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso (X := 𝟙_ (Labelled a n))
      (Y := object P l (𝟙_ FiniteSetGroupoid)) (unitArrow P l)
    μIso U V := asIso (X := object P l U ⊗ object P l V)
      (Y := object P l (U ⊗ V)) (tensorArrow P l U V)
    μIso_hom_natural_left := by
      intro U V f W
      have h := tensor_natural P l f (𝟙 W)
      rw [show arrow P l (𝟙 W)=𝟙 _ from (functor P l).map_id W] at h
      exact h
    μIso_hom_natural_right := by
      intro U V W f
      have h := tensor_natural P l (𝟙 W) f
      rw [show arrow P l (𝟙 W)=𝟙 _ from (functor P l).map_id W] at h
      exact h
    associativity := tensor_assoc P l
    left_unitality := unit_left P l
    right_unitality := unit_right P l }
noncomputable instance cellBraided : (functor P l).Braided where
  braided U V := by
    apply track_ext; intro x
    change FiniteSetGroupoid.swap U V x.val.1 =
      ((sumSwap (object P l U).polygon (object P l V).polygon).toEquiv x).val.1
    obtain ⟨y,rfl⟩ := (sumPointEquiv (object P l U).polygon (object P l V).polygon).surjective x
    cases y with
    | inl y =>
      rw [sumSwap_apply,sumSwapEquiv_inl,sumPointEquiv_inl,sumPointEquiv_inr]
      exact FiniteSetGroupoid.swap_left U V y.val.1
    | inr y =>
      rw [sumSwap_apply,sumSwapEquiv_inr,sumPointEquiv_inr,sumPointEquiv_inl]
      exact FiniteSetGroupoid.swap_right U V y.val.1
end SimpleAmenable.PolygonObject.Labelled.Cell

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_CellRelabel
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.Cell

variable {a n m : ℕ}
variable (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
  (hf : ∀g, Reduced g → Reduced (f g))
variable (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n)
noncomputable def relabelIso :
    functor P l ⋙ relabel f hf ≅ functor P ⟨f l.val,hf l.val l.property⟩ :=
  NatIso.ofComponents (fun U => asIso (X := (relabel f hf).obj (object P l U))
    (Y := object P ⟨f l.val,hf l.val l.property⟩ U)
    { arrow := 𝟙 _
      positional _ := rfl
      labelled _ := rfl }) (by
    intro U V g
    apply Hom.ext
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id]
    rfl)
noncomputable instance relabelIsoMonoidal : NatTrans.IsMonoidal (relabelIso f hf P l).hom where
  unit := by
    apply Hom.ext
    change (𝟙 _ ≫ (unitArrow P l).arrow) ≫ 𝟙 _ = (unitArrow P ⟨f l.val,hf l.val l.property⟩).arrow
    simp only [Category.id_comp,Category.comp_id]
    rfl
  tensor U V := by
    apply Hom.ext
    change (𝟙 _ ≫ (tensorArrow P l U V).arrow) ≫ 𝟙 _ =
      sumArrow (𝟙 _) (𝟙 _) ≫ (tensorArrow P ⟨f l.val,hf l.val l.property⟩ U V).arrow
    simp only [Category.id_comp,Category.comp_id,sumArrow_id]
    rfl
end SimpleAmenable.PolygonObject.Labelled.Cell

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneStepFunctions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

namespace PlaneStep
variable {a : ℕ}

noncomputable def representation (a : ℕ) :
    Representation ℤ (Multiplicative (CutRing × CutRing)) (PlaneStep a) where
  toFun u := translate u.toAdd
  map_one' := by
    ext f p
    simp [translate]
  map_mul' u v := by
    ext f p
    change f.val (GenericPlane.shift (-(u.toAdd+v.toAdd)) p)=
      f.val (GenericPlane.shift (-v.toAdd) (GenericPlane.shift (-u.toAdd) p))
    rw [GenericPlane.shift_add]
    abel_nf

end PlaneStep

abbrev PolygonGroupRing := MonoidAlgebra ℤ (Multiplicative (CutRing × CutRing))

end PlaneStepFunctions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonArea
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonArea
open Classical Set MeasureTheory

local instance localInst_r2c5f9e_1 : Countable CutRing :=
  (QuadraticAlgebra.equivProd (1 : ℤ) 1).injective.countable
theorem measurableSet_avoidsCuts (a : ℕ) : MeasurableSet {p : ℝ×ℝ | AvoidsCuts a p} := by
  change MeasurableSet {p | ∀j z,cutForm a j p≠ordinary z}
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro z
  exact ((continuous_cutForm a j).measurable (measurableSet_singleton (ordinary z))).compl

theorem ae_avoidsCuts (a : ℕ) : ∀ᵐp : ℝ×ℝ, AvoidsCuts a p := by
  rw [ae_iff]
  have he : {p : ℝ×ℝ | ¬AvoidsCuts a p}=⋃j : Fin 4,⋃z : CutRing,{p | cutForm a j p=ordinary z} := by
    ext p
    simp [AvoidsCuts]
  rw [he]
  exact measure_iUnion_null (fun j => measure_iUnion_null (fun z => volume_cut_level a j (ordinary z)))

theorem volume_genericSquare (a : ℕ) :
    volume {p : ℝ×ℝ | p.1∈Ico 0 1 ∧ p.2∈Ico 0 1 ∧ AvoidsCuts a p}=1 := by
  have he : {p : ℝ×ℝ | p.1∈Ico 0 1 ∧ p.2∈Ico 0 1 ∧ AvoidsCuts a p}
      =ᵐ[volume] (Ico (0:ℝ) 1)×ˢ(Ico (0:ℝ) 1) := by
    filter_upwards [ae_avoidsCuts a] with p hp
    apply propext
    change (p.1∈Ico 0 1 ∧ p.2∈Ico 0 1 ∧ AvoidsCuts a p) ↔
      (p.1∈Ico 0 1 ∧ p.2∈Ico 0 1)
    simp only [hp,and_true]
  rw [measure_congr he]
  change ((volume : Measure ℝ).prod volume) (Ico 0 1 ×ˢ Ico 0 1)=1
  rw [Measure.prod_prod]
  simp

end PolygonArea

section PolygonJordan
open Classical Set MeasureTheory
namespace PolygonArea

theorem area_eq_rep {a : ℕ} (U : polygonAlgebra a) {S : Set (ℝ×ℝ)}
    (hS : S⊆square) (he : ∀x : GenericSquare a,x∈U.val ↔ x.val∈S) : area U=volume S := by
  rw [area,image_eq_rep U hS he]
  apply measure_congr
  filter_upwards [ae_avoidsCuts a] with p hp
  apply propext
  exact ⟨And.left,fun h => ⟨h,hp⟩⟩

theorem measurable_image {a : ℕ} (U : polygonAlgebra a) :
    MeasurableSet (Subtype.val '' U.val) := by
  obtain ⟨S,hS,hm,hn,he⟩ := representative U.property
  rw [image_eq_rep U hS he]
  exact hm.inter (measurableSet_avoidsCuts a)

theorem area_le_one {a : ℕ} (U : polygonAlgebra a) : area U≤1 := by
  obtain ⟨S,hS,hm,hn,he⟩ := representative U.property
  rw [area_eq_rep U hS he]
  calc
    volume S≤volume square := measure_mono hS
    _=1 := by change ((volume : Measure ℝ).prod volume) (Ico 0 1 ×ˢ Ico 0 1)=1; simp

theorem area_top (a : ℕ) : area (⊤ : polygonAlgebra a)=1 := by
  change volume (Subtype.val '' (⊤ : polygonAlgebra a).val)=1
  have he : Subtype.val '' (⊤ : polygonAlgebra a).val=
      {p : ℝ×ℝ | p.1∈Ico 0 1 ∧ p.2∈Ico 0 1 ∧ AvoidsCuts a p} := by
    ext p
    constructor
    · rintro ⟨x,-,rfl⟩; exact x.property
    · intro h; exact ⟨⟨p,h⟩,by trivial,rfl⟩
  rw [he]
  exact volume_genericSquare a

end PolygonArea
end PolygonJordan

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonAreaAlgebra
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonAreaAlgebra

open Classical Set MeasureTheory
namespace PolygonArea

theorem area_eq_sum {a : ℕ} {ι : Type*} [Fintype ι] (U : polygonAlgebra a)
    (f : ι → polygonAlgebra a) (he : U.val=⋃i,(f i).val)
    (hd : Pairwise (fun i j => Disjoint (f i).val (f j).val)) :
    area U=∑i,area (f i) := by
  have hd' : Pairwise (fun i j =>
      Disjoint ((fun point : GenericSquare a => point.val) '' (f i).val)
        ((fun point : GenericSquare a => point.val) '' (f j).val)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,hyx⟩
    have : y=x := Subtype.ext hyx
    exact Set.disjoint_left.mp (hd hij) hx (by simpa only [this] using hy)
  change volume ((fun point : GenericSquare a => point.val) '' U.val)=_
  rw [he,Set.image_iUnion,measure_iUnion hd' (fun i => measurable_image (f i)),tsum_fintype]
  rfl

theorem area_sup_add_inf {a : ℕ} (U V : polygonAlgebra a) :
    area (U⊔V)+area (U⊓V)=area U+area V := by
  change volume ((fun point : GenericSquare a => point.val) '' (U.val∪V.val))+
    volume ((fun point : GenericSquare a => point.val) '' (U.val∩V.val))=_
  rw [Set.image_union,Set.image_inter (f := fun point : GenericSquare a => point.val)
    Subtype.val_injective]
  exact measure_union_add_inter _ (measurable_image V)

theorem area_compl {a : ℕ} (U : polygonAlgebra a) : area U+area Uᶜ=1 := by
  have h := area_sup_add_inf U Uᶜ
  simpa only [sup_compl_eq_top,inf_compl_eq_bot,area_top,area_bot,add_zero] using h.symm

theorem area_translation_wrap {a : ℕ} (u : CutRing×CutRing) (k : ℤ×ℤ)
    (U : polygonAlgebra a) (hU : U.val⊆wrapCell a u k) :
    area (translatedPolygon u U)=area U := by
  let v : ℝ×ℝ := (ordinary (u.1-(k.1:CutRing)),ordinary (u.2-(k.2:CutRing)))
  have he : Subtype.val '' (translatedPolygon u U).val=
      (fun p : ℝ×ℝ => p+v) '' (Subtype.val '' U.val) := by
    ext p
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x.val,⟨x,hx,rfl⟩,(translate_on_wrap u k (hU hx)).symm⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨translate a u x,⟨x,hx,rfl⟩,translate_on_wrap u k (hU hx)⟩
  change volume (Subtype.val '' (translatedPolygon u U).val)=_
  rw [he,Set.image_add_right,measure_preimage_add_right]
  rfl

theorem area_translation {a : ℕ} (u : CutRing×CutRing) (U : polygonAlgebra a) :
    area (translatedPolygon u U)=area U := by
  let W (k : wrapIndices u) : polygonAlgebra a :=
    U ⊓ ⟨wrapCell a u k.val,wrapCell_mem a u k.val⟩
  have hcov : U.val=⋃k,(W k).val := by
    ext x
    constructor
    · intro hx
      let k : wrapIndices u := ⟨(⌊x.val.1+ordinary u.1⌋,⌊x.val.2+ordinary u.2⌋),point_wrap_mem u x⟩
      exact Set.mem_iUnion.mpr ⟨k,hx,(mem_wrapCell u k.val x).mpr ⟨rfl,rfl⟩⟩
    · intro hx
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      exact hk.1
  have hdis : Pairwise (fun k l : wrapIndices u => Disjoint (W k).val (W l).val) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hx₁,hx₂⟩ := (mem_wrapCell u k.val x).mp hx.2
    obtain ⟨hy₁,hy₂⟩ := (mem_wrapCell u l.val x).mp hy.2
    exact hkl (Subtype.ext (Prod.ext (hx₁.symm.trans hy₁) (hx₂.symm.trans hy₂)))
  have he : (translatedPolygon u U).val=⋃k,(translatedPolygon u (W k)).val := by
    change translation a u '' U.val=⋃k,translation a u '' (W k).val
    rw [hcov,Set.image_iUnion]
  have hd : Pairwise (fun k l : wrapIndices u =>
      Disjoint (translatedPolygon u (W k)).val (translatedPolygon u (W l)).val) := by
    intro k l hkl
    apply Set.disjoint_image_image
    intro x hx y hy he
    have heq := (translation a u).injective he
    subst y
    exact Set.disjoint_left.mp (hdis hkl) hx hy
  rw [area_eq_sum _ _ he hd,area_eq_sum _ _ hcov hdis]
  exact Finset.sum_congr rfl (fun k _ => area_translation_wrap u k.val (W k) (fun _ hx => hx.2))

end PolygonArea
end PolygonAreaAlgebra

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonTrackArea
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonTrackArea
open Classical Set MeasureTheory
namespace PolygonGrid

theorem bank_representative {a m : ℕ} (U : Fin m → polygonAlgebra a) :
    ∃ S : Set PlaneTracks, S⊆region m ∧
      (∀i : Fin m,∀x : GenericSquare a,(i.val,x.val)∈S ↔ x∈(U i).val) ∧
      μ (closure S)=∑i,PolygonArea.area (U i) ∧
      μ (interior S)=∑i,PolygonArea.area (U i) := by
  choose R hR hm hn he using fun i => PolygonArea.representative (U i).property
  have hmR : ∀i,MeasurableSet (R i) := hm
  have harea (i : Fin m) : volume (R i)=PolygonArea.area (U i) :=
    (PolygonArea.area_eq_rep (U i) (hR i) (he i)).symm
  have hvol : μ (trackUnion R)=∑i,PolygonArea.area (U i) := by
    rw [volume_trackUnion R hmR]
    exact Finset.sum_congr rfl (fun i _ => harea i)
  have hclosure : closure (trackUnion R)⊆trackUnion (fun i => closure (R i)) := by
    apply (isClosed_iUnion_of_finite (fun i => isClosed_singleton.prod isClosed_closure)).closure_subset_iff.mpr
    exact trackUnion_mono (fun _ => subset_closure)
  have hinterior : trackUnion (fun i => interior (R i))⊆interior (trackUnion R) := by
    apply interior_maximal (trackUnion_mono (fun _ => interior_subset))
    exact isOpen_iUnion (fun i => (isOpen_discrete _).prod isOpen_interior)
  have hvclosure : μ (trackUnion (fun i => closure (R i)))=∑i,PolygonArea.area (U i) := by
    rw [volume_trackUnion _ (fun _ => isClosed_closure.measurableSet)]
    apply Finset.sum_congr rfl
    intro i _
    rw [measure_congr (PolygonArea.closure_ae_eq (hn i)),harea]
  have hvinterior : μ (trackUnion (fun i => interior (R i)))=∑i,PolygonArea.area (U i) := by
    rw [volume_trackUnion _ (fun _ => isOpen_interior.measurableSet)]
    apply Finset.sum_congr rfl
    intro i _
    rw [measure_congr (PolygonArea.interior_ae_eq (hn i)),harea]
  refine ⟨trackUnion R,trackUnion_region hR,?_,?_,?_⟩
  · intro i x
    exact (mem_trackUnion R i x.val).trans (he i x).symm
  · exact le_antisymm ((measure_mono hclosure).trans_eq hvclosure)
      (hvol.symm.trans_le (measure_mono subset_closure))
  · exact le_antisymm ((measure_mono interior_subset).trans_eq hvol)
      (hvinterior.symm.trans_le (measure_mono hinterior))

end PolygonGrid
end PolygonTrackArea

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonGridEmbedding
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonStrictComparison
open Classical Set
namespace PolygonGrid

theorem strict_comparison {a m : ℕ} (U V : Fin m → polygonAlgebra a)
    (harea : (∑i,PolygonArea.area (U i)) < ∑i,PolygonArea.area (V i)) :
    ∃ f : (PolygonObject.mk m U).Point ↪ (PolygonObject.mk m V).Point,
      PolygonObject.HasTable f := by
  let PU : PolygonObject a := ⟨m,U⟩
  let PV : PolygonObject a := ⟨m,V⟩
  obtain ⟨S,hS,heS,hcS,hiS⟩ := bank_representative U
  obtain ⟨T,hT,heT,hcT,hiT⟩ := bank_representative V
  have hh : MeasureTheory.Measure.count.prod ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
       MeasureTheory.volume) (closure S) < μ (interior T) := by
    change μ (closure S)<μ (interior T)
    rwa [hcS,hiT]
  obtain ⟨δ,hδ,hmatch⟩ := strict_grid_comparison hS hT hh
  obtain ⟨b,hr,hrδ⟩ := exists_grid_side hδ
  let r := shrinkingLevel b
  obtain ⟨N,I,J,⟨route⟩,hcover,hinto⟩ := hmatch (ordinary r) hr hrδ
  have getsrc (p : PU.Point) : ∃i : I,(p.val.1.val,p.val.2.val)∈cell (ordinary r) i.val := by
    have hs : (p.val.1.val,p.val.2.val)∈S := (heS p.val.1 p.val.2).mpr p.property
    obtain ⟨i,hi,hp⟩ := Set.mem_iUnion₂.mp (hcover hs)
    exact ⟨⟨i,hi⟩,hp⟩
  choose src hsrc using getsrc
  have src_eq (p : PU.Point) (i : I) (hi : (p.val.1.val,p.val.2.val)∈cell (ordinary r) i.val) :
      src p=i := by
    apply Subtype.ext
    by_contra hn
    exact Set.disjoint_left.mp (cells_disjoint hr hn) (hsrc p) hi
  let out (p : PU.Point) : TrackPoint a m :=
    ((route (src p)).val.1,translate a (displacement r (src p).val (route (src p)).val) p.val.2)
  have houtCell (p : PU.Point) : ( (out p).1.val,(out p).2.val)∈
      cell (ordinary r) (route (src p)).val := by
    apply translate_displacement_mem r _ _ ⟨rfl,(hsrc p).2⟩
    exact Set.Subset.trans (hinto _ (route (src p)).property) hT
  have houtV (p : PU.Point) : (out p).2∈(V (out p).1).val := by
    apply (heT _ _).mp
    exact hinto _ (route (src p)).property (houtCell p)
  have hout_inj : Function.Injective out := by
    intro p q hpq
    have ht : (route (src p)).val=(route (src q)).val := by
      by_contra hn
      exact Set.disjoint_left.mp (cells_disjoint hr hn) (houtCell p)
        (by simpa only [hpq] using houtCell q)
    have hs : src p=src q := route.injective (Subtype.ext ht)
    have htrack : p.val.1=q.val.1 := by
      apply Fin.ext
      exact (hsrc p).1.trans (by simpa only [hs] using (hsrc q).1.symm)
    have hpoint : p.val.2=q.val.2 := by
      have he := congrArg Prod.snd hpq
      change translate a (displacement r (src p).val (route (src p)).val) p.val.2 =
        translate a (displacement r (src q).val (route (src q)).val) q.val.2 at he
      rw [hs] at he
      exact (translation a _).injective he
    exact Subtype.ext (Prod.ext htrack hpoint)
  let f : PU.Point ↪ PV.Point :=
    ⟨fun p => ⟨out p,houtV p⟩,fun _ _ h => hout_inj (congrArg Subtype.val h)⟩
  let chart (i : I) : PolygonObject.Chart (a:=a) m m :=
    ⟨i.val.1,(route i).val.1,displacement r i.val (route i).val,
      U i.val.1 ⊓ rectangle a r i.val.2.1.val i.val.2.2.val⟩
  refine ⟨f,Finset.univ.image chart,?_,?_⟩
  · intro c hc
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hc
    intro x hx
    change x∈(U i.val.1).val ∧ x∈(rectangle a r i.val.2.1.val i.val.2.2.val).val at hx
    refine ⟨hx.1,?_⟩
    have hcell : (i.val.1.val,x.val)∈cell (ordinary r) i.val :=
      ⟨rfl,(mem_rectangle a r _ _ x).mp hx.2⟩
    have hs := src_eq ⟨(i.val.1,x),hx.1⟩ i hcell
    change out ⟨(i.val.1,x),hx.1⟩ = ((route i).val.1,translate a (displacement r i.val (route i).val) x)
    simp only [out,hs]
  · intro p
    refine ⟨chart (src p),Finset.mem_image.mpr ⟨src p,Finset.mem_univ _,rfl⟩,?_,?_⟩
    · exact Fin.ext (hsrc p).1
    · change p.val.2∈(U (src p).val.1).val ∧
        p.val.2∈(rectangle a r (src p).val.2.1.val (src p).val.2.2.val).val
      refine ⟨?_,(mem_rectangle a r _ _ _).mpr (hsrc p).2⟩
      have ht : p.val.1=(src p).val.1 := Fin.ext (hsrc p).1
      simpa only [←ht] using p.property

end PolygonGrid
end PolygonStrictComparison

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_EmptyStage
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.FiniteSetGroupoid
noncomputable def emptyFunctor : Terminal ⥤ FiniteSetGroupoid :=
  (Functor.const _).obj empty
noncomputable instance emptyFunctorMonoidal : emptyFunctor.Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x
    μIso_hom_natural_right := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x
    associativity := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x
    left_unitality := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x
    right_unitality := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x }
noncomputable instance instBraidedTerminalEmptyFunctor : emptyFunctor.Braided where
  braided _ _ := by apply Equiv.ext; intro x; exact Fin.elim0 x
end SimpleAmenable.PolygonObject.FiniteSetGroupoid

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_LabelTranslation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled

variable {a n : ℕ} (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
noncomputable def translateObj (U : Labelled a n) : Labelled a n where
  polygon := shifted U.polygon (fun i => d (U.label i))
  label := U.label
  reduced := U.reduced
noncomputable abbrev translateArrow (U : Labelled a n) : U.polygon ⟶ (translateObj d U).polygon :=
  shiftArrow U.polygon (fun i => d (U.label i))
noncomputable def translateHom {U V : Labelled a n} (f : U ⟶ V) : translateObj d U ⟶ translateObj d V where
  arrow := inv (translateArrow d U) ≫ f.arrow ≫ translateArrow d V
  positional x := by
    obtain ⟨y,rfl⟩ := (translateArrow d U).toEquiv.surjective x
    simp only [arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
    change translate a (d (V.label (f.arrow.toEquiv y).val.1)) (f.arrow.toEquiv y).val.2 =
      translate a (d (U.label y.val.1)) y.val.2
    rw [f.labelled,f.positional]
  labelled x := by
    obtain ⟨y,rfl⟩ := (translateArrow d U).toEquiv.surjective x
    simp only [arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
    exact f.labelled y
noncomputable def translateFunctor : Labelled a n ⥤ Labelled a n where
  obj := translateObj d
  map := translateHom d
  map_id U := by
    apply Hom.ext
    change inv _ ≫ 𝟙 _ ≫ _ = _
    simp
    rfl
  map_comp f g := by
    apply Hom.ext
    change inv _ ≫ (f.arrow ≫ g.arrow) ≫ _ = (inv _ ≫ f.arrow ≫ _) ≫ (inv _ ≫ g.arrow ≫ _)
    simp only [Category.assoc,IsIso.hom_inv_id_assoc]
noncomputable def translationIso : forget (a:=a) (n:=n) ≅ translateFunctor d ⋙ forget :=
  NatIso.ofComponents (fun U => by
    let e := asIso (translateArrow d U)
    exact e) (by
    intro U V f
    change f.arrow ≫ translateArrow d V = translateArrow d U ≫
      (inv (translateArrow d U) ≫ f.arrow ≫ translateArrow d V)
    simp)
noncomputable def translationCore : (translateFunctor (a:=a) d ⋙ forget).CoreMonoidal :=
  Functor.Monoidal.coreMonoidalTransport (translationIso d)
lemma translationCore_unit : (translationCore (a:=a) d).εIso.hom=translateArrow d (𝟙_ _) := by
  exact Category.id_comp (translateArrow d (𝟙_ _))
lemma translationCore_tensor (U V:Labelled a n) :
    ((translationCore d).μIso U V).hom =
      inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V) := by
  change (inv (translateArrow d U) ⊗ₘ inv (translateArrow d V)) ≫ 𝟙 _ ≫ _ = _
  erw [Category.id_comp]
  congr 1
  apply (cancel_epi (sumArrow (translateArrow d U) (translateArrow d V))).mp
  change (_ ⊗ₘ _) ≫ (_ ⊗ₘ _) = _
  rw [tensorHom_comp_tensorHom]
  simp
  rfl
noncomputable def translationUnit : 𝟙_ (Labelled a n) ⟶ (translateFunctor d).obj (𝟙_ _) where
  arrow := translateArrow d (𝟙_ _)
  positional x := by change Point PolygonObject.empty at x; exact isEmptyElim x
  labelled x := by change Point PolygonObject.empty at x; exact isEmptyElim x
noncomputable def translationTensor (U V:Labelled a n) :
    (translateFunctor d).obj U ⊗ (translateFunctor d).obj V ⟶ (translateFunctor d).obj (U⊗V) where
  arrow := inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V)
  positional x := by
    erw [arrow_comp_apply,inv_arrow_apply]
    change ((translateArrow d (sum U V)).toEquiv
      ((sumArrow (translateArrow d U) (translateArrow d V)).toEquiv.symm x)).val.2 = x.val.2
    obtain ⟨y,rfl⟩ := (sumArrow (translateArrow d U) (translateArrow d V)).toEquiv.surjective x
    rw [Equiv.symm_apply_apply]
    change translate a (d ((sum U V).label y.val.1)) y.val.2 =
      ((sumArrow (translateArrow d U) (translateArrow d V)).toEquiv y).val.2
    obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
    cases z <;> (first | erw [sumArrow_inl] | erw [sumArrow_inr]) <;>
      simp only [sumPointEquiv_inl,sumPointEquiv_inr,
      translateArrow,Fin.addCases_left,Fin.addCases_right]
    all_goals rfl
  labelled x := by
    erw [arrow_comp_apply,inv_arrow_apply]
    change (sum U V).label ((translateArrow d (sum U V)).toEquiv
      ((sumArrow (translateArrow d U) (translateArrow d V)).toEquiv.symm x)).val.1 =
      (sum (translateObj d U) (translateObj d V)).label x.val.1
    obtain ⟨y,rfl⟩ := (sumArrow (translateArrow d U) (translateArrow d V)).toEquiv.surjective x
    rw [Equiv.symm_apply_apply]
    change (sum U V).label y.val.1 =
      (sum (translateObj d U) (translateObj d V)).label
        ((sumArrow (translateArrow d U) (translateArrow d V)).toEquiv y).val.1
    obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
    cases z <;> (first | erw [sumArrow_inl] | erw [sumArrow_inr]) <;> rfl
lemma translationTensor_arrow (U V : Labelled a n) :
    (translationTensor d U V).arrow=((translationCore d).μIso U V).hom := by
  rw [translationCore_tensor]; rfl
lemma translationUnit_arrow : (translationUnit (a:=a) d).arrow=(translationCore d).εIso.hom := by
  rw [translationCore_unit]; rfl
noncomputable instance translationMonoidal : (translateFunctor (a:=a) d).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso (translationUnit d)
    μIso U V := asIso (translationTensor d U V)
    μIso_hom_natural_left := by
      intro U V f W
      apply Hom.ext
      change sumArrow (translateHom d f).arrow (𝟙 _) ≫ (translationTensor d V W).arrow =
        (translationTensor d U W).arrow ≫ (translateHom d (f ▷ W)).arrow
      rw [translationTensor_arrow,translationTensor_arrow]
      exact (translationCore d).μIso_hom_natural_left f W
    μIso_hom_natural_right := by
      intro U V W f
      apply Hom.ext
      change sumArrow (𝟙 _) (translateHom d f).arrow ≫ (translationTensor d W V).arrow =
        (translationTensor d W U).arrow ≫ (translateHom d (W ◁ f)).arrow
      rw [translationTensor_arrow,translationTensor_arrow]
      exact (translationCore d).μIso_hom_natural_right W f
    associativity := by
      intro U V W
      apply Hom.ext
      change sumArrow (translationTensor d U V).arrow (𝟙 _) ≫
        (translationTensor d (U⊗V) W).arrow ≫ (translateHom d (α_ U V W).hom).arrow =
        sumAssoc _ _ _ ≫ sumArrow (𝟙 _) (translationTensor d V W).arrow ≫
          (translationTensor d U (V⊗W)).arrow
      simp only [translationTensor_arrow]
      exact (translationCore d).associativity U V W
    left_unitality := by
      intro U
      apply Hom.ext
      change leftUnit _ = sumArrow (translationUnit d).arrow (𝟙 _) ≫
        (translationTensor d (𝟙_ _) U).arrow ≫ (translateHom d (λ_ U).hom).arrow
      rw [translationUnit_arrow,translationTensor_arrow]
      exact (translationCore d).left_unitality U
    right_unitality := by
      intro U
      apply Hom.ext
      change rightUnit _ = sumArrow (𝟙 _) (translationUnit d).arrow ≫
        (translationTensor d U (𝟙_ _)).arrow ≫ (translateHom d (ρ_ U).hom).arrow
      rw [translationUnit_arrow,translationTensor_arrow]
      exact (translationCore d).right_unitality U }
noncomputable instance translationBraided : (translateFunctor (a:=a) d).Braided where
  braided U V := by
    apply Hom.ext
    change (translationTensor d U V).arrow ≫ (translateHom d (β_ U V).hom).arrow =
      sumSwap _ _ ≫ (translationTensor d V U).arrow
    change (inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V)) ≫
      (inv (translateArrow d (U⊗V)) ≫ sumSwap _ _ ≫ translateArrow d (V⊗U)) =
      sumSwap _ _ ≫ inv (sumArrow (translateArrow d V) (translateArrow d U)) ≫ translateArrow d (V⊗U)
    simp only [Category.assoc,IsIso.hom_inv_id_assoc]
    apply (cancel_epi (sumArrow (translateArrow d U) (translateArrow d V))).mp
    simp only [IsIso.hom_inv_id_assoc]
    have h := BraidedCategory.braiding_naturality (translateArrow d U) (translateArrow d V)
    change sumArrow (translateArrow d U) (translateArrow d V) ≫ sumSwap _ _ =
      sumSwap _ _ ≫ sumArrow (translateArrow d V) (translateArrow d U) at h
    rw [←Category.assoc (sumArrow (translateArrow d U) (translateArrow d V)),h]
    simp
end SimpleAmenable.PolygonObject.Labelled

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PointFiberEvaluation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Classical Set MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.PointFiber

variable {a n : ℕ}
abbrev Fiber (U : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) :=
  {x : U.polygon.Point // x.val.2=b.1 ∧ U.label x.val.1=b.2}

noncomputable instance instFintypeFiber (U : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) : Fintype (Fiber U b) :=
  Fintype.ofInjective (fun x : Fiber U b => x.val.val.1) (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext h (x.property.1.trans y.property.1.symm))

noncomputable def fiberMap {U V : Labelled a n} (f : U ⟶ V) (b : GenericSquare a × (Fin n → CutRing × CutRing)) :
    Fiber U b ≃ Fiber V b where
  toFun x := ⟨f.arrow.toEquiv x.val,
    (f.positional x.val).trans x.property.1,
    (f.labelled x.val).trans x.property.2⟩
  invFun y := ⟨f.arrow.toEquiv.symm y.val,by
    have h := f.positional (f.arrow.toEquiv.symm y.val)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans y.property.1,by
    have h := f.labelled (f.arrow.toEquiv.symm y.val)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans y.property.2⟩
  left_inv _ := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (Equiv.apply_symm_apply _ _)

noncomputable def evaluation : Labelled a n ⥤ (GenericSquare a × (Fin n → CutRing × CutRing) → FiniteSetGroupoid) where
  obj U b := ⟨Fintype.card (Fiber U b)⟩
  map {U V} f b := (Fintype.equivFin (Fiber U b)).symm.trans
    ((fiberMap f b).trans (Fintype.equivFin (Fiber V b)))
  map_id U := by
    funext b
    apply Equiv.ext
    intro j
    change (Fintype.equivFin (Fiber U b)) ((fiberMap (𝟙 U) b)
      ((Fintype.equivFin (Fiber U b)).symm j))=j
    change (Fintype.equivFin (Fiber U b)) ((Fintype.equivFin (Fiber U b)).symm j)=j
    exact Equiv.apply_symm_apply _ _
  map_comp {U V W} f g := by
    funext b
    apply Equiv.ext
    intro j
    change (Fintype.equivFin (Fiber W b)) ((fiberMap (f≫g) b) _)=
      (Fintype.equivFin (Fiber W b)) ((fiberMap g b)
        ((Fintype.equivFin (Fiber V b)).symm ((Fintype.equivFin (Fiber V b)) _)))
    rw [Equiv.symm_apply_apply]
    rfl

end SimpleAmenable.PolygonObject.Labelled.PointFiber

end

section
open _root_.CategoryTheory Classical Set MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.PointFiber

variable {a n : ℕ}
variable (U V : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing))
noncomputable def fiberSumFun : Fiber U b ⊕ Fiber V b → Fiber (sum U V) b
  | .inl x => ⟨sumPointEquiv U.polygon V.polygon (.inl x.val),by
      simpa only [sumPointEquiv_inl] using x.property.1,by
      simpa only [sum,sumPointEquiv_inl,Fin.addCases_left] using x.property.2⟩
  | .inr y => ⟨sumPointEquiv U.polygon V.polygon (.inr y.val),by
      simpa only [sumPointEquiv_inr] using y.property.1,by
      simpa only [sum,sumPointEquiv_inr,Fin.addCases_right] using y.property.2⟩
noncomputable def fiberSum : Fiber U b ⊕ Fiber V b ≃ Fiber (sum U V) b :=
  Equiv.ofBijective (fiberSumFun U V b) ⟨by
    intro x y h
    have h' := congrArg Subtype.val h
    cases x <;> cases y
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj ((sumPointEquiv _ _).injective h')))
    · cases ((sumPointEquiv _ _).injective h')
    · cases ((sumPointEquiv _ _).injective h')
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj ((sumPointEquiv _ _).injective h'))),by
    intro z
    obtain ⟨x,hx⟩ := (sumPointEquiv U.polygon V.polygon).surjective z.val
    cases x with
    | inl x =>
      have hp : x.val.2=b.1 ∧ U.label x.val.1=b.2 := by
        simpa only [←hx,sumPointEquiv_inl,sum,Fin.addCases_left] using z.property
      exact ⟨.inl ⟨x,hp⟩,Subtype.ext hx⟩
    | inr x =>
      have hp : x.val.2=b.1 ∧ V.label x.val.1=b.2 := by
        simpa only [←hx,sumPointEquiv_inr,sum,Fin.addCases_right] using z.property
      exact ⟨.inr ⟨x,hp⟩,Subtype.ext hx⟩⟩
@[simp] lemma fiberSum_inl (x : Fiber U b) :
    (fiberSum U V b (.inl x)).val=sumPointEquiv U.polygon V.polygon (.inl x.val) := rfl
@[simp] lemma fiberSum_inr (x : Fiber V b) :
    (fiberSum U V b (.inr x)).val=sumPointEquiv U.polygon V.polygon (.inr x.val) := rfl

noncomputable abbrev E := evaluation (a:=a) (n:=n)
noncomputable def enumerate (U : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) : Fiber U b ≃ Fin (E.obj U b).size := Fintype.equivFin (Fiber U b)
@[simp] lemma E_map_enum {U V : Labelled a n} (f : U ⟶ V) (b : GenericSquare a × (Fin n → CutRing × CutRing)) (x : Fiber U b) :
    E.map f b (enumerate U b x)=enumerate V b (fiberMap f b x) := by
  change enumerate V b (fiberMap f b ((enumerate U b).symm (enumerate U b x)))=_
  rw [Equiv.symm_apply_apply]
noncomputable def mu (U V : Labelled a n) : E.obj U ⊗ E.obj V ⟶ E.obj (U⊗V) := fun b =>
  (FiniteSetGroupoid.sumEquiv _ _).symm.trans
    ((Equiv.sumCongr (enumerate U b).symm (enumerate V b).symm).trans
      ((fiberSum U V b).trans (enumerate (sum U V) b)))
@[simp] lemma mu_inl (x : Fiber U b) :
    mu U V b (FiniteSetGroupoid.sumEquiv _ _ (.inl (enumerate U b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inl x)) := by
  change (enumerate (sum U V) b) ((fiberSum U V b) ((Equiv.sumCongr (enumerate U b).symm (enumerate V b).symm)
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).symm
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)) _)))) = _
  rw [Equiv.symm_apply_apply]
  simp only [Equiv.sumCongr_apply,Sum.map_inl,Equiv.symm_apply_apply]
@[simp] lemma mu_inr (x : Fiber V b) :
    mu U V b (FiniteSetGroupoid.sumEquiv _ _ (.inr (enumerate V b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inr x)) := by
  change (enumerate (sum U V) b) ((fiberSum U V b) ((Equiv.sumCongr (enumerate U b).symm (enumerate V b).symm)
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).symm
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)) _)))) = _
  rw [Equiv.symm_apply_apply]
  simp only [Equiv.sumCongr_apply,Sum.map_inr,Equiv.symm_apply_apply]
lemma fiberMap_sum_inl {U V W Z : Labelled a n} (f : U ⟶ W) (g : V ⟶ Z)
    (b : GenericSquare a × (Fin n → CutRing × CutRing)) (x : Fiber U b) :
    fiberMap (sumHom f g) b (fiberSum U V b (.inl x))=
      fiberSum W Z b (.inl (fiberMap f b x)) := by
  apply Subtype.ext
  exact sumArrow_inl f.arrow g.arrow x.val
lemma fiberMap_sum_inr {U V W Z : Labelled a n} (f : U ⟶ W) (g : V ⟶ Z)
    (b : GenericSquare a × (Fin n → CutRing × CutRing)) (x : Fiber V b) :
    fiberMap (sumHom f g) b (fiberSum U V b (.inr x))=
      fiberSum W Z b (.inr (fiberMap g b x)) := by
  apply Subtype.ext
  exact sumArrow_inr f.arrow g.arrow x.val
end SimpleAmenable.PolygonObject.Labelled.PointFiber

end

section
open _root_.CategoryTheory Classical Set MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.PointFiber

variable {a n : ℕ}
instance fiberEmpty (b : GenericSquare a × (Fin n → CutRing × CutRing)) : IsEmpty (Fiber (empty (a:=a) (n:=n)) b) :=
  ⟨fun x => isEmptyElim x.val⟩
noncomputable def eps : 𝟙_ ((GenericSquare a × (Fin n → CutRing × CutRing) → FiniteSetGroupoid)) ⟶ E.obj (𝟙_ (Labelled a n)) := fun b =>
  (Equiv.equivOfIsEmpty (Fin 0) (Fiber empty b)).trans (enumerate empty b)
@[simp] lemma fiberMap_id (U : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) (x : Fiber U b) :
    fiberMap (𝟙 U) b x=x := rfl
lemma mu_natural {U V W Z : Labelled a n} (f : U ⟶ W) (g : V ⟶ Z) :
    (E.map f ⊗ₘ E.map g) ≫ mu W Z = mu U V ≫ E.map (f⊗ₘg) := by
  funext b
  apply Equiv.ext
  intro x
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
  cases x with
  | inl x =>
    obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
    change mu W Z b (FiniteSetGroupoid.sumHom (E.map f b) (E.map g b) _) = E.map (sumHom f g) b _
    rw [FiniteSetGroupoid.sumHom_inl,E_map_enum,mu_inl,mu_inl,E_map_enum,fiberMap_sum_inl]
  | inr x =>
    obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
    change mu W Z b (FiniteSetGroupoid.sumHom (E.map f b) (E.map g b) _) = E.map (sumHom f g) b _
    rw [FiniteSetGroupoid.sumHom_inr,E_map_enum,mu_inr,mu_inr,E_map_enum,fiberMap_sum_inr]

variable (U V W : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing))
@[simp] lemma fiber_assoc_left (x : Fiber U b) :
    fiberMap (assocHom U V W) b (fiberSum (sum U V) W b (.inl (fiberSum U V b (.inl x))))=
      fiberSum U (sum V W) b (.inl x) := by
  apply Subtype.ext
  change sumAssocEquiv U.polygon V.polygon W.polygon _ = _
  exact sumAssocEquiv_left _ _ _ x.val
@[simp] lemma fiber_assoc_mid (x : Fiber V b) :
    fiberMap (assocHom U V W) b (fiberSum (sum U V) W b (.inl (fiberSum U V b (.inr x))))=
      fiberSum U (sum V W) b (.inr (fiberSum V W b (.inl x))) := by
  apply Subtype.ext
  change sumAssocEquiv U.polygon V.polygon W.polygon _ = _
  exact sumAssocEquiv_mid _ _ _ x.val
@[simp] lemma fiber_assoc_right (x : Fiber W b) :
    fiberMap (assocHom U V W) b (fiberSum (sum U V) W b (.inr x))=
      fiberSum U (sum V W) b (.inr (fiberSum V W b (.inr x))) := by
  apply Subtype.ext
  change sumAssocEquiv U.polygon V.polygon W.polygon _ = _
  exact sumAssocEquiv_right _ _ _ x.val
@[simp] lemma fiber_left (x : Fiber U b) :
    fiberMap (leftHom U) b (fiberSum empty U b (.inr x))=x := by
  apply Subtype.ext
  exact leftUnitEquiv_apply _ x.val
@[simp] lemma fiber_right (x : Fiber U b) :
    fiberMap (rightHom U) b (fiberSum U empty b (.inl x))=x := by
  apply Subtype.ext
  exact rightUnitEquiv_apply _ x.val
@[simp] lemma fiber_swap_left (x : Fiber U b) :
    fiberMap (swapHom U V) b (fiberSum U V b (.inl x))=fiberSum V U b (.inr x) := by
  apply Subtype.ext
  exact sumSwapEquiv_inl _ _ x.val
@[simp] lemma fiber_swap_right (x : Fiber V b) :
    fiberMap (swapHom U V) b (fiberSum U V b (.inr x))=fiberSum V U b (.inl x) := by
  apply Subtype.ext
  exact sumSwapEquiv_inr _ _ x.val
end SimpleAmenable.PolygonObject.Labelled.PointFiber

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageFiberSum
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.UniformObject

variable {a n s : ℕ} {P : BooleanPartition a} {L : Fin s → Fin n → CutRing × CutRing}
variable (U V : UniformObject P L) (b : Fin P.size × Fin s)
noncomputable def fiberSumFun : Fiber U b ⊕ Fiber V b → Fiber (sum U V) b
  | .inl x => ⟨sumPointEquiv U.obj.polygon V.obj.polygon (.inl x.val),by
      simpa only [sumPointEquiv_inl] using x.property.1,by
      simpa only [sum,Labelled.sum,sumPointEquiv_inl,Fin.addCases_left] using x.property.2⟩
  | .inr y => ⟨sumPointEquiv U.obj.polygon V.obj.polygon (.inr y.val),by
      simpa only [sumPointEquiv_inr] using y.property.1,by
      simpa only [sum,Labelled.sum,sumPointEquiv_inr,Fin.addCases_right] using y.property.2⟩
noncomputable def fiberSum : Fiber U b ⊕ Fiber V b ≃ Fiber (sum U V) b :=
  Equiv.ofBijective (fiberSumFun U V b) ⟨by
    intro x y h
    have h' := congrArg Subtype.val h
    cases x <;> cases y
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj ((sumPointEquiv _ _).injective h')))
    · cases ((sumPointEquiv _ _).injective h')
    · cases ((sumPointEquiv _ _).injective h')
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj ((sumPointEquiv _ _).injective h'))),by
    intro z
    obtain ⟨x,hx⟩ := (sumPointEquiv U.obj.polygon V.obj.polygon).surjective z.val
    cases x with
    | inl x =>
      have hp : x.val.2=P.point b.1 ∧ U.obj.label x.val.1=L b.2 := by
        simpa only [←hx,sumPointEquiv_inl,sum,Labelled.sum,Fin.addCases_left] using z.property
      exact ⟨.inl ⟨x,hp⟩,Subtype.ext hx⟩
    | inr x =>
      have hp : x.val.2=P.point b.1 ∧ V.obj.label x.val.1=L b.2 := by
        simpa only [←hx,sumPointEquiv_inr,sum,Labelled.sum,Fin.addCases_right] using z.property
      exact ⟨.inr ⟨x,hp⟩,Subtype.ext hx⟩⟩
@[simp] lemma fiberSum_inl (x : Fiber U b) :
    (fiberSum U V b (.inl x)).val=sumPointEquiv U.obj.polygon V.obj.polygon (.inl x.val) := rfl
@[simp] lemma fiberSum_inr (x : Fiber V b) :
    (fiberSum U V b (.inr x)).val=sumPointEquiv U.obj.polygon V.obj.polygon (.inr x.val) := rfl

noncomputable abbrev E := evaluation (P:=P) (L:=L)
noncomputable def enumerate (U : UniformObject P L) (b : Fin P.size × Fin s) : Fiber U b ≃ Fin (E.obj U b).size := Fintype.equivFin (Fiber U b)
@[simp] lemma E_map_enum {U V : UniformObject P L} (f : U ⟶ V) (b : Fin P.size × Fin s) (x : Fiber U b) :
    E.map f b (enumerate U b x)=enumerate V b (fiberMap f b x) := by
  change enumerate V b (fiberMap f b ((enumerate U b).symm (enumerate U b x)))=_
  rw [Equiv.symm_apply_apply]
noncomputable def mu (U V : UniformObject P L) : E.obj U ⊗ E.obj V ⟶ E.obj (U⊗V) := fun b =>
  (FiniteSetGroupoid.sumEquiv _ _).symm.trans
    ((Equiv.sumCongr (enumerate U b).symm (enumerate V b).symm).trans
      ((fiberSum U V b).trans (enumerate (sum U V) b)))
@[simp] lemma mu_inl (x : Fiber U b) :
    mu U V b (FiniteSetGroupoid.sumEquiv _ _ (.inl (enumerate U b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inl x)) := by
  change (enumerate (sum U V) b) ((fiberSum U V b) ((Equiv.sumCongr (enumerate U b).symm (enumerate V b).symm)
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).symm
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)) _)))) = _
  rw [Equiv.symm_apply_apply]
  simp only [Equiv.sumCongr_apply,Sum.map_inl,Equiv.symm_apply_apply]
@[simp] lemma mu_inr (x : Fiber V b) :
    mu U V b (FiniteSetGroupoid.sumEquiv _ _ (.inr (enumerate V b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inr x)) := by
  change (enumerate (sum U V) b) ((fiberSum U V b) ((Equiv.sumCongr (enumerate U b).symm (enumerate V b).symm)
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).symm
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)) _)))) = _
  rw [Equiv.symm_apply_apply]
  simp only [Equiv.sumCongr_apply,Sum.map_inr,Equiv.symm_apply_apply]
lemma fiberMap_sum_inl {U V W Z : UniformObject P L} (f : U ⟶ W) (g : V ⟶ Z)
    (b : Fin P.size × Fin s) (x : Fiber U b) :
    fiberMap (sumHom f g) b (fiberSum U V b (.inl x))=
      fiberSum W Z b (.inl (fiberMap f b x)) := by
  apply Subtype.ext
  exact sumArrow_inl f.arrow.arrow g.arrow.arrow x.val
lemma fiberMap_sum_inr {U V W Z : UniformObject P L} (f : U ⟶ W) (g : V ⟶ Z)
    (b : Fin P.size × Fin s) (x : Fiber V b) :
    fiberMap (sumHom f g) b (fiberSum U V b (.inr x))=
      fiberSum W Z b (.inr (fiberMap g b x)) := by
  apply Subtype.ext
  exact sumArrow_inr f.arrow.arrow g.arrow.arrow x.val
end SimpleAmenable.PolygonObject.LabelledStage.UniformObject

end

section
open _root_.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.UniformObject

variable {a n s : ℕ} {P : BooleanPartition a} {L : Fin s → Fin n → CutRing × CutRing}
instance fiberEmpty (b : Fin P.size × Fin s) : IsEmpty (Fiber (empty (P:=P) (L:=L)) b) :=
  ⟨fun x => isEmptyElim x.val⟩
noncomputable def eps : 𝟙_ (Obj P (s:=s)) ⟶ E.obj (𝟙_ (UniformObject P L)) := fun b =>
  (Equiv.equivOfIsEmpty (Fin 0) (Fiber empty b)).trans (enumerate empty b)
@[simp] lemma fiberMap_id (U : UniformObject P L) (b : Fin P.size × Fin s) (x : Fiber U b) :
    fiberMap (𝟙 U) b x=x := rfl
lemma mu_natural {U V W Z : UniformObject P L} (f : U ⟶ W) (g : V ⟶ Z) :
    (E.map f ⊗ₘ E.map g) ≫ mu W Z = mu U V ≫ E.map (f⊗ₘg) := by
  funext b
  apply Equiv.ext
  intro x
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
  cases x with
  | inl x =>
    obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
    change mu W Z b (FiniteSetGroupoid.sumHom (E.map f b) (E.map g b) _) = E.map (sumHom f g) b _
    rw [FiniteSetGroupoid.sumHom_inl,E_map_enum,mu_inl,mu_inl,E_map_enum,fiberMap_sum_inl]
  | inr x =>
    obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
    change mu W Z b (FiniteSetGroupoid.sumHom (E.map f b) (E.map g b) _) = E.map (sumHom f g) b _
    rw [FiniteSetGroupoid.sumHom_inr,E_map_enum,mu_inr,mu_inr,E_map_enum,fiberMap_sum_inr]

variable (U V W : UniformObject P L) (b : Fin P.size × Fin s)
@[simp] lemma fiber_assoc_left (x : Fiber U b) :
    fiberMap (assocHom U V W) b (fiberSum (sum U V) W b (.inl (fiberSum U V b (.inl x))))=
      fiberSum U (sum V W) b (.inl x) := by
  apply Subtype.ext
  change sumAssocEquiv U.obj.polygon V.obj.polygon W.obj.polygon _ = _
  exact sumAssocEquiv_left _ _ _ x.val
@[simp] lemma fiber_assoc_mid (x : Fiber V b) :
    fiberMap (assocHom U V W) b (fiberSum (sum U V) W b (.inl (fiberSum U V b (.inr x))))=
      fiberSum U (sum V W) b (.inr (fiberSum V W b (.inl x))) := by
  apply Subtype.ext
  change sumAssocEquiv U.obj.polygon V.obj.polygon W.obj.polygon _ = _
  exact sumAssocEquiv_mid _ _ _ x.val
@[simp] lemma fiber_assoc_right (x : Fiber W b) :
    fiberMap (assocHom U V W) b (fiberSum (sum U V) W b (.inr x))=
      fiberSum U (sum V W) b (.inr (fiberSum V W b (.inr x))) := by
  apply Subtype.ext
  change sumAssocEquiv U.obj.polygon V.obj.polygon W.obj.polygon _ = _
  exact sumAssocEquiv_right _ _ _ x.val
@[simp] lemma fiber_left (x : Fiber U b) :
    fiberMap (leftHom U) b (fiberSum empty U b (.inr x))=x := by
  apply Subtype.ext
  exact leftUnitEquiv_apply _ x.val
@[simp] lemma fiber_right (x : Fiber U b) :
    fiberMap (rightHom U) b (fiberSum U empty b (.inl x))=x := by
  apply Subtype.ext
  exact rightUnitEquiv_apply _ x.val
@[simp] lemma fiber_swap_left (x : Fiber U b) :
    fiberMap (swapHom U V) b (fiberSum U V b (.inl x))=fiberSum V U b (.inr x) := by
  apply Subtype.ext
  exact sumSwapEquiv_inl _ _ x.val
@[simp] lemma fiber_swap_right (x : Fiber V b) :
    fiberMap (swapHom U V) b (fiberSum U V b (.inr x))=fiberSum V U b (.inl x) := by
  apply Subtype.ext
  exact sumSwapEquiv_inr _ _ x.val
end SimpleAmenable.PolygonObject.LabelledStage.UniformObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageRealization
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.braided _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instCoeFunHomForallFinSize _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.monoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.symmetric _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

noncomputable def realizeObject (U : Obj P (s:=s)) : UniformObject P L where
  obj := object P L hL U
  uniform j x y h := by
    change (P.color x=_) ↔ (P.color y=_)
    rw [h]
  supported j := ⟨_,rfl⟩

noncomputable def realize : Obj P (s:=s) ⥤ UniformObject P L where
  obj := realizeObject P L hL
  map f := ⟨arrow P L hL f,fun _ _ h _ => congrArg (indexMap P L hL f) h⟩
  map_id U := UniformObject.Hom.ext _ _ ((functor P L hL).map_id U)
  map_comp f g := UniformObject.Hom.ext _ _ ((functor P L hL).map_comp f g)

namespace UniformObject
variable {P L}
noncomputable def labelIndex (U : UniformObject P L) (j : Fin U.obj.polygon.tracks) : Fin s :=
  (U.supported j).choose
lemma labelIndex_spec (U : UniformObject P L) (j : Fin U.obj.polygon.tracks) :
    L (labelIndex U j)=U.obj.label j := (U.supported j).choose_spec

variable (hLi : Function.Injective L)
include hLi in
lemma labelIndex_fiber (U : UniformObject P L) {b : Fin P.size × Fin s} (y : Fiber U b) :
    labelIndex U y.val.val.1=b.2 := hLi ((labelIndex_spec U _).trans y.property.2)

noncomputable abbrev evaluated (U : UniformObject P L) := (evaluation (P:=P) (L:=L)).obj U

noncomputable def fiberIndex (U : UniformObject P L) :
    Fin (Fintype.card (Track P (evaluated U))) ≃ Σ b : Fin P.size × Fin s,Fiber U b :=
  (index P (evaluated U)).symm.trans
    (Equiv.sigmaCongrRight (fun b => (Fintype.equivFin (Fiber U b)).symm))

noncomputable abbrev trackFiber (U : UniformObject P L)
    (j : Fin (Fintype.card (Track P (evaluated U)))) := (fiberIndex U j).2

noncomputable def sourceAtom (U : UniformObject P L) (x : U.obj.polygon.Point) : Fin P.size × Fin s :=
  (P.color x.val.2,labelIndex U x.val.1)

noncomputable def sample (U : UniformObject P L) (x : U.obj.polygon.Point) : Fiber U (sourceAtom U x) :=
  ⟨⟨(x.val.1,P.point (P.color x.val.2)),
    (U.uniform x.val.1 x.val.2 (P.point (P.color x.val.2)) (by simp)).mp x.property⟩,
    rfl,(labelIndex_spec U _).symm⟩

noncomputable def sourceIndex (U : UniformObject P L) (x : U.obj.polygon.Point) :
    Fin (Fintype.card (Track P (evaluated U))) :=
  (fiberIndex U).symm ⟨sourceAtom U x,sample U x⟩

@[simp] lemma sourceIndex_atom (U : UniformObject P L) (x : U.obj.polygon.Point) :
    ((index P (evaluated U)).symm (sourceIndex U x)).1=sourceAtom U x := by
  change (fiberIndex U ((fiberIndex U).symm ⟨sourceAtom U x,sample U x⟩)).1=_
  rw [Equiv.apply_symm_apply]

@[simp] lemma sourceIndex_track (U : UniformObject P L) (x : U.obj.polygon.Point) :
    (trackFiber U (sourceIndex U x)).val.val.1=x.val.1 := by
  change (fiberIndex U ((fiberIndex U).symm ⟨sourceAtom U x,sample U x⟩)).2.val.val.1=_
  rw [Equiv.apply_symm_apply]
  rfl

variable (P L)
noncomputable def reconstructMap (U : UniformObject P L)
    (x : (object P L hL (evaluated U)).polygon.Point) : U.obj.polygon.Point :=
  ⟨((trackFiber U x.val.1).val.val.1,x.val.2),by
    have h := (trackFiber U x.val.1).val.property
    have hc : P.color (trackFiber U x.val.1).val.val.2=P.color x.val.2 := by
      rw [(trackFiber U x.val.1).property.1,BooleanPartition.color_point]
      exact x.property.symm
    exact (U.uniform _ _ _ hc).mp h⟩

noncomputable def reconstructInverse (U : UniformObject P L) (x : U.obj.polygon.Point) :
    (object P L hL (evaluated U)).polygon.Point :=
  ⟨(sourceIndex U x,x.val.2),by
    change P.color x.val.2=((index P (evaluated U)).symm (sourceIndex U x)).1.1
    rw [sourceIndex_atom]
    rfl⟩

lemma reconstruct_right (U : UniformObject P L) (x : U.obj.polygon.Point) :
    reconstructMap P L hL U (reconstructInverse P L hL U x)=x := by
  apply Subtype.ext
  apply Prod.ext
  · exact sourceIndex_track U x
  · rfl

include hLi in
lemma reconstruct_left (U : UniformObject P L)
    (x : (object P L hL (evaluated U)).polygon.Point) :
    reconstructInverse P L hL U (reconstructMap P L hL U x)=x := by
  apply Subtype.ext
  apply Prod.ext
  · change sourceIndex U (reconstructMap P L hL U x)=x.val.1
    apply (fiberIndex U).injective
    change fiberIndex U ((fiberIndex U).symm _) = _
    rw [Equiv.apply_symm_apply]
    have hb : sourceAtom U (reconstructMap P L hL U x)=(fiberIndex U x.val.1).1 := by
      apply Prod.ext
      · exact x.property
      · exact labelIndex_fiber hLi U (trackFiber U x.val.1)
    apply Sigma.ext hb
    apply (Subtype.heq_iff_coe_eq (by intro y; dsimp only; rw [hb])).mpr
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change P.point (P.color x.val.2)=(trackFiber U x.val.1).val.val.2
      rw [show P.color x.val.2=(fiberIndex U x.val.1).1.1 from x.property]
      exact (trackFiber U x.val.1).property.1.symm

  · rfl

noncomputable def reconstructEquiv (U : UniformObject P L) :
    (object P L hL (evaluated U)).polygon.Point ≃ U.obj.polygon.Point where
  toFun := reconstructMap P L hL U
  invFun := reconstructInverse P L hL U
  left_inv := reconstruct_left P L hL hLi U
  right_inv := reconstruct_right P L hL U

end UniformObject
end LabelledStage
end SimpleAmenable.PolygonObject

end

section

open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace LabelledStage
variable {a n s : ℕ} (P : BooleanPartition a)
    (L : Fin s → Fin n → CutRing × CutRing)
    (hL : ∀ j i, orbitRepresentative (L j i)=L j i)
    (hLi : Function.Injective L)

namespace UniformObject
noncomputable def reconstruct (U : UniformObject P L) :
    (realize P L hL).obj (evaluated U) ⟶ U where
  arrow := {
    arrow := relabelArrow (reconstructEquiv P L hL hLi U)
      (fun j => (trackFiber U j).val.val.1) (fun _ => rfl)
    positional := fun _ => rfl
    labelled := fun x => (trackFiber U x.val.1).property.2 }
  uniform := fun _ _ h _ => congrArg (fun j => (trackFiber U j).val.val.1) h
end UniformObject

open UniformObject
include hLi in
theorem realize_essSurj : (realize P L hL).EssSurj := {
  mem_essImage U := ⟨evaluated U,⟨asIso (reconstruct P L hL hLi U)⟩⟩ }

noncomputable def fiberPoint (U : Obj P (s:=s)) (b : Fin P.size × Fin s) (k : Fin (U b).size) :
    Fiber (realizeObject P L hL U) b :=
  ⟨⟨(index P U ⟨b,k⟩,P.point b.1),by
    change P.color (P.point b.1)=((index P U).symm ((index P U) ⟨b,k⟩)).1.1
    rw [Equiv.symm_apply_apply,BooleanPartition.color_point]⟩,rfl,by
    change L (((index P U).symm ((index P U) ⟨b,k⟩)).1.2)=L b.2
    rw [Equiv.symm_apply_apply]⟩

include hLi in
lemma fiber_base (U : Obj P (s:=s)) (b : Fin P.size × Fin s)
    (y : Fiber (realizeObject P L hL U) b) :
    ((index P U).symm y.val.val.1).1=b := by
  apply Prod.ext
  · have hp := y.val.property
    change P.color y.val.val.2=((index P U).symm y.val.val.1).1.1 at hp
    rw [y.property.1,BooleanPartition.color_point] at hp
    exact hp.symm
  · apply hLi
    exact y.property.2

noncomputable def fiberFin (U : Obj P (s:=s)) (b : Fin P.size × Fin s)
    (y : Fiber (realizeObject P L hL U) b) : Fin (U b).size :=
  (fiber_base P L hL hLi U b y) ▸ ((index P U).symm y.val.val.1).2

lemma fiberFin_spec (U : Obj P (s:=s)) (b : Fin P.size × Fin s)
    (y : Fiber (realizeObject P L hL U) b) :
    (⟨b,fiberFin P L hL hLi U b y⟩ : Track P U)=((index P U).symm y.val.val.1) := by
  apply Sigma.ext (fiber_base P L hL hLi U b y).symm
  dsimp only [fiberFin]
  exact eqRec_heq (φ:=fun b => Fin (U b).size) _ _

noncomputable def fiberEquiv (U : Obj P (s:=s)) (b : Fin P.size × Fin s) :
    Fin (U b).size ≃ Fiber (realizeObject P L hL U) b where
  toFun := fiberPoint P L hL U b
  invFun := fiberFin P L hL hLi U b
  left_inv k := by
    have h := fiberFin_spec P L hL hLi U b (fiberPoint P L hL U b k)
    change (⟨b,_⟩ : Track P U)=(index P U).symm ((index P U) ⟨b,k⟩) at h
    rw [Equiv.symm_apply_apply] at h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change index P U ⟨b,fiberFin P L hL hLi U b y⟩=y.val.val.1
      rw [fiberFin_spec]
      exact Equiv.apply_symm_apply (index P U) y.val.val.1
    · exact y.property.1.symm

end LabelledStage
end SimpleAmenable.PolygonObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageEvaluationEquiv
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n s : ℕ} (P : BooleanPartition a) (L : Fin s → Fin n → CutRing × CutRing)
    (hL : ∀ j i, orbitRepresentative (L j i)=L j i) (hLi : Function.Injective L)
open UniformObject
lemma fiberMap_realize {U V : Obj P (s:=s)} (f : U ⟶ V) (b : Fin P.size × Fin s)
    (x : Fin (U b).size) :
    fiberMap ((realize P L hL).map f) b (fiberPoint P L hL U b x)=fiberPoint P L hL V b (f b x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change indexMap P L hL f (index P U ⟨b,x⟩)=index P V ⟨b,f b x⟩
    change (index P V) ((trackMap P f) ((index P U).symm ((index P U) ⟨b,x⟩)))=_
    rw [Equiv.symm_apply_apply]
    rfl
  · rfl
noncomputable def evaluationRealize : 𝟭 (Obj P (s:=s)) ≅ realize P L hL ⋙ evaluation := by
  refine NatIso.ofComponents (fun U => asIso (show U ⟶ E.obj ((realize P L hL).obj U) from
    fun b => (fiberEquiv P L hL hLi U b).trans (enumerate ((realize P L hL).obj U) b))) ?_
  intro U V f
  funext b
  apply Equiv.ext
  intro x
  change enumerate ((realize P L hL).obj V) b (fiberPoint P L hL V b (f b x))=
    E.map ((realize P L hL).map f) b (enumerate ((realize P L hL).obj U) b (fiberPoint P L hL U b x))
  exact ((E_map_enum ((realize P L hL).map f) b (fiberPoint P L hL U b x)).trans
    (congrArg (enumerate ((realize P L hL).obj V) b) (fiberMap_realize P L hL f b x))).symm

include hL hLi

theorem evaluationEssSurj : (evaluation (P:=P) (L:=L)).EssSurj := {
  mem_essImage U := ⟨(realize P L hL).obj U,⟨(evaluationRealize P L hL hLi).app U |>.symm⟩⟩ }

theorem evaluationFull : (evaluation (P:=P) (L:=L)).Full := by
  let R := realize P L hL
  have : R.EssSurj := realize_essSurj P L hL hLi
  have : (R ⋙ evaluation (P:=P) (L:=L)).IsEquivalence :=
    Functor.isEquivalence_of_iso (evaluationRealize P L hL hLi)
  apply Functor.full_of_comp_essSurj (evaluation (P:=P) (L:=L)) R
  intro X Y φ
  refine ⟨R.map ((R ⋙ evaluation).preimage φ), ?_⟩
  exact (R ⋙ evaluation).map_preimage φ

theorem evaluationIsEquivalence : (evaluation (P:=P) (L:=L)).IsEquivalence := {
  faithful := inferInstance
  full := evaluationFull P L hL hLi
  essSurj := evaluationEssSurj P L hL hLi }
end SimpleAmenable.PolygonObject.LabelledStage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageNerveColimit
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage

variable {a n : ℕ} {S T : Stage a n} (h : S≤T)
noncomputable instance inclusionMonoidal : (inclusion h).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso U V := Iso.refl _
    μIso_hom_natural_left := by intros; apply UniformObject.Hom.ext; simp; rfl
    μIso_hom_natural_right := by intros; apply UniformObject.Hom.ext; simp; rfl
    associativity := by
      intro first second third
      apply UniformObject.Hom.ext
      change (Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫
        Labelled.assocHom first.obj second.obj third.obj) =
        (Labelled.assocHom first.obj second.obj third.obj ≫ Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _)
      simp only [Labelled.sumHom_id,Category.id_comp,Category.comp_id]
    left_unitality := by
      intro object
      apply UniformObject.Hom.ext
      change Labelled.leftHom object.obj =
        Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ Labelled.leftHom object.obj
      simp only [Labelled.sumHom_id,Category.id_comp]
    right_unitality := by
      intro object
      apply UniformObject.Hom.ext
      change Labelled.rightHom object.obj =
        Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ Labelled.rightHom object.obj
      simp only [Labelled.sumHom_id,Category.id_comp] }
noncomputable instance inclusionBraided : (inclusion h).Braided where
  braided U V := by
    change (𝟙 _ ≫ (inclusion h).map (β_ U V).hom) = (β_ ((inclusion h).obj U) ((inclusion h).obj V)).hom ≫ 𝟙 _
    simp only [Category.id_comp,Category.comp_id]
    apply UniformObject.Hom.ext
    rfl
@[simp] lemma inclusion_η : Functor.OplaxMonoidal.η (inclusion h)=𝟙 _ := rfl
@[simp] lemma inclusion_ε : Functor.LaxMonoidal.ε (inclusion h)=𝟙 _ := rfl
@[simp] lemma inclusion_μ (U V : S.Obj) : Functor.LaxMonoidal.μ (inclusion h) U V=𝟙 _ := rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram

variable {a n : ℕ} {I : Type} [Preorder I]
lemma map_inclusion_id (S : Stage a n) : Diagram.map (I:=I) (inclusion (le_refl S))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i; apply Iso.ext; apply UniformObject.Hom.ext
      simp [Diagram.map,mapObj]; rfl
    · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext; apply UniformObject.Hom.ext
      simp [Diagram.map,mapObj]; rfl
  · intro source target arrow; apply Hom.ext; intro first last ordered
    simp only [comp_app,Diagram.eqToHom_app]
    change arrow.app first last ordered = 𝟙 _ ≫ arrow.app first last ordered ≫ 𝟙 _
    simp
lemma map_inclusion_comp {S T U : Stage a n} (h : S≤T) (k : T≤U) :
    Diagram.map (I:=I) (inclusion (h.trans k)) = Diagram.map (inclusion h) ⋙ Diagram.map (inclusion k) := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i; apply Iso.ext; apply UniformObject.Hom.ext
      simp [Diagram.map,mapObj]; rfl
    · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext; apply UniformObject.Hom.ext
      simp [Diagram.map,mapObj]; rfl
  · intro source target arrow; apply Hom.ext; intro first last ordered
    simp only [comp_app,Diagram.eqToHom_app]
    change (inclusion (h.trans k)).map (arrow.app first last ordered) =
      𝟙 _ ≫ (inclusion (h.trans k)).map (arrow.app first last ordered) ≫ 𝟙 _
    simp
lemma map_inclusion_forget {S T : Stage a n} (h : S≤T) :
    Diagram.map (I:=I) (inclusion h) ⋙ Diagram.map T.forget=Diagram.map S.forget := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i; apply Iso.ext
      simp [Diagram.map,mapObj]; rfl
    · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext
      simp [Diagram.map,mapObj]; rfl
  · intro source target arrow; apply Hom.ext; intro first last ordered
    simp only [comp_app,Diagram.eqToHom_app]
    change S.forget.map (arrow.app first last ordered) =
      𝟙 _ ≫ S.forget.map (arrow.app first last ordered) ≫ 𝟙 _
    simp
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageIteratedMaps2
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram

variable {a n : ℕ} {I J K : Type} [Preorder I] [Preorder J] [Preorder K]
lemma map₂_inclusion_id (S : Stage a n) :
    Diagram.map (I:=J) (Diagram.map (I:=I) (inclusion (le_refl S)))=𝟭 _ := by
  have he (X : Diagram S.Obj I) : mapObj (inclusion (le_refl S)) X=X :=
    congrArg (fun F => F.obj X) (map_inclusion_id S)
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he _
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply heq_of_eq
      change (inclusion (le_refl S)).map ((A.unit i).hom.app j k h) ≫
        (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion (le_refl S)))).app j k h =
        (A.unit i).hom.app j k h
      rw [map_η_app,inclusion_η]
      apply UniformObject.Hom.ext
      exact Category.comp_id _
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      intro l m h
      simp [mapObj]; rfl
  · intro A B f
    apply Hom.ext; intro i j h
    apply Hom.ext; intro k l hkl
    simp only [comp_app,Diagram.eqToHom_app]
    change (f.app i j h).app k l hkl = 𝟙 _ ≫ (f.app i j h).app k l hkl ≫ 𝟙 _
    simp
lemma map₂_inclusion_comp_obj {S T U : Stage a n} (h : S≤T) (k : T≤U)
    (A : Diagram (Diagram S.Obj I) J) :
    mapObj (Diagram.map (I:=I) (inclusion (h.trans k))) A =
      mapObj (Diagram.map (inclusion k)) (mapObj (Diagram.map (inclusion h)) A) := by
  have he (X : Diagram S.Obj I) : mapObj (inclusion (h.trans k)) X=
    mapObj (inclusion k) (mapObj (inclusion h) X) :=
  congrArg (fun F => F.obj X) (map_inclusion_comp h k)
  refine ext_heq ?_ ?_ ?_
  · funext i j h; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro first last ordered
    apply heq_of_eq
    change (inclusion (h.trans k)).map ((A.unit i).hom.app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion (h.trans k)))).app first last ordered =
      (inclusion k).map ((inclusion h).map ((A.unit i).hom.app first last ordered) ≫
        (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion h))).app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion k))).app first last ordered
    simp only [map_η_app,inclusion_η]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro k
    apply hfunext; intro hij
    apply hfunext; intro hjk
    apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
    intro l m h
    simp [mapObj]; rfl
lemma map₂_inclusion_forget_obj {S T : Stage a n} (h : S≤T)
    (A : Diagram (Diagram S.Obj I) J) :
    mapObj (Diagram.map T.forget) (mapObj (Diagram.map (I:=I) (inclusion h)) A)=
      mapObj (Diagram.map S.forget) A := by
  have he (X : Diagram S.Obj I) : mapObj T.forget (mapObj (inclusion h) X)=mapObj S.forget X :=
  congrArg (fun F => F.obj X) (map_inclusion_forget h)
  refine ext_heq ?_ ?_ ?_
  · funext i j h; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro first last ordered
    apply heq_of_eq
    change T.forget.map ((inclusion h).map ((A.unit i).hom.app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion h))).app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) T.forget)).app first last ordered =
      S.forget.map ((A.unit i).hom.app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) S.forget)).app first last ordered
    simp only [map_η_app,inclusion_η,forget_η]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro k
    apply hfunext; intro hij
    apply hfunext; intro hjk
    apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
    intro l m h
    simp [mapObj]; rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_BooleanStepCoefficients
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace BooleanPartition
variable {a:ℕ}
lemma arrangement_color (P:BooleanPartition a) : HasSquareArrangement P.color := by
  choose S hS using fun b => polygon_hasSquareArrangement (P.polygon b)
  refine ⟨Finset.univ.biUnion S,fun p q hpq => ?_⟩
  have h := hS (P.color p) p q (fun l hl => hpq l (Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,hl⟩))
  exact ((decide_eq_decide.mp h).mp rfl).symm
lemma arrangement_values (P:BooleanPartition a) {K:Type*} (v:Fin P.size→K) :
    HasSquareArrangement (fun p => v (P.color p)) := by
  obtain ⟨S,hS⟩ := P.arrangement_color
  exact ⟨S,fun p q h => congrArg v (hS p q h)⟩

lemma exists_arrangement_partition {ι K:Type} [Fintype ι] (f:ι→GenericSquare a→K)
    (hf:∀i,HasSquareArrangement (f i)) :
    ∃P:BooleanPartition a,∀i p q,P.color p=P.color q → f i p=f i q := by
  choose S hS using hf
  let T := Finset.univ.biUnion S
  let C : T → polygonAlgebra a := fun l => ⟨_,halfPlane_mem a l.val.1 l.val.2⟩
  refine ⟨generated C,fun i p q hpq => hS i p q (fun l hl => ?_)⟩
  have h := generated_constant C hpq (⟨l,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hl⟩⟩:T)
  exact decide_eq_decide.mpr h
end BooleanPartition
variable (a:ℕ) (K:Type) [AddCommGroup K] [Module ℤ K]
noncomputable def booleanStepSubmodule : Submodule ℤ (GenericSquare a→K) where
  carrier := {f | HasSquareArrangement f}
  zero_mem' := ⟨∅,fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨S,hS⟩ ⟨T,hT⟩
    exact ⟨S∪T,fun p q h => congrArg₂ (·+·)
      (hS p q (fun l hl => h l (Finset.mem_union_left T hl)))
      (hT p q (fun l hl => h l (Finset.mem_union_right S hl)))⟩
  smul_mem' := by
    rintro r f ⟨S,hS⟩
    exact ⟨S,fun p q h => congrArg (r • ·) (hS p q h)⟩
noncomputable abbrev BooleanStep := ↥(booleanStepSubmodule a K)
namespace BooleanStep
variable {a K}
noncomputable def inflate (P:BooleanPartition a) : (Fin P.size→K) →ₗ[ℤ] BooleanStep a K where
  toFun v := ⟨fun p => v (P.color p),P.arrangement_values v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def evaluate (P:BooleanPartition a) : BooleanStep a K →ₗ[ℤ] (Fin P.size→K) where
  toFun f b := f.val (P.point b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [Module ℤ K] in
@[simp] lemma inflate_apply (P:BooleanPartition a) (v:Fin P.size→K) (p:GenericSquare a) :
    (inflate (K:=K) P v).val p=v (P.color p) := rfl
omit [Module ℤ K] in
@[simp] lemma evaluate_apply (P:BooleanPartition a) (v:BooleanStep a K) (b:Fin P.size) :
    evaluate (K:=K) P v b=v.val (P.point b) := rfl
omit [Module ℤ K] in
lemma evaluate_inflate (P:BooleanPartition a) : (evaluate (K:=K) P).comp (inflate (K:=K) P)=LinearMap.id := by
  apply LinearMap.ext; intro v; funext i
  simp only [LinearMap.comp_apply,evaluate_apply,inflate_apply,BooleanPartition.color_point,LinearMap.id_apply]
omit [Module ℤ K] in
lemma inflate_injective (P:BooleanPartition a) : Function.Injective (inflate (K:=K) P) := by
  intro x y h
  have hh := congrArg (evaluate (K:=K) P) h
  change ((evaluate (K:=K) P).comp (inflate (K:=K) P)) x=((evaluate (K:=K) P).comp (inflate (K:=K) P)) y at hh
  simpa only [evaluate_inflate,LinearMap.id_apply] using hh
noncomputable def refinement {P Q:BooleanPartition a} (_h:P.Refines Q) :
    (Fin P.size→K) →ₗ[ℤ] (Fin Q.size→K) := (evaluate (K:=K) Q).comp (inflate (K:=K) P)
omit [Module ℤ K] in
lemma inflate_refinement {P Q:BooleanPartition a} (h:P.Refines Q) :
    (inflate (K:=K) Q).comp (refinement h)=inflate (K:=K) P := by
  apply LinearMap.ext; intro v; apply Subtype.ext; funext p
  change v (P.color (Q.point (Q.color p)))=v (P.color p)
  exact congrArg v (h _ _ (Q.color_point (Q.color p)))
omit [Module ℤ K] in
lemma exists_common {ι:Type} [Fintype ι] (f:ι→BooleanStep a K) :
    ∃P:BooleanPartition a,∀i,inflate (K:=K) P (evaluate (K:=K) P (f i))=f i := by
  obtain ⟨P,hP⟩ := BooleanPartition.exists_arrangement_partition (fun i => (f i).val) (fun i => (f i).property)
  refine ⟨P,fun i => ?_⟩
  apply Subtype.ext; funext p
  exact hP i _ _ (P.color_point (P.color p))
end BooleanStep
end SimpleAmenable.PolygonObject

end

section
open _root_.CategoryTheory Classical Set TensorProduct
namespace SimpleAmenable.PolygonObject.BooleanStep

variable {a:ℕ} {K:Type} [AddCommGroup K]
noncomputable def multiply : BooleanStep a ℤ →ₗ[ℤ] K →ₗ[ℤ] BooleanStep a K where
  toFun f := {
    toFun k := ⟨fun p => f.val p • k,by
      obtain ⟨S,hS⟩ := f.property
      exact ⟨S,fun p q h => congrArg (· • k) (hS p q h)⟩⟩
    map_add' x y := by apply Subtype.ext; funext p; change f.val p • (x+y)=f.val p • x+f.val p • y; exact smul_add _ _ _
    map_smul' r k := by apply Subtype.ext; funext p; change f.val p • (r • k)=r • (f.val p • k); exact smul_comm _ _ _ }
  map_add' f g := by ext k p; exact add_smul _ _ _
  map_smul' r f := by
    apply LinearMap.ext; intro k; apply Subtype.ext; funext p
    change (r • f.val p) • k = r • (f.val p • k)
    exact smul_assoc r (f.val p) k
noncomputable def tensorMap : BooleanStep a ℤ ⊗[ℤ] K →ₗ[ℤ] BooleanStep a K :=
  TensorProduct.lift multiply
@[simp] lemma tensorMap_tmul (f:BooleanStep a ℤ) (k:K) (p:GenericSquare a) :
    (tensorMap (a:=a) (K:=K) (f ⊗ₜ[ℤ] k)).val p=f.val p • k := rfl
noncomputable def finiteTensorEquiv (P:BooleanPartition a) :
    (Fin P.size→ℤ) ⊗[ℤ] K ≃ₗ[ℤ] (Fin P.size→K) :=
  TensorProduct.comm ℤ _ _ ≪≫ₗ TensorProduct.piScalarRight ℤ ℤ K (Fin P.size)
@[simp] lemma finiteTensorEquiv_tmul (P:BooleanPartition a) (v:Fin P.size→ℤ) (k:K) :
    finiteTensorEquiv (K:=K) P (v ⊗ₜ[ℤ] k)=fun i => v i • k := by
  change TensorProduct.piScalarRightHom ℤ ℤ K (Fin P.size) (k ⊗ₜ[ℤ] v)=_
  exact TensorProduct.piScalarRightHom_tmul ℤ ℤ K (Fin P.size) k v
noncomputable def tensorInflate (P:BooleanPartition a) :
    (Fin P.size→ℤ) ⊗[ℤ] K →ₗ[ℤ] BooleanStep a ℤ ⊗[ℤ] K :=
  TensorProduct.map (inflate (K:=ℤ) P) LinearMap.id
lemma tensorMap_inflate (P:BooleanPartition a) :
    (tensorMap (a:=a) (K:=K)).comp (tensorInflate P) =
      (inflate (K:=K) P).comp (finiteTensorEquiv (K:=K) P).toLinearMap := by
  apply TensorProduct.ext'; intro v k; apply Subtype.ext; funext p
  change v (P.color p) • k=finiteTensorEquiv (K:=K) P (v ⊗ₜ[ℤ] k) (P.color p)
  rw [finiteTensorEquiv_tmul]
lemma tensorInflate_refinement {P Q:BooleanPartition a} (h:P.Refines Q) :
    (tensorInflate (K:=K) Q).comp (TensorProduct.map (refinement (K:=ℤ) h) LinearMap.id)=
      tensorInflate P := by
  apply TensorProduct.ext'; intro v k
  exact congrArg (fun f => f ⊗ₜ[ℤ] k) (LinearMap.congr_fun (inflate_refinement (K:=ℤ) h) v)
lemma exists_tensor_stage (x:BooleanStep a ℤ ⊗[ℤ] K) :
    ∃P:BooleanPartition a,∃v:(Fin P.size→ℤ) ⊗[ℤ] K,tensorInflate P v=x := by
  induction x using OAI.tensorInductionOn with
  | tmul f k =>
    obtain ⟨P,hP⟩ := exists_common (fun _:Fin 1 => f)
    refine ⟨P,evaluate (K:=ℤ) P f ⊗ₜ[ℤ] k,?_⟩
    change inflate (K:=ℤ) P (evaluate (K:=ℤ) P f) ⊗ₜ[ℤ] k = f ⊗ₜ[ℤ] k
    rw [hP 0]
  | add x y hx hy =>
    obtain ⟨P,v,rfl⟩ := hx
    obtain ⟨Q,w,rfl⟩ := hy
    let T := P.join Q
    let hP : P.Refines T := P.le_join_left Q
    let hQ : Q.Refines T := P.le_join_right Q
    refine ⟨T,TensorProduct.map (refinement hP) LinearMap.id v+
      TensorProduct.map (refinement hQ) LinearMap.id w,?_⟩
    rw [map_add]
    exact congrArg₂ (·+·) (LinearMap.congr_fun (tensorInflate_refinement (K:=K) hP) v)
      (LinearMap.congr_fun (tensorInflate_refinement (K:=K) hQ) w)
lemma tensorMap_injective : Function.Injective (tensorMap (a:=a) (K:=K)) := by
  apply (tensorMap (a:=a) (K:=K)).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨P,v,rfl⟩ := exists_tensor_stage x
  have hv : inflate (K:=K) P (finiteTensorEquiv (K:=K) P v)=0 := by
    change ((inflate (K:=K) P).comp (finiteTensorEquiv (K:=K) P).toLinearMap) v=0
    rw [←tensorMap_inflate]
    exact hx
  have hv0 : finiteTensorEquiv (K:=K) P v=0 := inflate_injective P (hv.trans (map_zero _).symm)
  have h := (finiteTensorEquiv (K:=K) P).injective (hv0.trans (map_zero _).symm)
  rw [h,map_zero]
lemma tensorMap_surjective : Function.Surjective (tensorMap (a:=a) (K:=K)) := by
  intro f
  obtain ⟨P,hP⟩ := exists_common (fun _:Fin 1 => f)
  refine ⟨tensorInflate P ((finiteTensorEquiv (K:=K) P).symm (evaluate (K:=K) P f)),?_⟩
  change ((tensorMap (a:=a) (K:=K)).comp (tensorInflate P)) _ = _
  rw [tensorMap_inflate,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  exact hP 0

noncomputable def tensorEquiv : SquareStep a ⊗[ℤ] K ≃ₗ[ℤ] BooleanStep a K :=
  LinearEquiv.ofBijective tensorMap ⟨tensorMap_injective,tensorMap_surjective⟩
end SimpleAmenable.PolygonObject.BooleanStep

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FilteredHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StageProductColimit.instEssSurjForallPowerMap _root_.OAI.StageProductColimit.instFullForallPowerMap _root_.OAI.StageProductColimit.instIsEquivalenceForallPowerMap _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open StageProductColimit

variable {a n : ℕ} (κ : Type)
noncomputable def productStage : Stage a n ⥤ Cat.{0,0} where
  obj S := Cat.of (κ → S.Obj)
  map h := (powerMap κ (inclusion (leOfHom h))).toCatHom
  map_id S := by
    apply Cat.ext
    change powerMap κ (inclusion (le_refl S))=𝟭 _
    rw [inclusion_id]; rfl
  map_comp h k := by
    apply Cat.ext
    change powerMap κ (inclusion ((leOfHom h).trans (leOfHom k)))=
      powerMap κ (inclusion (leOfHom h)) ⋙ powerMap κ (inclusion (leOfHom k))
    rw [←powerMap_comp,←inclusion_comp]
noncomputable def productCocone : Cocone (productStage (a:=a) (n:=n) κ) where
  pt := Cat.of (κ → Labelled a n)
  ι := {
    app S := (powerMap κ S.forget).toCatHom
    naturality S T h := by
      apply Cat.ext
      change powerMap κ (inclusion (leOfHom h)) ⋙ powerMap κ T.forget=powerMap κ S.forget
      rw [←powerMap_comp,inclusion_forget] }
noncomputable def productNerveCocone : Cocone (productStage (a:=a) (n:=n) κ ⋙ nerveFunctor) :=
  nerveFunctor.mapCocone (productCocone κ)
lemma exists_lift_product [Fintype κ] {K : Type} [Category.{0} K] [Fintype K]
    [∀i j:K,Fintype (i ⟶ j)] (F : K ⥤ (κ → Labelled a n)) :
    ∃S : Stage a n,∃G : K ⥤ (κ → S.Obj),G ⋙ powerMap κ S.forget=F := by
  let τ := κ × (Σk:K,Σl:K,k ⟶ l)
  let U : κ × K → Labelled a n := fun t => F.obj t.2 t.1
  let src : τ → κ × K := fun t => (t.1,t.2.1)
  let dst : τ → κ × K := fun t => (t.1,t.2.2.1)
  let f : ∀t,U (src t) ⟶ U (dst t) := fun t => F.map t.2.2.2 t.1
  obtain ⟨S,hP,hL,hf⟩ := exists_lift_family U src dst f
  let G : K ⥤ (κ → S.Obj) := {
    obj k i := ⟨F.obj k i,hP (i,k),hL (i,k)⟩
    map {k l} g i := ⟨F.map g i,hf (i,⟨k,l,g⟩)⟩
    map_id k := by funext i; apply UniformObject.Hom.ext; exact congrFun (F.map_id k) i
    map_comp g h := by funext i; apply UniformObject.Hom.ext; exact congrFun (F.map_comp g h) i }
  exact ⟨S,G,rfl⟩
noncomputable def productNerveIsColimit [Fintype κ] :
    IsColimit (productNerveCocone (a:=a) (n:=n) κ) := by
  apply evaluationJointlyReflectsColimits
  intro p
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨S,G,h⟩ := exists_lift_product κ x
    exact ⟨S,G,h.symm⟩
  · intro S x y h
    have he : x=y := StageNerveColimit.comp_injective (powerMap κ S.forget)
      (powerMap_injective κ S.forget (forget_injective S)) h
    exact ⟨S,𝟙 S,congrArg _ he⟩
noncomputable def productHomologyIsColimit [Fintype κ] (q:ℕ) : IsColimit
    ((SSet.homologyFunctor (ModuleCat.of ℤ ℤ) q).mapCocone
      (productNerveCocone (a:=a) (n:=n) κ)) :=
  isColimitOfPreserves _ (productNerveIsColimit κ)
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_StageCoefficients
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.inclusionBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.inclusionMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n:ℕ} {K:Type} [AddCommGroup K]
noncomputable abbrev Coefficients (a n:ℕ) (K:Type) [AddCommGroup K] :=
  ReducedLabel n →₀ BooleanStep a K
namespace Stage
variable (S:Stage a n)
noncomputable def label (j:Fin S.support.card) : ReducedLabel n := ⟨S.L j,S.L_reduced j⟩
lemma label_injective : Function.Injective S.label := fun _ _ equality => S.L_injective (congrArg Subtype.val equality)
lemma label_mem_support (j:Fin S.support.card) : S.label j∈S.support :=
  (S.label_mem _ _).mp ⟨j,rfl⟩
lemma label_range (l:ReducedLabel n) : (∃j,S.label j=l) ↔ l∈S.support := by
  simpa only [label,Subtype.ext_iff] using S.label_mem l.val l.property
noncomputable def realize : (Fin S.partition.size × Fin S.support.card → K) →ₗ[ℤ] Coefficients a n K :=
  ∑j:Fin S.support.card,
    (Finsupp.lsingle (S.label j)).comp
      ((BooleanStep.inflate (K:=K) S.partition).comp (LinearMap.funLeft ℤ K (fun i => (i,j))))
lemma realize_at_label (v:Fin S.partition.size × Fin S.support.card → K) (j:Fin S.support.card) :
    (S.realize (K:=K) v) (S.label j) = BooleanStep.inflate (K:=K) S.partition (fun i => v (i,j)) := by
  simp only [realize,LinearMap.sum_apply,LinearMap.comp_apply,Finsupp.lsingle_apply,Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finsupp.single_eq_same]; rfl
  · intro k hk hkj
    exact Finsupp.single_eq_of_ne (fun e => hkj (S.label_injective e.symm))
  · intro h; exact False.elim (h (Finset.mem_univ _))
lemma realize_outside (v:Fin S.partition.size × Fin S.support.card → K) (l:ReducedLabel n)
    (hl:l∉S.support) : (S.realize (K:=K) v) l=0 := by
  simp only [realize,LinearMap.sum_apply,LinearMap.comp_apply,Finsupp.lsingle_apply,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero; intro j hj
  exact Finsupp.single_eq_of_ne (fun e => hl (e.symm ▸ S.label_mem_support j))
noncomputable def coefficientEvaluate : Coefficients a n K →ₗ[ℤ] (Fin S.partition.size × Fin S.support.card → K) where
  toFun f c := (f (S.label c.2)).val (S.partition.point c.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma coefficientEvaluate_realize :
    (S.coefficientEvaluate (K:=K)).comp S.realize=LinearMap.id := by
  apply LinearMap.ext; intro v; funext c
  change (S.realize (K:=K) v (S.label c.2)).val (S.partition.point c.1)=v c
  rw [realize_at_label,BooleanStep.inflate_apply,S.partition.color_point]
lemma realize_injective : Function.Injective (S.realize (K:=K)) := by
  intro v w h
  have hh := congrArg (S.coefficientEvaluate (K:=K)) h
  change ((S.coefficientEvaluate (K:=K)).comp S.realize) v=((S.coefficientEvaluate (K:=K)).comp S.realize) w at hh
  simpa only [coefficientEvaluate_realize,LinearMap.id_apply] using hh

def Admissible (f:Coefficients a n K) : Prop :=
  f.support ⊆ S.support ∧ ∀l p q,S.partition.color p=S.partition.color q → (f l).val p=(f l).val q
lemma realize_admissible (v:Fin S.partition.size × Fin S.support.card → K) : S.Admissible (S.realize (K:=K) v) := by
  constructor
  · intro l hl
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hl) (S.realize_outside v l hn)
  · intro l p q hpq
    by_cases hl:l∈S.support
    · obtain ⟨j,rfl⟩ := (S.label_range l).mpr hl
      rw [S.realize_at_label,BooleanStep.inflate_apply,BooleanStep.inflate_apply,hpq]
    · rw [S.realize_outside v l hl]; rfl
lemma realize_coefficientEvaluate (f:Coefficients a n K) (hf:S.Admissible f) :
    S.realize (K:=K) (S.coefficientEvaluate (K:=K) f)=f := by
  apply Finsupp.ext; intro l
  by_cases hl:l∈S.support
  · obtain ⟨j,rfl⟩ := (S.label_range l).mpr hl
    rw [realize_at_label]
    apply Subtype.ext; funext p
    exact hf.2 _ _ _ (S.partition.color_point (S.partition.color p))
  · rw [realize_outside _ _ _ hl]
    exact (Finsupp.notMem_support_iff.mp (fun h => hl (hf.1 h))).symm
lemma admissible_mono {T:Stage a n} (h:S≤T) {f:Coefficients a n K} (hf:S.Admissible f) :
    T.Admissible f := ⟨hf.1.trans h.2,fun l p q hpq => hf.2 l p q (h.1 p q hpq)⟩
variable {S}
noncomputable def coefficientRefinement {T:Stage a n} (_h:S≤T) :
    (Fin S.partition.size × Fin S.support.card →K) →ₗ[ℤ] (Fin T.partition.size × Fin T.support.card →K) :=
  (T.coefficientEvaluate (K:=K)).comp S.realize
lemma realize_refinement {T:Stage a n} (h:S≤T) :
    (T.realize (K:=K)).comp (coefficientRefinement h)=S.realize (K:=K) := by
  apply LinearMap.ext; intro v
  exact T.realize_coefficientEvaluate _ (S.admissible_mono h (S.realize_admissible v))
lemma exists_coefficient_stage (f:Coefficients a n K) : ∃S:Stage a n,S.Admissible f := by
  obtain ⟨P,hP⟩ := BooleanStep.exists_common (fun l:f.support => f l.val)
  refine ⟨⟨P,f.support⟩,Subset.rfl,?_⟩
  intro l p q hpq
  by_cases hl:l∈f.support
  · have h := congrArg Subtype.val (hP ⟨l,hl⟩)
    exact (congrFun h p).symm.trans ((congrArg (fun i => (BooleanStep.evaluate (K:=K) P (f l)) i) hpq).trans (congrFun h q))
  · rw [Finsupp.notMem_support_iff.mp hl]; rfl
end Stage
end SimpleAmenable.PolygonObject.LabelledStage

end

section
open _root_.CategoryTheory Limits Classical Set
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage

variable {a n:ℕ} (K:Type) [AddCommGroup K]
noncomputable def coefficientDiagram : Stage a n ⥤ ModuleCat ℤ where
  obj S := ModuleCat.of ℤ (Fin S.partition.size × Fin S.support.card→K)
  map h := ModuleCat.ofHom (coefficientRefinement (K:=K) (leOfHom h))
  map_id S := by
    apply ModuleCat.hom_ext
    exact coefficientEvaluate_realize S
  map_comp {S T U} h k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext; intro v
    change U.coefficientEvaluate (K:=K) (S.realize (K:=K) v) =
      U.coefficientEvaluate (K:=K) (T.realize (K:=K) (coefficientRefinement (K:=K) (leOfHom h) v))
    exact congrArg (U.coefficientEvaluate (K:=K)) (LinearMap.congr_fun (realize_refinement (K:=K) (leOfHom h)) v).symm
noncomputable def coefficientCocone : Cocone (coefficientDiagram (a:=a) (n:=n) K) where
  pt := ModuleCat.of ℤ (Coefficients a n K)
  ι := {
    app S := ModuleCat.ofHom (S.realize (K:=K))
    naturality _ _ h := ModuleCat.hom_ext (realize_refinement (K:=K) (leOfHom h)) }

noncomputable def coefficientIsColimit : IsColimit (coefficientCocone (a:=a) (n:=n) K) := by
  apply isColimitOfReflects (CategoryTheory.forget (ModuleCat ℤ))
  apply Types.FilteredColimit.isColimitOf'
  · intro f
    obtain ⟨S,hS⟩ := exists_coefficient_stage f
    exact ⟨S,S.coefficientEvaluate (K:=K) f,(S.realize_coefficientEvaluate f hS).symm⟩
  · intro S v w h
    have hvw := S.realize_injective h
    exact ⟨S,𝟙 S,congrArg _ hvw⟩
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageTripleHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open StageProductColimit IntervalBar IntervalBar.Diagram ColimitTransfer

variable {a n : ℕ} (l m p q : ℕ)
noncomputable def tripleEvalIso (C : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] :
    (H q).obj (Cat.of (tripleDegree l m p C)) ≅ (H q).obj (Cat.of (Fin l × (Fin m × Fin p) → C)) :=
  NerveHomotopy.homologyIso (eval₃ l m p).asEquivalence (ModuleCat.of ℤ ℤ) q
noncomputable def tripleHomologyStage : Stage a n ⥤ ModuleCat ℤ :=
  transportDiagram (productStage (a:=a) (n:=n) (Fin l × (Fin m × Fin p)) ⋙ H q)
    (fun S => (H q).obj (Cat.of (tripleDegree l m p S.Obj)))
    (fun S => tripleEvalIso l m p q S.Obj)
noncomputable def tripleHomologyCocone : Cocone (tripleHomologyStage (a:=a) (n:=n) l m p q) :=
  transportCocone ((H q).mapCocone (productCocone (a:=a) (n:=n) (Fin l × (Fin m × Fin p))))
    (fun S => (H q).obj (Cat.of (tripleDegree l m p S.Obj)))
    (fun S => tripleEvalIso l m p q S.Obj)
    ((H q).obj (Cat.of (tripleDegree l m p (Labelled a n))))
    (tripleEvalIso l m p q (Labelled a n))

noncomputable def tripleHomologyIsColimit :
    IsColimit (tripleHomologyCocone (a:=a) (n:=n) l m p q) :=
  transportIsColimit _ _ _ _ _ (productHomologyIsColimit _ q)
variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
lemma tripleEvalIso_hom (C : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] :
    (tripleEvalIso l m p q C).hom = (H q).map (eval₃ (C:=C) l m p).toCatHom := rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram

variable {a n : ℕ} (l m p : ℕ)
lemma map₃_inclusion_comp_obj {S T U : Stage a n} (h:S≤T) (k:T≤U)
    (A : tripleDegree l m p S.Obj) :
    mapObj (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (h.trans k)))) A =
      mapObj (Diagram.map (Diagram.map (inclusion k))) (mapObj (Diagram.map (Diagram.map (inclusion h))) A) := by
  have he (X : Diagram (Diagram S.Obj (Fin (p+1))) (Fin (m+1))) :
      mapObj (Diagram.map (inclusion (h.trans k))) X=
        mapObj (Diagram.map (inclusion k)) (mapObj (Diagram.map (inclusion h)) X) :=
    map₂_inclusion_comp_obj h k X
  have he₁ (X : Diagram S.Obj (Fin (p+1))) : mapObj (inclusion (h.trans k)) X=
      mapObj (inclusion k) (mapObj (inclusion h) X) :=
    congrArg (fun F=>F.obj X) (map_inclusion_comp h k)
  refine ext_heq ?_ ?_ ?_
  · funext i j hij; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j z hjz
    apply hom_hext (he₁ _) rfl
    intro v w hvw
    apply heq_of_eq
    change (inclusion (h.trans k)).map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) (inclusion (h.trans k))))).app j z hjz).app v w hvw =
      (inclusion k).map ((inclusion h).map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
        ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
          (Diagram.map (I:=Fin (p+1)) (inclusion h)))).app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) (inclusion k)))).app j z hjz).app v w hvw
    simp only [map₂_η_app,inclusion_η]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro z
    apply hfunext; intro hij
    apply hfunext; intro hjz
    apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    intro v w hvw
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he₁ _) (he₁ _)) (he₁ _)
    intro x y hxy
    simp only [mapObj,Functor.mapIso_hom,Iso.trans_hom,Functor.Monoidal.μIso_hom,
      map₂_μ_app,comp_app,map_map_app,inclusion_μ,Functor.map_comp]
    rfl
lemma map₃_inclusion_comp {S T U : Stage a n} (h:S≤T) (k:T≤U) :
    Diagram.map (I:=Fin (l+1)) (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (h.trans k)))) =
      Diagram.map (Diagram.map (Diagram.map (inclusion h))) ⋙ Diagram.map (Diagram.map (Diagram.map (inclusion k))) := by
  refine CategoryTheory.Functor.hext (map₃_inclusion_comp_obj l m p h k) ?_
  intro A B f
  apply hom_hext (map₃_inclusion_comp_obj l m p h k A) (map₃_inclusion_comp_obj l m p h k B)
  intro i j hij
  apply hom_hext (map₂_inclusion_comp_obj h k _) (map₂_inclusion_comp_obj h k _)
  intro v w hvw
  apply hom_hext
    (congrArg (fun F => F.obj ((A.obj i j hij).obj v w hvw)) (map_inclusion_comp h k))
    (congrArg (fun F => F.obj ((B.obj i j hij).obj v w hvw)) (map_inclusion_comp h k))
  intro x y hxy
  rfl
lemma map₃_inclusion_forget_obj {S T : Stage a n} (h:S≤T)
    (A : tripleDegree l m p S.Obj) :
    mapObj (Diagram.map (Diagram.map T.forget))
      (mapObj (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion h))) A) =
      mapObj (Diagram.map (Diagram.map S.forget)) A := by
  have he (X : Diagram (Diagram S.Obj (Fin (p+1))) (Fin (m+1))) :
      mapObj (Diagram.map T.forget) (mapObj (Diagram.map (inclusion h)) X)=
        mapObj (Diagram.map S.forget) X := map₂_inclusion_forget_obj h X
  have he₁ (X : Diagram S.Obj (Fin (p+1))) : mapObj T.forget (mapObj (inclusion h) X)=
      mapObj S.forget X := congrArg (fun F=>F.obj X) (map_inclusion_forget h)
  refine ext_heq ?_ ?_ ?_
  · funext i j hij; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j z hjz
    apply hom_hext (he₁ _) rfl
    intro v w hvw
    apply heq_of_eq
    change T.forget.map ((inclusion h).map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) (inclusion h)))).app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) T.forget))).app j z hjz).app v w hvw =
      S.forget.map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) S.forget))).app j z hjz).app v w hvw
    simp only [map₂_η_app,inclusion_η,forget_η]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro z
    apply hfunext; intro hij
    apply hfunext; intro hjz
    apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    intro v w hvw
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he₁ _) (he₁ _)) (he₁ _)
    intro x y hxy
    simp only [mapObj,Functor.mapIso_hom,Iso.trans_hom,Functor.Monoidal.μIso_hom,
      map₂_μ_app,comp_app,map_map_app,forget_μ,Functor.map_comp]
    rfl
lemma map₃_inclusion_forget {S T : Stage a n} (h:S≤T) :
    Diagram.map (I:=Fin (l+1)) (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion h))) ⋙
      Diagram.map (Diagram.map (Diagram.map T.forget)) = Diagram.map (Diagram.map (Diagram.map S.forget)) := by
  refine CategoryTheory.Functor.hext (map₃_inclusion_forget_obj l m p h) ?_
  intro A B f
  apply hom_hext (map₃_inclusion_forget_obj l m p h A) (map₃_inclusion_forget_obj l m p h B)
  intro i j hij
  apply hom_hext (map₂_inclusion_forget_obj h _) (map₂_inclusion_forget_obj h _)
  intro v w hvw
  apply hom_hext
    (congrArg (fun F => F.obj ((A.obj i j hij).obj v w hvw)) (map_inclusion_forget h))
    (congrArg (fun F => F.obj ((B.obj i j hij).obj v w hvw)) (map_inclusion_forget h))
  intro x y hxy
  rfl
lemma map₃_inclusion_id_obj (S : Stage a n) (A : tripleDegree l m p S.Obj) :
    mapObj (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (le_refl S)))) A=A := by
  have he (X : Diagram (Diagram S.Obj (Fin (p+1))) (Fin (m+1))) :
      mapObj (Diagram.map (inclusion (le_refl S))) X=X :=
    congrArg (fun F=>F.obj X) (map₂_inclusion_id S)
  have he₁ (X : Diagram S.Obj (Fin (p+1))) : mapObj (inclusion (le_refl S)) X=X :=
    congrArg (fun F=>F.obj X) (map_inclusion_id S)
  refine ext_heq ?_ ?_ ?_
  · funext i j hij; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j z hjz
    apply hom_hext (he₁ _) rfl
    intro v w hvw
    apply heq_of_eq
    change (inclusion (le_refl S)).map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) (inclusion (le_refl S))))).app j z hjz).app v w hvw =
      ((A.unit i).hom.app j z hjz).app v w hvw
    rw [map₂_η_app,inclusion_η]
    apply UniformObject.Hom.ext
    exact Category.comp_id _
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro z
    apply hfunext; intro hij
    apply hfunext; intro hjz
    apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    intro v w hvw
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he₁ _) (he₁ _)) (he₁ _)
    intro x y hxy
    simp only [mapObj,Functor.mapIso_hom,Iso.trans_hom,Functor.Monoidal.μIso_hom,
      comp_app,map_map_app]
    rfl
lemma map₃_inclusion_id (S : Stage a n) :
    Diagram.map (I:=Fin (l+1)) (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (le_refl S))))=𝟭 _ := by
  refine CategoryTheory.Functor.hext (map₃_inclusion_id_obj l m p S) ?_
  intro A B f
  apply hom_hext (map₃_inclusion_id_obj l m p S A) (map₃_inclusion_id_obj l m p S B)
  intro i j hij
  apply hom_hext
    (congrArg (fun F => F.obj (A.obj i j hij)) (map₂_inclusion_id S))
    (congrArg (fun F => F.obj (B.obj i j hij)) (map₂_inclusion_id S))
  intro v w hvw
  apply hom_hext
    (congrArg (fun F => F.obj ((A.obj i j hij).obj v w hvw)) (map_inclusion_id S))
    (congrArg (fun F => F.obj ((B.obj i j hij).obj v w hvw)) (map_inclusion_id S))
  intro x y hxy
  rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.inclusionBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.inclusionMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.UniformObject

variable {a n s : ℕ} {P : BooleanPartition a} {L : Fin s → Fin n → CutRing × CutRing}
noncomputable def muEval (U V : UniformObject P L) (b : Fin P.size × Fin s) :
    FiniteSetGroupoid.sum (E.obj U b) (E.obj V b) ⟶ E.obj (sum U V) b := mu U V b
@[simp] lemma muEval_inl (U V : UniformObject P L) (b : Fin P.size × Fin s) (x : Fiber U b) :
    muEval U V b (FiniteSetGroupoid.sumEquiv _ _ (.inl (enumerate U b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inl x)) := mu_inl U V b x
@[simp] lemma muEval_inr (U V : UniformObject P L) (b : Fin P.size × Fin s) (x : Fiber V b) :
    muEval U V b (FiniteSetGroupoid.sumEquiv _ _ (.inr (enumerate V b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inr x)) := mu_inr U V b x
noncomputable def epsEval (b : Fin P.size × Fin s) :
    FiniteSetGroupoid.empty ⟶ E.obj (empty (P:=P) (L:=L)) b := eps b
lemma mu_assoc (U V W : UniformObject P L) :
    mu U V ▷ E.obj W ≫ mu (U⊗V) W ≫ E.map (α_ U V W).hom =
      (α_ (E.obj U) (E.obj V) (E.obj W)).hom ≫ E.obj U ◁ mu V W ≫ mu U (V⊗W) := by
  funext b
  apply Equiv.ext
  intro x
  change E.map (assocHom U V W) b (muEval (sum U V) W b
      (FiniteSetGroupoid.sumHom (muEval U V b) (𝟙 (E.obj W b)) x)) =
    muEval U (sum V W) b (FiniteSetGroupoid.sumHom (𝟙 (E.obj U b)) (muEval V W b)
      (FiniteSetGroupoid.assoc (E.obj U b) (E.obj V b) (E.obj W b) x))
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (FiniteSetGroupoid.sum (E.obj U b) (E.obj V b)) (E.obj W b)).surjective x
  cases x with
  | inl x =>
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      rw [FiniteSetGroupoid.sumHom_inl (muEval U V b) (𝟙 (E.obj W b)),muEval_inl,muEval_inl,E_map_enum,fiber_assoc_left,
        FiniteSetGroupoid.assoc_left,FiniteSetGroupoid.sumHom_inl,FiniteSetGroupoid.id_apply,muEval_inl]
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      rw [FiniteSetGroupoid.sumHom_inl (muEval U V b) (𝟙 (E.obj W b)),muEval_inr,muEval_inl,E_map_enum,fiber_assoc_mid,
        FiniteSetGroupoid.assoc_mid,FiniteSetGroupoid.sumHom_inr,muEval_inl,muEval_inr]
  | inr x =>
    obtain ⟨x,rfl⟩ := (enumerate W b).surjective x
    rw [FiniteSetGroupoid.sumHom_inr (muEval U V b) (𝟙 (E.obj W b)),FiniteSetGroupoid.id_apply,muEval_inr,E_map_enum,fiber_assoc_right,
      FiniteSetGroupoid.assoc_right,FiniteSetGroupoid.sumHom_inr,muEval_inr,muEval_inr]
lemma eps_left (U : UniformObject P L) :
    (λ_ (E.obj U)).hom = eps ▷ E.obj U ≫ mu (𝟙_ _) U ≫ E.map (λ_ U).hom := by
  funext b
  apply Equiv.ext
  intro x
  change FiniteSetGroupoid.left (E.obj U b) x = E.map (leftHom U) b
    (muEval empty U b (FiniteSetGroupoid.sumHom (epsEval b) (𝟙 (E.obj U b)) x))
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv FiniteSetGroupoid.empty (E.obj U b)).surjective x
  cases x with
  | inl x => exact Fin.elim0 x
  | inr x =>
    obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
    rw [FiniteSetGroupoid.left_apply,FiniteSetGroupoid.sumHom_inr (epsEval b) (𝟙 (E.obj U b)),
      FiniteSetGroupoid.id_apply,muEval_inr,E_map_enum,fiber_left]
lemma eps_right (U : UniformObject P L) :
    (ρ_ (E.obj U)).hom = E.obj U ◁ eps ≫ mu U (𝟙_ _) ≫ E.map (ρ_ U).hom := by
  funext b
  apply Equiv.ext
  intro x
  change FiniteSetGroupoid.right (E.obj U b) x = E.map (rightHom U) b
    (muEval U empty b (FiniteSetGroupoid.sumHom (𝟙 (E.obj U b)) (epsEval b) x))
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) FiniteSetGroupoid.empty).surjective x
  cases x with
  | inl x =>
    obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
    rw [FiniteSetGroupoid.right_apply,FiniteSetGroupoid.sumHom_inl (𝟙 (E.obj U b)) (epsEval b),
      FiniteSetGroupoid.id_apply,muEval_inl,E_map_enum,fiber_right]
  | inr x => exact Fin.elim0 x
noncomputable instance evaluationMonoidal : (evaluation (P:=P) (L:=L)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso eps
    μIso U V := asIso (mu U V)
    μIso_hom_natural_left := by intro U V f W; simpa using mu_natural f (𝟙 W)
    μIso_hom_natural_right := by intro U V W f; simpa using mu_natural (𝟙 W) f
    associativity := mu_assoc
    left_unitality := eps_left
    right_unitality := eps_right }
noncomputable instance evaluationBraided : (evaluation (P:=P) (L:=L)).Braided where
  braided U V := by
    change mu U V ≫ E.map (swapHom U V) = (β_ (E.obj U) (E.obj V)).hom ≫ mu V U
    funext b
    apply Equiv.ext
    intro x
    change E.map (swapHom U V) b (muEval U V b x) =
      muEval V U b (FiniteSetGroupoid.swap (E.obj U b) (E.obj V b) x)
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      rw [muEval_inl,E_map_enum,fiber_swap_left,FiniteSetGroupoid.swap_left,muEval_inr]
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      rw [muEval_inr,E_map_enum,fiber_swap_right,FiniteSetGroupoid.swap_right,muEval_inl]
end SimpleAmenable.PolygonObject.LabelledStage.UniformObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PowerDiagonal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.connected _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower

variable {a n : ℕ} (S : Stage a n)
noncomputable def finiteProductComparison : bar₃ (C:=S.Obj) ⟶
    (power (Fin S.partition.size × Fin S.support.card)).obj (bar₃ (C:=FiniteSetGroupoid)) :=
  bar₃Map UniformObject.evaluation ≫ triplePowerComparison _
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageSimplicialColimit
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram ColimitTransfer

variable {a n : ℕ} (p q : ℕ)
noncomputable def degreeRowsStage : Stage a n ⥤ (SimplexCategoryᵒᵖ ⥤ Cat.{0,0}) where
  obj S := simplicial (C:=Diagram (Diagram S.Obj (Fin (p+1))) (Fin (q+1)))
  map h := simplicialMap (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (leOfHom h))))
  map_id S := by
    apply NatTrans.ext; funext r; apply Cat.ext
    exact map₃_inclusion_id r.unop.len q p S
  map_comp h k := by
    apply NatTrans.ext; funext r; apply Cat.ext
    exact map₃_inclusion_comp r.unop.len q p (leOfHom h) (leOfHom k)
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace SimplicialDiagonal

variable {J : Type} [Category.{0} J] [IsFiltered J]
noncomputable def diagonalHomologyIsColimit {F : J ⥤ (I ⥤ SSet)} (t : Cocone F)
    (ht : ∀ p q, IsColimit (((evaluation I SSet).obj p ⋙
      SSet.homologyFunctor DiagonalResolution.Z q).mapCocone t)) (n:ℕ) :
    IsColimit ((diagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z n).mapCocone t) := by
  let s := colimit.cocone F
  let u : s.pt ⟶ t.pt := colimit.desc F t
  have hrow (p:I) (q:ℕ) : IsIso (SSet.homologyMap (u.app p) DiagonalResolution.Z q) := by
    apply isIso_of_colimit_fac
      (isColimitOfPreserves ((evaluation I SSet).obj p ⋙ SSet.homologyFunctor DiagonalResolution.Z q)
        (colimit.isColimit F)) (ht p q)
    intro j
    change SSet.homologyMap ((s.ι.app j).app p) _ _ ≫ SSet.homologyMap (u.app p) _ _ = _
    rw [←SSet.homologyMap_comp]
    have hu : s.ι.app j ≫ u=t.ι.app j := colimit.ι_desc t j
    have hv := congrArg (fun f : F.obj j ⟶ t.pt => f.app p) hu
    exact congrArg (fun f => SSet.homologyMap f DiagonalResolution.Z q) hv
  haveI := homologyMap_isIso u hrow n
  let G := diagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z n
  change IsColimit (G.mapCocone t)
  haveI : IsIso (G.map u) := homologyMap_isIso u hrow n
  refine IsColimit.ofIsoColimit (isColimitOfPreserves G (colimit.isColimit F))
    (Cocone.ext (c := G.mapCocone s) (c' := G.mapCocone t) (asIso (G.map u)) ?_)
  intro j
  change G.map (s.ι.app j) ≫ G.map u = G.map (t.ι.app j)
  rw [←Functor.map_comp]
  exact congrArg G.map (colimit.ι_desc t j)
end SimplicialDiagonal

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram ColimitTransfer SimplicialDiagonal

variable {a n : ℕ}
noncomputable def middleRowsStage (p:ℕ) : Stage a n ⥤ (I ⥤ SSet) where
  obj S := rows₂ (C:=Diagram S.Obj (Fin (p+1)))
  map h := rows₂Map (Diagram.map (I:=Fin (p+1)) (inclusion (leOfHom h)))
  map_id S := by
    apply NatTrans.ext; funext q
    change nerveDiagonal.map ((degreeRowsStage p q.unop.len).map (𝟙 S)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id]
  map_comp h k := by
    apply NatTrans.ext; funext q
    change nerveDiagonal.map ((degreeRowsStage p q.unop.len).map (h ≫ k)) =
      nerveDiagonal.map ((degreeRowsStage p q.unop.len).map h) ≫
        nerveDiagonal.map ((degreeRowsStage p q.unop.len).map k)
    rw [Functor.map_comp,Functor.map_comp]
noncomputable def topRowsStage : Stage a n ⥤ (I ⥤ SSet) where
  obj S := rows₃ (C:=S.Obj)
  map h := rows₃Map (inclusion (leOfHom h))
  map_id S := by
    apply NatTrans.ext; funext p
    change diagonal.map ((middleRowsStage p.unop.len).map (𝟙 S)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id]
  map_comp h k := by
    apply NatTrans.ext; funext p
    change diagonal.map ((middleRowsStage p.unop.len).map (h ≫ k)) =
      diagonal.map ((middleRowsStage p.unop.len).map h) ≫
        diagonal.map ((middleRowsStage p.unop.len).map k)
    rw [Functor.map_comp,Functor.map_comp]
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_StageHomologyCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower FreeChains

attribute [local instance 1200] Pi.module Prod.instModule
variable {a n:ℕ}
noncomputable abbrev E := bar₃ (C:=FiniteSetGroupoid)
noncomputable abbrev K (j:ℕ) : ModuleCat ℤ := E.homology Z j
noncomputable def coefficientVectorIso (S:Stage a n) (j:ℕ) :
    ModuleCat.of ℤ (Fin S.partition.size × Fin S.support.card → K j) ≅
      (coefficientDiagram (a:=a) (n:=n) (K j)).obj S :=
  (AddEquiv.refl (Fin S.partition.size × Fin S.support.card → K j)).toIntLinearEquiv.toModuleIso
noncomputable def homologyCoordinates (S:Stage a n) (j:ℕ) :
    (bar₃ (C:=S.Obj)).homology Z j ⟶ (coefficientDiagram (a:=a) (n:=n) (K j)).obj S :=
  SSet.homologyMap S.finiteProductComparison Z j ≫ coordinates _ E j ≫ (S.coefficientVectorIso j).hom
lemma homologyCoordinates_at (S:Stage a n) (j:ℕ)
    (x:((bar₃ (C:=S.Obj)).homology Z j : A)) (c:Fin S.partition.size × Fin S.support.card) :
    S.homologyCoordinates j x c =
      SSet.homologyMap (S.finiteProductComparison ≫ evaluate _ E c) Z j x := by
  rw [SSet.homologyMap_comp]
  rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

abbrev PlaneCornerIndex (a : ℕ) := VertexType (commonVertexDenominator a) × PlaneSectorIndex

end PlaneCornerCoordinates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PointFiberMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Classical Set MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.PointFiber

variable {a n : ℕ}
noncomputable def muEval (U V : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) :
    FiniteSetGroupoid.sum (E.obj U b) (E.obj V b) ⟶ E.obj (sum U V) b := mu U V b
@[simp] lemma muEval_inl (U V : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) (x : Fiber U b) :
    muEval U V b (FiniteSetGroupoid.sumEquiv _ _ (.inl (enumerate U b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inl x)) := mu_inl U V b x
@[simp] lemma muEval_inr (U V : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) (x : Fiber V b) :
    muEval U V b (FiniteSetGroupoid.sumEquiv _ _ (.inr (enumerate V b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inr x)) := mu_inr U V b x
noncomputable def epsEval (b : GenericSquare a × (Fin n → CutRing × CutRing)) :
    FiniteSetGroupoid.empty ⟶ E.obj (empty (a:=a) (n:=n)) b := eps b
lemma mu_assoc (U V W : Labelled a n) :
    mu U V ▷ E.obj W ≫ mu (U⊗V) W ≫ E.map (α_ U V W).hom =
      (α_ (E.obj U) (E.obj V) (E.obj W)).hom ≫ E.obj U ◁ mu V W ≫ mu U (V⊗W) := by
  funext b
  apply Equiv.ext
  intro x
  change E.map (assocHom U V W) b (muEval (sum U V) W b
      (FiniteSetGroupoid.sumHom (muEval U V b) (𝟙 (E.obj W b)) x)) =
    muEval U (sum V W) b (FiniteSetGroupoid.sumHom (𝟙 (E.obj U b)) (muEval V W b)
      (FiniteSetGroupoid.assoc (E.obj U b) (E.obj V b) (E.obj W b) x))
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (FiniteSetGroupoid.sum (E.obj U b) (E.obj V b)) (E.obj W b)).surjective x
  cases x with
  | inl x =>
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      rw [FiniteSetGroupoid.sumHom_inl (muEval U V b) (𝟙 (E.obj W b)),muEval_inl,muEval_inl,E_map_enum,fiber_assoc_left,
        FiniteSetGroupoid.assoc_left,FiniteSetGroupoid.sumHom_inl,FiniteSetGroupoid.id_apply,muEval_inl]
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      rw [FiniteSetGroupoid.sumHom_inl (muEval U V b) (𝟙 (E.obj W b)),muEval_inr,muEval_inl,E_map_enum,fiber_assoc_mid,
        FiniteSetGroupoid.assoc_mid,FiniteSetGroupoid.sumHom_inr,muEval_inl,muEval_inr]
  | inr x =>
    obtain ⟨x,rfl⟩ := (enumerate W b).surjective x
    rw [FiniteSetGroupoid.sumHom_inr (muEval U V b) (𝟙 (E.obj W b)),FiniteSetGroupoid.id_apply,muEval_inr,E_map_enum,fiber_assoc_right,
      FiniteSetGroupoid.assoc_right,FiniteSetGroupoid.sumHom_inr,muEval_inr,muEval_inr]
lemma eps_left (U : Labelled a n) :
    (λ_ (E.obj U)).hom = eps ▷ E.obj U ≫ mu (𝟙_ _) U ≫ E.map (λ_ U).hom := by
  funext b
  apply Equiv.ext
  intro x
  change FiniteSetGroupoid.left (E.obj U b) x = E.map (leftHom U) b
    (muEval empty U b (FiniteSetGroupoid.sumHom (epsEval b) (𝟙 (E.obj U b)) x))
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv FiniteSetGroupoid.empty (E.obj U b)).surjective x
  cases x with
  | inl x => exact Fin.elim0 x
  | inr x =>
    obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
    rw [FiniteSetGroupoid.left_apply,FiniteSetGroupoid.sumHom_inr (epsEval b) (𝟙 (E.obj U b)),
      FiniteSetGroupoid.id_apply,muEval_inr,E_map_enum,fiber_left]
lemma eps_right (U : Labelled a n) :
    (ρ_ (E.obj U)).hom = E.obj U ◁ eps ≫ mu U (𝟙_ _) ≫ E.map (ρ_ U).hom := by
  funext b
  apply Equiv.ext
  intro x
  change FiniteSetGroupoid.right (E.obj U b) x = E.map (rightHom U) b
    (muEval U empty b (FiniteSetGroupoid.sumHom (𝟙 (E.obj U b)) (epsEval b) x))
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) FiniteSetGroupoid.empty).surjective x
  cases x with
  | inl x =>
    obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
    rw [FiniteSetGroupoid.right_apply,FiniteSetGroupoid.sumHom_inl (𝟙 (E.obj U b)) (epsEval b),
      FiniteSetGroupoid.id_apply,muEval_inl,E_map_enum,fiber_right]
  | inr x => exact Fin.elim0 x
noncomputable instance evaluationMonoidal : (evaluation (a:=a) (n:=n)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso eps
    μIso U V := asIso (mu U V)
    μIso_hom_natural_left := by intro U V f W; simpa using mu_natural f (𝟙 W)
    μIso_hom_natural_right := by intro U V W f; simpa using mu_natural (𝟙 W) f
    associativity := mu_assoc
    left_unitality := eps_left
    right_unitality := eps_right }
noncomputable instance evaluationBraided : (evaluation (a:=a) (n:=n)).Braided where
  braided U V := by
    change mu U V ≫ E.map (swapHom U V) = (β_ (E.obj U) (E.obj V)).hom ≫ mu V U
    funext b
    apply Equiv.ext
    intro x
    change E.map (swapHom U V) b (muEval U V b x) =
      muEval V U b (FiniteSetGroupoid.swap (E.obj U b) (E.obj V b) x)
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      rw [muEval_inl,E_map_enum,fiber_swap_left,FiniteSetGroupoid.swap_left,muEval_inr]
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      rw [muEval_inr,E_map_enum,fiber_swap_right,FiniteSetGroupoid.swap_right,muEval_inl]
end SimpleAmenable.PolygonObject.Labelled.PointFiber

end

end OAI
end



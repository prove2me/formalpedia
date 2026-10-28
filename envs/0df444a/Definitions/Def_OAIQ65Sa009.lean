-- Prove2me | Definitions.Def_OAIQ65Sa009
-- name    : OAIQ65Sa009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:49:07.689109+00:00
-- url     : https://prove2.me/theorems/f2c80130-e7db-4dee-aec9-80dce33aa207
-- title:
--   Definitions bundle OAIQ65Sa009 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 115 declarations of OpenAI's Lean: 71 definitions, 4 instances and 40 theorems. The definitions and types are `OAI.SimpleAmenable.SameAffineBranch`, `OAI.SimpleAmenable.SquareStep.coefficientRep`, `OAI.SimpleAmenable.SquareStep.eval`, `OAI.SimpleAmenable.SquareStep.orbitLift`, `OAI.SimpleAmenable.SquareStep.orbitProjection`, `OAI.SimpleAmenable.SquareStep.orbitRepresentation`, `OAI.SimpleAmenable.SquareStep.periodize`, `OAI.SimpleAmenable.SquareStep.representation`, `OAI.SimpleAmenable.TangentIntervalReach`, `OAI.SimpleAmenable.TangentIntervalStep`, `OAI.SimpleAmenable.affineConjugateCost`, `OAI.SimpleAmenable.anchorCutSet`, `OAI.SimpleAmenable.axisCellRectangle`, `OAI.SimpleAmenable.axisCellStripPair`, `OAI.SimpleAmenable.barrierBitsTransport`, `OAI.SimpleAmenable.barrierInteriorSite`, `OAI.SimpleAmenable.boundedCutLevels`, `OAI.SimpleAmenable.chartCrossingParameter`, `OAI.SimpleAmenable.clippedLabel`, `OAI.SimpleAmenable.closedRefinedBox`, `OAI.SimpleAmenable.closedWindowBox`, `OAI.SimpleAmenable.conditionalWord`, `OAI.SimpleAmenable.conjugateIntersectionCoefficient`, `OAI.SimpleAmenable.flagAffineData`, `OAI.SimpleAmenable.flagBadSeparatorRow`, `OAI.SimpleAmenable.flagDirectionStrip`, `OAI.SimpleAmenable.flagExceptionalConstant`, `OAI.SimpleAmenable.flagGoodRow`, `OAI.SimpleAmenable.flagSignalSupport`, `OAI.SimpleAmenable.flagSiteFromNumerator`, `OAI.SimpleAmenable.flagWindow`, `OAI.SimpleAmenable.formalAssignmentEval`, `OAI.SimpleAmenable.formalPolygonTable`, `OAI.SimpleAmenable.growthAnchorFamily`, `OAI.SimpleAmenable.jointBitReindex`, `OAI.SimpleAmenable.latticeRowTent`, `OAI.SimpleAmenable.liftedCoordinate`, `OAI.SimpleAmenable.lowerEnclosure`, `OAI.SimpleAmenable.openSquareChart`, `OAI.SimpleAmenable.pairedQuadraticBox` and 31 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Amenability_BarrierChartRefinement`, `SimpleAmenable_Amenability_BarrierCore`, `SimpleAmenable_Amenability_BarrierFiniteMenu`, `SimpleAmenable_Arithmetic_LatticeRiemann`, `SimpleAmenable_CentralCovers_FormalPairSplits`, `SimpleAmenable_CentralCovers_PairControl`, `SimpleAmenable_CentralCovers_PrimitiveWords`, `SimpleAmenable_CentralCovers_SmallStarRelators`, `SimpleAmenable_CentralCovers_StarProjection`, `SimpleAmenable_Homology_ClippedLineSlide`, `SimpleAmenable_Homology_TorusCoefficientFinite`, `SimpleAmenable_Homology_WindowEnclosureChains`, `SimpleAmenable_PolygonGeometry_AxisAnchorFamily`, `SimpleAmenable_PolygonGeometry_ClippedIntervals`, `SimpleAmenable_PolygonGeometry_CompactCommonRefinement`, `SimpleAmenable_PolygonGeometry_CompactFineGrid`, `SimpleAmenable_PolygonGeometry_DirectionStripCounts`, `SimpleAmenable_PolygonGeometry_FiniteNestedLaw`, `SimpleAmenable_PolygonGeometry_FiniteSectorPartition`, `SimpleAmenable_PolygonGeometry_FlagSiteCounts`, `SimpleAmenable_PolygonGeometry_FlagSites`, `SimpleAmenable_PolygonGeometry_FlagTentMass`, `SimpleAmenable_PolygonGeometry_FullGroupAffineData`, `SimpleAmenable_PolygonGeometry_GoodRowSeparators`, `SimpleAmenable_PolygonGeometry_IntervalTangentConnectivity`, `SimpleAmenable_PolygonGeometry_OpenAffineCharts`, `SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates`, `SimpleAmenable_PolygonGeometry_PlaneCornerInjectivity`, `SimpleAmenable_PolygonGeometry_PlaneCornerKernel`, `SimpleAmenable_PolygonGeometry_PlanePeriodization`, `SimpleAmenable_PolygonGeometry_PlaneStepFunctions`, `SimpleAmenable_PolygonGeometry_SeparatedAxisSectors`, `SimpleAmenable_PolygonGeometry_ShiftedSlots`, `SimpleAmenable_PolygonGeometry_SortedAxisCuts`, `SimpleAmenable_PolygonGeometry_TorusStepFunctions`, `SimpleAmenable_PolygonGeometry_WindowCellPartition`, `SimpleAmenable_PolygonGeometry_WindowCells`, `SimpleAmenable_PolygonGeometry_WindowEnclosureGeometry`, `SimpleAmenable_PolygonGeometry_WindowRectangles`, `SimpleAmenable_RandomFields_AveragingAffinePairs`, `SimpleAmenable_RandomFields_CovarianceLimit`, `SimpleAmenable_RandomFields_FlagSignalEnergy`, `SimpleAmenable_RandomFields_JointBitField`, `SimpleAmenable_RandomFields_PeriodizationCovariance`, `SimpleAmenable_RandomFields_SignalGoodRows`, `SimpleAmenable_RandomFields_WeightedAveragingError`, `SimpleAmenable_Simplicial_TrajectoryFinite`, `SimpleAmenable_Simplicial_TranslationCoinvariants`, `SimpleAmenable_Simplicial_TranslationNerve`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa004`, `OAIQ65Sa005` and `OAIQ65Sa006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa011`, `OAIQ65Sa015`, `OAIQ65Sa016` and `OAIQ65Sa019`; the proofs of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.inactive_clipped_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations` and `OAI.SimpleAmenable.finePatchAtlas_eventually`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa004
import Definitions.Def_OAIQ65Sa005
import Definitions.Def_OAIQ65Sa006

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_LatticeRiemann
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section PairedLatticeRiemann
open Classical Module MeasureTheory

def pairedQuadraticBox (d s t R : ℝ) (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) : Set (CutRing×CutRing) :=
  {z | ‖q+pairedQuadraticEmbedding d s t z‖≤R}

end PairedLatticeRiemann

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneStepFunctions
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
section PlaneStepFunctions

instance instFGCutRing : AddGroup.FG CutRing := by
  apply Module.Finite.iff_addGroup_fg.mp
  infer_instance

end PlaneStepFunctions

section PlaneArrangementGerms

open Classical

theorem planeGerm_evaluate {a : ℕ} (f : PlaneStep a) {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    {z v : ℝ × ℝ} (hv : TransverseDirection a v) {p : GenericPlane a}
    (hp : p.val∈arrangementNeighborhood a S z) (hpv : p.val∈planeSector a z v) :
    f.val p=planeGerm f z v := by
  obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
  obtain ⟨q,hq,hqv⟩ := planeSector_generic hv
    ((arrangementNeighborhood_open a S z).inter hN)
    ⟨self_mem_arrangementNeighborhood a S z,hz⟩
  have hpq : f.val p=f.val q := hS p q (fun l hl =>
    (planeSign_neighborhood hp hpv hl).trans (planeSign_neighborhood hq.1 hqv hl).symm)
  exact hpq.trans (hf q hq.2 hqv)

end PlaneArrangementGerms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TorusStepFunctions
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
section TorusStepFunctions
open Classical

namespace SquareStep
variable {a : ℕ}

noncomputable def representation (a : ℕ) :
    Representation ℤ (Multiplicative (CutRing × CutRing)) (SquareStep a) where
  toFun u := translate u.toAdd
  map_one' := by ext f p; exact congrFun (congrArg Subtype.val (translate_zero f)) p
  map_mul' u v := by ext f p; exact congrFun (congrArg Subtype.val (translate_add u.toAdd v.toAdd f)) p

end SquareStep
end TorusStepFunctions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ShiftedSlots
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

theorem untranslate_mem {a : ℕ} {U V : polygonAlgebra a}
    (u : CutRing × CutRing) (hVU : V.val ⊆ (translatedPolygon u U).val)
    (x : V.val) : translate a (-u) x.val ∈ U.val := by
  obtain ⟨y,hy,he⟩ := hVU x.property
  change translate a u y = x.val at he
  rw [← he,← translate_add,neg_add_cancel,translate_zero]
  exact hy

end LocalDisplacement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveWords
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section PrimitiveWords

noncomputable def conditionalWord {m : ℕ} (j : Fin 5)
    (s : alternatingGroup (Fin (m+1))) : FreeGroup (SourceGeneratorLabel m) :=
  FreeGroup.map (fun t : SmallAlt m => sourceConditionalLabel m
    (j,⟨t.val.val,t.val.property,t.property⟩)) (smallAltWord s)

noncomputable def primitiveWord {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I)
    (p : Fin 5 × (CutRing × CutRing)) (s : alternatingGroup I) :
    FreeGroup (SourceGeneratorLabel m) :=
  let k := (commonFrame a r m hm I b hb p.2).k
  latticeWord k * conditionalWord p.1 (subtypeAlternatingHom I s) * (latticeWord k)⁻¹

end PrimitiveWords

section PrimitiveFamilyLaws

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {ι : Type*}

noncomputable def primitiveFamilyWord (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) :
    Option ι × alternatingGroup I → FreeGroup (SourceGeneratorLabel m)
  | (none,s) => conditionalWord 0 (subtypeAlternatingHom I s)
  | (some i,s) => primitiveWord (a := a) (r := r) (hm := hm) I b hb (P i) s

end PrimitiveFamilyLaws

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowEnclosureGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowEnclosureGeometry

theorem coordinate_window_brackets (n : ℕ) (hn : 1 ≤ n) (q : ℤ) (t : ℝ) :
    ∃ u v : CutRing,
      (q ≤ endpointLabel u ∧ endpointLabel u < q+n) ∧
      (q ≤ endpointLabel v ∧ endpointLabel v < q+n) ∧
      t-201/(n:ℝ) ≤ ordinary u ∧ ordinary u < t ∧
      t < ordinary v ∧ ordinary v ≤ t+201/(n:ℝ) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨u,hu₁,hu₂,hu⟩ := coordinate_window_net n hn q (t-101/(n:ℝ))
  obtain ⟨v,hv₁,hv₂,hv⟩ := coordinate_window_net n hn q (t+101/(n:ℝ))
  have hpos : 0 < 1/(n:ℝ) := div_pos zero_lt_one hn'
  rcases abs_le.mp hu with ⟨huL,huR⟩
  rcases abs_le.mp hv with ⟨hvL,hvR⟩
  refine ⟨u,v,⟨hu₁,hu₂⟩,⟨hv₁,hv₂⟩,?_,?_,?_,?_⟩ <;>
    simp only [div_eq_mul_inv,one_mul] at * <;> linarith

end WindowEnclosureGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_WindowEnclosureChains
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowEnclosureChains

noncomputable def windowBracket (n : ℕ) (hn : 1 ≤ n) (q : ℤ) (t : ℝ) :
    WindowBracket n q t := Classical.choice (by
  obtain ⟨u,v,hu,hv,huL,huR,hvL,hvR⟩ := coordinate_window_brackets n hn q t
  exact ⟨⟨u,v,hu,hv,huL,huR,hvL,hvR⟩⟩)

noncomputable def lowerEnclosure (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a : ℝ) :
    ℕ → CutRing
  | 0 => (windowBracket n hn (q 0) a).lower
  | k+1 => (windowBracket n hn (q (k+1)) (ordinary (lowerEnclosure n hn q a k))).lower

noncomputable def upperEnclosure (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (b : ℝ) :
    ℕ → CutRing
  | 0 => (windowBracket n hn (q 0) b).upper
  | k+1 => (windowBracket n hn (q (k+1)) (ordinary (upperEnclosure n hn q b k))).upper

end WindowEnclosureChains

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteNestedLaw
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section QuadrantControl

def signQuadrantLower (s : CutRing) (d : Fin 2) (positive : Bool) (j : Fin 2) : CutRing :=
  if positive then (if j=d then -s else 0) else (if j=d then 0 else -s)

def signQuadrantUpper (s : CutRing) (d : Fin 2) (positive : Bool) (j : Fin 2) : CutRing :=
  if positive then (if j=d then 0 else s) else (if j=d then s else 0)

end QuadrantControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowCells
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowCells

attribute [local instance] cutOrdinaryOrder

theorem windowInterior_label (n : ℕ) (i : Fin n) :
    0 ≤ endpointLabel (windowInterior n i) ∧ endpointLabel (windowInterior n i) < n := by
  have hh := windowInterior_mem n i
  simp only [windowEndpointSet,Finset.mem_image,Finset.mem_univ,true_and] at hh
  obtain ⟨j,hj⟩ := hh
  rw [← hj,endpointLabel_cutFraction]
  have he : endpointLabel ((j.val:CutRing)*cutTau) = (j.val:ℤ) := by
    exact_mod_cast endpointLabel_labelTau (j.val:ℤ)
  rw [he]
  exact ⟨by omega,by omega⟩

theorem windowCut_label (n : ℕ) (q : ℤ) (hn : 0 < n) (i : Fin (n+1)) :
    q ≤ endpointLabel (windowCut n q i) ∧ endpointLabel (windowCut n q i) < q+n := by
  unfold windowCut
  split_ifs with hi
  · rw [endpointLabel_add,endpointLabel_labelTau]
    have hh := windowInterior_label n ⟨i.val,hi⟩
    omega
  · simp only [endpointLabel_add,endpointLabel_labelTau]
    change q ≤ q+0 ∧ q+0 < q+n
    omega

theorem windowCut_strictMono (n : ℕ) (q : ℤ) :
    StrictMono fun i => ordinary (windowCut n q i) := by
  intro i j hij
  have hi : i.val < n := by have hh := j.isLt; change i.val < j.val at hij; omega
  simp only [windowCut,dite_eq_left hi,map_add]
  split_ifs with hj
  · apply add_lt_add_right
    exact (windowInterior n).strictMono (show (⟨i.val,hi⟩:Fin n) < ⟨j.val,hj⟩ from hij)
  · simpa only [map_one] using add_lt_add_right (windowInterior_bounds n ⟨i.val,hi⟩).2
      (ordinary ((q:CutRing)*cutTau))

end WindowCells

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowCellPartition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowCellPartition

noncomputable def windowCell (a : ℕ) (j : Fin 2) (n : ℕ) (q : ℤ) (i : Fin n) :
    polygonAlgebra a := coordinateInterval a j (windowCut n q i.castSucc) (windowCut n q i.succ)

noncomputable def liftedCoordinate {a : ℕ} (j : Fin 2) (z : CutRing) (p : GenericSquare a) : ℝ :=
  coordinate j p - (⌊coordinate j p-ordinary z⌋:ℤ)

end WindowCellPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteSectorPartition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section AxisCellSplitting

noncomputable def axisCellRectangle {n : ℕ} (d : Fin 2)
    (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (hlpos : 0 < l)
    (p q : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) (i : Fin l) : LabelledRectangle n where
  length j := if j=d then k else l
  length_le j := by split <;> assumption
  start j := if j=d then p else q
  lower j := if j=d then u else windowCut l q i.castSucc
  upper j := if j=d then v else windowCut l q i.succ
  ordered j := by
    split
    · exact huv
    · exact (windowCut_strictMono l q (Fin.castSucc_lt_succ (i := i))).le
  lower_label j := by
    split_ifs
    · exact hu
    · exact windowCut_label l q hlpos i.castSucc
  upper_label j := by
    split_ifs
    · exact hv
    · exact windowCut_label l q hlpos i.succ

end AxisCellSplitting

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SeparatedAxisSectors
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SeparatedAxisSectors

noncomputable def axisCellStripPair {n : ℕ} (d : Fin 2)
    (k k' l : ℕ) (hk : k ≤ n) (hk' : k' ≤ n) (hl : l ≤ n) (hlpos : 0 < l)
    (p p' q : ℤ) (u v u' v' : CutRing)
    (huv : ordinary u ≤ ordinary v) (hgap : ordinary v < ordinary u')
    (huv' : ordinary u' ≤ ordinary v')
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hu' : p' ≤ endpointLabel u' ∧ endpointLabel u' < p'+k')
    (hv' : p' ≤ endpointLabel v' ∧ endpointLabel v' < p'+k')
    (hkn : k ≤ n*9/10) (hkn' : k' ≤ n*9/10) (hln : l ≤ n/4) (i : Fin l) : OldStripPair n d where
  left := axisCellRectangle d k l hk hl hlpos p q u v huv hu hv i
  right := axisCellRectangle d k' l hk' hl hlpos p' q u' v' huv' hu' hv' i
  lo := u
  cutLeft := v
  cutRight := u'
  hi := v'
  bottom := windowCut l q i.castSucc
  top := windowCut l q i.succ
  left_lower _ := rfl
  left_upper _ := rfl
  right_lower _ := rfl
  right_upper _ := rfl
  ordered_left := huv
  ordered_gap := hgap
  ordered_right := huv'
  ordered_cross := (windowCut_strictMono l q (Fin.castSucc_lt_succ (i := i))).le
  left_length j := by change (if j=d then k else l) ≤ _; split <;> assumption
  right_length j := by change (if j=d then k' else l) ≤ _; split <;> assumption

end SeparatedAxisSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SortedAxisCuts
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SortedAxisCuts
attribute [local instance] cutOrdinaryOrder

noncomputable def sortedAxisCutSequence (n k N : ℕ) (p : ℤ) (u v : CutRing)
    (S : Finset CutRing) (hu : u ∈ S) (hv : v ∈ S)
    (hbound : ∀ z ∈ S, ordinary u ≤ ordinary z ∧ ordinary z ≤ ordinary v)
    (hlabels : ∀ z ∈ S, p ≤ endpointLabel z ∧ endpointLabel z < p+N)
    (hoveru : p+(N:ℤ)-k ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hoverv : p+(N:ℤ)-k ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (_hkN : k ≤ N) (_hNk : N ≤ 2*k) (hkn : k ≤ n*9/10) : AxisCutSequence n (S.card-1) := by
  classical
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨u,hu⟩
  have hcard : S.card = S.card-1+1 := by omega
  let f : Fin (S.card-1+1) ↪o CutRing := S.orderEmbOfFin hcard
  have hmem (i) : f i ∈ S := Finset.orderEmbOfFin_mem S hcard i
  have hsurj : ∀ z ∈ S, ∃ i, f i=z := by
    intro z hz
    have hh : z ∈ Set.range f := by
      change z ∈ Set.range (S.orderEmbOfFin hcard)
      rw [Finset.range_orderEmbOfFin]
      exact hz
    exact hh
  have hzero : f 0=u := by
    obtain ⟨i,hi⟩ := hsurj u hu
    apply ordinary_injective
    apply le_antisymm
    · have hh := f.monotone (Fin.zero_le i)
      change ordinary (f 0) ≤ ordinary (f i) at hh
      simpa only [hi] using hh
    · exact (hbound _ (hmem 0)).1
  have hlast : f (Fin.last (S.card-1))=v := by
    obtain ⟨i,hi⟩ := hsurj v hv
    apply ordinary_injective
    apply le_antisymm
    · exact (hbound _ (hmem _)).2
    · have hh := f.monotone (Fin.le_last i)
      change ordinary (f i) ≤ ordinary (f (Fin.last (S.card-1))) at hh
      simpa only [hi] using hh
  refine {
    cut := f
    strictMono := f.strictMono
    length := fun _ => k
    start := fun i => if endpointLabel (f i) < p+k then p else p+(N:ℤ)-k
    length_le := fun _ => hkn
    lower_label := ?_
    upper_label := ?_
    cut_label := ?_ }
  · intro i
    rw [hzero]
    split_ifs <;> have hh := hlabels u hu <;> constructor <;> omega
  · intro i
    rw [hlast]
    split_ifs <;> have hh := hlabels v hv <;> constructor <;> omega
  · intro i
    have hh := hlabels (f i) (hmem i)
    split_ifs <;> constructor <;> omega

theorem labelLift_bounds (u : CutRing) (q : ℤ) :
    ordinary u ≤ ordinary (labelLift u q) ∧ ordinary (labelLift u q) < ordinary u+1 := by
  simp only [labelLift,map_add,ordinary_cutFraction]
  have hh := Int.fract_nonneg (ordinary ((q:CutRing)*cutTau-u))
  have hh' := Int.fract_lt_one (ordinary ((q:CutRing)*cutTau-u))
  constructor <;> linarith

noncomputable def anchorCutSet (N : ℕ) (p : ℤ) (u v : CutRing) : Finset CutRing := by
  classical
  exact insert u (insert v ((Finset.univ.image fun i : Fin N => labelLift u (p+(i.val:ℤ))).filter
    fun z => ordinary z ≤ ordinary v))

theorem anchorCutSet_lower (N : ℕ) (p : ℤ) (u v : CutRing) : u ∈ anchorCutSet N p u v := by
  classical
  simp only [anchorCutSet,Finset.mem_insert_self]

theorem anchorCutSet_upper (N : ℕ) (p : ℤ) (u v : CutRing) : v ∈ anchorCutSet N p u v := by
  classical
  simp [anchorCutSet]

theorem anchorCutSet_bounds (N : ℕ) (p : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v) :
    ∀ z ∈ anchorCutSet N p u v, ordinary u ≤ ordinary z ∧ ordinary z ≤ ordinary v := by
  classical
  intro z hz
  simp only [anchorCutSet,Finset.mem_insert,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and] at hz
  rcases hz with rfl | rfl | ⟨⟨i,rfl⟩,hz⟩
  · exact ⟨le_rfl,huv⟩
  · exact ⟨huv,le_rfl⟩
  · exact ⟨(labelLift_bounds u _).1,hz⟩

theorem anchorCutSet_labels (N : ℕ) (p : ℤ) (u v : CutRing)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+N)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+N) :
    ∀ z ∈ anchorCutSet N p u v, p ≤ endpointLabel z ∧ endpointLabel z < p+N := by
  classical
  intro z hz
  simp only [anchorCutSet,Finset.mem_insert,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and] at hz
  rcases hz with rfl | rfl | ⟨⟨i,rfl⟩,_⟩
  · exact hu
  · exact hv
  · rw [endpointLabel_labelLift]; constructor <;> omega

end SortedAxisCuts

section SortedAxisCutSpecs
attribute [local instance] cutOrdinaryOrder
variable (n k N : ℕ) (p : ℤ) (u v : CutRing)
    (S : Finset CutRing) (hu : u ∈ S) (hv : v ∈ S)
    (hbound : ∀ z ∈ S, ordinary u ≤ ordinary z ∧ ordinary z ≤ ordinary v)
    (hlabels : ∀ z ∈ S, p ≤ endpointLabel z ∧ endpointLabel z < p+N)
    (hoveru : p+(N:ℤ)-k ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hoverv : p+(N:ℤ)-k ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hkN : k ≤ N) (hNk : N ≤ 2*k) (hkn : k ≤ n*9/10)
local notation "D" => sortedAxisCutSequence n k N p u v S hu hv hbound hlabels hoveru hoverv hkN hNk hkn

theorem sortedAxisCutSequence_mem (i) : (D).cut i ∈ S := by
  exact Finset.orderEmbOfFin_mem S _ i

theorem sortedAxisCutSequence_range : Set.range (D).cut = (S : Set CutRing) := by
  exact Finset.range_orderEmbOfFin S _

theorem sortedAxisCutSequence_lower : (D).cut 0=u := by
  have hh : u ∈ Set.range (D).cut := by
    rw [sortedAxisCutSequence_range]
    exact hu
  obtain ⟨i,hi⟩ := hh
  apply ordinary_injective
  apply le_antisymm
  · have hh := ((D).ordered i).1
    simpa only [hi] using hh
  · exact (hbound _ (sortedAxisCutSequence_mem n k N p u v S hu hv hbound hlabels hoveru hoverv hkN hNk hkn 0)).1

theorem sortedAxisCutSequence_upper : (D).cut (Fin.last (S.card-1))=v := by
  have hh : v ∈ Set.range (D).cut := by
    rw [sortedAxisCutSequence_range]
    exact hv
  obtain ⟨i,hi⟩ := hh
  apply ordinary_injective
  apply le_antisymm
  · exact (hbound _ (sortedAxisCutSequence_mem n k N p u v S hu hv hbound hlabels hoveru hoverv hkN hNk hkn _)).2
  · have hh := ((D).ordered i).2
    simpa only [hi] using hh

end SortedAxisCutSpecs

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AxisAnchorFamily
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section GrowthAnchors
attribute [local instance] cutOrdinaryOrder

theorem growth_anchor_label {n : ℕ} (hn : 1005 ≤ n) (p : ℤ) (i : Fin (growthAnchorLength n+1)) :
    p+(growthNewLength n:ℤ)-growthOldLength n ≤ endpointLabel (windowCut (growthAnchorLength n) (growthAnchorStart n p) i) ∧
    endpointLabel (windowCut (growthAnchorLength n) (growthAnchorStart n p) i) < p+growthOldLength n := by
  have h := windowCut_label (growthAnchorLength n) (growthAnchorStart n p) (by have := growth_lengths hn; omega) i
  have hh := growth_lengths hn
  have he : (growthAnchorLength n:ℤ) = 2*(growthOldLength n:ℤ)-growthNewLength n := by
    unfold growthAnchorLength
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  unfold growthAnchorStart at h ⊢
  rw [he] at h
  omega

noncomputable def growthAnchorFamily (n : ℕ) (hn : 1005 ≤ n) (p : ℤ) :
    AxisAnchorFamily n (growthAnchorLength n) (growthAnchorStart n p) := by
  let l := growthAnchorLength n
  let q := growthAnchorStart n p
  let u (i : Fin l) := windowCut l q i.castSucc
  let v (i : Fin l) := windowCut l q i.succ
  let S (i : Fin l) := anchorCutSet (growthNewLength n) p (u i) (v i)
  have hlens := growth_lengths hn
  have hl (i : Fin l) : ordinary (u i) ≤ ordinary (v i) :=
    (windowCut_strictMono l q (Fin.castSucc_lt_succ (i := i))).le
  have hu (i : Fin l) := growth_anchor_label hn p i.castSucc
  have hv (i : Fin l) := growth_anchor_label hn p i.succ
  have hu' (i : Fin l) : p ≤ endpointLabel (u i) ∧ endpointLabel (u i) < p+growthNewLength n := by
    have := hu i; dsimp [u,l,q]; constructor <;> omega
  have hv' (i : Fin l) : p ≤ endpointLabel (v i) ∧ endpointLabel (v i) < p+growthNewLength n := by
    have := hv i; dsimp [v,l,q]; constructor <;> omega
  let D (i : Fin l) := sortedAxisCutSequence n (growthOldLength n) (growthNewLength n) p (u i) (v i) (S i)
    (anchorCutSet_lower _ _ _ _) (anchorCutSet_upper _ _ _ _)
    (anchorCutSet_bounds _ _ _ _ (hl i)) (anchorCutSet_labels _ _ _ _ (hu' i) (hv' i))
    (hu i) (hv i) hlens.2.1 hlens.2.2.1 (by rfl)
  exact ⟨fun i => (S i).card-1,D,fun i => sortedAxisCutSequence_lower ..,
    fun i => sortedAxisCutSequence_upper ..⟩

end GrowthAnchors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClippedIntervals
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ClippedIntervals
attribute [local instance] cutOrdinaryOrder

noncomputable def clippedLabel (u v : CutRing) (q : ℤ) : CutRing := min v (labelLift u q)

end ClippedIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PairControl
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

section AssignmentExclusions
variable {E S G K ι Ω : Type*} [Group E] [Group S] [Group G] [Group K]

noncomputable def formalAssignmentEval (π : E →* S) :
    FreeGroup (Option ι × E) →* ((ι → Bool) → S) :=
  (assignmentEval (fun i : ι => {σ : ι → Bool | σ i = true})).comp (copySourceMap π)

end AssignmentExclusions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SmallStarRelators
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
section SmallStarRelators
variable {α ι Ω H Q : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]

noncomputable def smallFamilyStarWord : SmallFamilyWord α ι →*
    FreeGroup (Option ι × TrackStar α) :=
  FreeGroup.lift (fun l => FreeGroup.of (l.2.1,alphabetStarLift l.1 l.2.2))

end SmallStarRelators

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalPairSplits
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
section FormalPairSplits
variable {α ι H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

def starPair (F : Option ι → TrackStar α →* H) (i j : ι) :
    Option Bool → TrackStar α →* H
  | none => F none
  | some false => F (some i)
  | some true => F (some j)

end FormalPairSplits

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_StarProjection
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
section ActualStarProjection
variable {a m : ℕ} {ι : Type*} [Finite ι]

noncomputable def formalPolygonTable (U : ι → polygonAlgebra a) :
    ((ι → Bool) → alternatingGroup (Fin (m+1))) →* polygonAlternatingGroup a (m+1) :=
  (actualPolygonTableHom U).comp (assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val))

end ActualStarProjection

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ClippedLineSlide
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ClippedLineSlide

noncomputable def tangentAllowedLower (a : ℕ) (r : CutRing) (d : Fin 2)
    (z : CutRing × CutRing) (V : Fin 2 → CutRing) : ℝ :=
  max ((ordinary (V 0)-ordinary (pointCoordinate z 0)-ordinary r)/tangentCoefficient a d 0)
    ((ordinary (V 1)-ordinary (pointCoordinate z 1)-ordinary r)/tangentCoefficient a d 1)

noncomputable def tangentAllowedUpper (a : ℕ) (r : CutRing) (d : Fin 2)
    (z : CutRing × CutRing) (L : Fin 2 → CutRing) : ℝ :=
  min ((ordinary (L 0)-ordinary (pointCoordinate z 0)+ordinary r)/tangentCoefficient a d 0)
    ((ordinary (L 1)-ordinary (pointCoordinate z 1)+ordinary r)/tangentCoefficient a d 1)

end ClippedLineSlide

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_IntervalTangentConnectivity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section IntervalTangentConnectivity

def TangentIntervalStep (u : CutRing) (L H : ℝ) (x y : CutRing) : Prop :=
  L ≤ ordinary x ∧ ordinary x ≤ H ∧ L ≤ ordinary y ∧ ordinary y ≤ H ∧
    (y-x=u ∨ y-x= -u ∨ y-x=cutTau*u ∨ y-x= -(cutTau*u))

def TangentIntervalReach (u : CutRing) (L H : ℝ) (x y : CutRing) : Prop :=
  Relation.ReflTransGen (TangentIntervalStep u L H) x y

end IntervalTangentConnectivity

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowRectangles
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowRectangles

noncomputable def windowPlanarLift {a : ℕ} (q : Fin 2 → ℤ) (p : GenericSquare a) : ℝ × ℝ :=
  (liftedCoordinate 0 ((q 0:CutRing)*cutTau) p,
   liftedCoordinate 1 ((q 1:CutRing)*cutTau) p)

end WindowRectangles

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CompactFineGrid
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section CompactFineGrid

def closedWindowBox (n : ℕ) (cell : Fin 2 → Fin n) : Set (ℝ × ℝ) :=
  {p | ∀ j, ordinary (windowCut n 0 (cell j).castSucc) ≤ realCoordinate p j ∧
    realCoordinate p j ≤ ordinary (windowCut n 0 (cell j).succ)}

end CompactFineGrid

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CompactCommonRefinement
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section CompactCommonRefinement

def closedRefinedBox (N : ℕ) (e : Fin (N+1) → CutRing) (cell : Fin 2 → Fin N) : Set (ℝ × ℝ) :=
  {p | ∀ j, ordinary (e (cell j).castSucc) ≤ realCoordinate p j ∧
    realCoordinate p j≤ordinary (e (cell j).succ)}

end CompactCommonRefinement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSites
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
section FlagSites
open Classical

instance instCountableFlagSite {a m D : ℕ} {v : ℝ×ℝ} : Countable (FlagSite a m D v) := by
  apply Function.Injective.countable (f := fun z : FlagSite a m D v => (z.val.1,flagSiteNumerator z))
  intro z w h
  apply Subtype.ext
  have ht : z.val.1=w.val.1 := congrArg (fun p : Fin m × (CutRing×CutRing) => p.1) h
  have hn : flagSiteNumerator z=flagSiteNumerator w :=
    congrArg (fun p : Fin m × (CutRing×CutRing) => p.2) h
  apply Prod.ext
  · exact ht
  · apply Subtype.ext
    rw [← flagSiteNumerator_spec z,← flagSiteNumerator_spec w,hn]

end FlagSites

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSiteCounts
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

section FlagWindowCounts
open Classical

def flagWindow {a m D : ℕ} {v : ℝ×ℝ} (x y : ℝ×ℝ) (B C : ℝ) : Set (FlagSite a m D v) :=
  {z | z.val.2.val.1∈Set.Icc x.1 (x.1+B) ∧ z.val.2.val.2∈Set.Icc x.2 (x.2+B) ∧
    (flagSiteConjugate z).1∈Set.Icc y.1 (y.1+C) ∧
    (flagSiteConjugate z).2∈Set.Icc y.2 (y.2+C)}

end FlagWindowCounts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_DirectionStripCounts
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
section DirectionStripCounts
open Classical

def flagDirectionStrip {a m D : ℕ} {v : ℝ×ℝ} (j : Fin 4) (c ε R : ℝ) :
    Set (FlagSite a m D v) :=
  {z | z∈flagSiteBox R ∧ |cutForm a j z.val.2.val-c| ≤ ε}

end DirectionStripCounts

section ExceptionalRowCounts
open Classical

def boundedCutLevels (A B : ℝ) : Set CutRing :=
  {c | |ordinary c| ≤ A ∧ |conjugate c| ≤ B}

end ExceptionalRowCounts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_GoodRowSeparators
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
section GoodRowSeparators
open Classical MeasureTheory ProbabilityTheory

def flagBadSeparatorRow {a m D : ℕ} {v : ℝ×ℝ} (s κ R : ℝ) : Set (FlagSite a m D v) :=
  {z | z∈flagSiteBox R ∧ ∃j c, |conjugate c| ≤ 2*κ/s ∧
    |cutForm a j z.val.2.val-ordinary c| ≤ (1+|ordinary (cutTau^a)|)*s}

end GoodRowSeparators

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagTentMass
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
section FlagTentMass
open Classical

noncomputable def latticeRowTent (D : ℕ) (s t : ℝ) (x y : ℝ×ℝ) (u : CutRing×CutRing) : ℝ :=
  planeTent s x (scaledOrdinary D u)*planeTent t y (scaledConjugate D u)

noncomputable def flagSiteFromNumerator {a m D : ℕ} {v : ℝ×ℝ}
    (hv : TransverseDirection a v) (k : Fin m) (u : CutRing×CutRing)
    (hu : SquareBoundary v (scaledOrdinary D u)) : FlagSite a m D v :=
  ⟨(k,⟨scaledOrdinary D u,hv,hu⟩),u,rfl⟩

end FlagTentMass

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FullGroupAffineData
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
section FullGroupAffineData
open Classical

noncomputable def flagAffineData {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (i : Fin m) (z : SquareFlag a v) : Fin m × (CutRing×CutRing) :=
  flagValue (fullGroupAffineData g i) (fullGroupAffineData_arrangement g i) z

end FullGroupAffineData

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FlagSignalEnergy
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
section FlagSignalEnergy
open Classical

noncomputable def flagSignalSupport {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) {K N : ℝ} (hK : 0<K) (hN : 0<N) : Finset (FlagSite a m D v) :=
  let S := (flagSiteBox_finite (v:=v) hD (mul_pos hN hK)).toFinset
  S ∪ S.image (flagSiteAction hD g)

end FlagSignalEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_WeightedAveragingError
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

section GoodRowAveraging
open Classical

def flagGoodRow {a m D : ℕ} {v : ℝ×ℝ} (s κ : ℝ) (z : FlagSite a m D v) : Prop :=
  ∀j c,|conjugate c| ≤ 2*κ/s →
    (1+|ordinary (cutTau^a)|)*s < |cutForm a j z.val.2.val-ordinary c|

end GoodRowAveraging

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_SignalGoodRows
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

section ApproximationEnergy
open Classical

noncomputable def flagExceptionalConstant (a m D : ℕ) (Q : ℝ) : ℝ :=
  4*(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*(1+|ordinary (cutTau^a)|)*Q+2)*
    (2*(D:ℝ)^2*Q+2)*(16*(1+|ordinary (cutTau^a)|)+2))

end ApproximationEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AveragingAffinePairs
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
section AveragingAffinePairs
open Classical MeasureTheory

def SameAffineBranch {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z w : FlagTrackPoint a m v) : Prop :=
  z.1=w.1 ∧ flagAffineData g z.1 z.2=flagAffineData g w.1 w.2

noncomputable def affineConjugateCost (a : ℕ) (u : CutRing×CutRing) : ℝ :=
  |conjugate u.1|+|conjugate u.2|+∑j : Fin 4,|conjugate (integralCutForm a j u)|

end AveragingAffinePairs

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_CovarianceLimit
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

section SourceFieldConcentration
open Classical Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable def sourceActiveSites {a m D : ℕ} {v : ℝ×ℝ}
    (hD : 0<D) {K : ℝ} (hK : 0<K) (n : ℕ) : Finset (FlagSite a m D v) :=
  (flagSiteBox_finite hD (mul_pos (sourceDyadicN_pos n) hK)).toFinset

end SourceFieldConcentration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierCore
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
section BarrierCore
open Classical

noncomputable def conjugateIntersectionCoefficient (a : ℕ) (i j : Fin 4) : ℝ :=
  (|conjugate (lineNormal a i).1|+|conjugate (lineNormal a i).2|+
    |conjugate (lineNormal a j).1|+|conjugate (lineNormal a j).2|)/|conjugate (lineDet a i j)|

end BarrierCore

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierChartRefinement
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

section BarrierCrossings
open Classical Set

noncomputable def barrierInteriorSite {a m : ℕ} (ha : 0 < a) (i : Fin m) (j : Fin 4)
    {p : ℝ×ℝ} (hp : p ∈ squareInterior)
    (hl : InFlagLattice (commonVertexDenominator a) p) :
    FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) :=
  ⟨(i,⟨p,(barrierFlagDirection_spec ha j).1,
    ⟨⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩,
    fun h => (ne_of_gt hp.1.1 h).elim,fun h => (ne_of_lt hp.1.2 h).elim,
    fun h => (ne_of_gt hp.2.1 h).elim,fun h => (ne_of_lt hp.2.2 h).elim⟩⟩),hl⟩

end BarrierCrossings

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_OpenAffineCharts
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
section OpenAffineCharts
open Classical Set

noncomputable def openSquareChart {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a) : Set (ℝ×ℝ) :=
  squareInterior ∩ strictLineCell a (fun l : T => l.val.1)
    (fun l => ordinary l.val.2) (fun l => squareSign l.val p)

end OpenAffineCharts

section ChartLineIntervals
open Classical Set

noncomputable def chartCrossingParameter (a : ℕ) (j : Fin 4) (c : CutRing) (l : PlaneCut) : ℝ :=
  (ordinary l.2-cutForm a l.1 (barrierLinePoint a j c 0))/cutForm a l.1 (barrierTangent a j)

end ChartLineIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_JointBitField
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
section JointBitField
open Classical MeasureTheory Filter
open scoped Topology

noncomputable def jointBitReindex {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (hD : 0<D) (g : polygonFullGroup a m) :
    (∀j,FlagSite a m D (v j) → Bool) → (∀j,FlagSite a m D (v j) → Bool) :=
  fun b j => bitReindex (flagSitePermutation hD g) (b j)

end JointBitField

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierFiniteMenu
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

section EightBarrierFields
open Classical MeasureTheory Filter Set
open scoped Topology

noncomputable def barrierBitsTransport {a m : ℕ} {ha : 0 < a} (g : polygonFullGroup a m)
    (b : BarrierBits a m ha) : BarrierBits a m ha :=
  jointBitReindex (barrierEightDirections ha) (commonVertexDenominator_pos ha) g b

end EightBarrierFields

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerInjectivity
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
section PlaneCornerInjectivity
open Classical

theorem TransverseDirection.neg {a : ℕ} {v : ℝ × ℝ} (hv : TransverseDirection a v) :
    TransverseDirection a (-v) := by
  intro j
  simpa only [cutForm_neg,neg_ne_zero] using hv j

theorem plane_antidiagonal_transverse (a : ℕ) : TransverseDirection a (-1,1) := by
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  intro j
  fin_cases j <;> simp [cutForm] <;> linarith

end PlaneCornerInjectivity

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerKernel
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
section PlaneCornerKernel
open Classical

noncomputable def planePairValue {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ) : ℤ :=
  planeGerm f z v+planeGerm f z (-v)

noncomputable def planeCornerValue {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ) : ℤ :=
  planePairValue f z v-planePairValue f z (-1,1)

@[simp] theorem planeCornerValue_zero {a : ℕ} (z v : ℝ × ℝ) :
    planeCornerValue (0 : PlaneStep a) z v=0 := by simp [planeCornerValue,planePairValue]

@[simp] theorem planeCornerValue_add {a : ℕ} (f g : PlaneStep a) (z v : ℝ × ℝ) :
    planeCornerValue (f+g) z v=planeCornerValue f z v+planeCornerValue g z v := by
  simp only [planeCornerValue,planePairValue,planeGerm_add]; ring

@[simp] theorem planeCornerValue_smul {a : ℕ} (c : ℤ) (f : PlaneStep a) (z v : ℝ × ℝ) :
    planeCornerValue (c • f) z v=c • planeCornerValue f z v := by
  simp only [planeCornerValue,planePairValue,planeGerm_smul,smul_add,smul_sub]

def planeSupportClosure {a : ℕ} (f : PlaneStep a) : Set (ℝ × ℝ) :=
  closure {z | ∃ p : GenericPlane a, p.val=z ∧ f.val p≠0}

end PlaneCornerKernel

section PlaneCornerSupport
open Classical

theorem planeGerm_congr_incident {a : ℕ} (f : PlaneStep a) {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    (z : ℝ × ℝ) {v w : ℝ × ℝ} (hv : TransverseDirection a v)
    (hw : TransverseDirection a w)
    (he : ∀ l∈S, cutForm a l.1 z=ordinary l.2 →
      (cutForm a l.1 v<0 ↔ cutForm a l.1 w<0)) :
    planeGerm f z v=planeGerm f z w := by
  obtain ⟨p,hp,hpv⟩ := planeSector_generic hv (arrangementNeighborhood_open a S z)
    (self_mem_arrangementNeighborhood a S z)
  obtain ⟨q,hq,hqv⟩ := planeSector_generic hw (arrangementNeighborhood_open a S z)
    (self_mem_arrangementNeighborhood a S z)
  rw [← planeGerm_evaluate f hS hv hp hpv,← planeGerm_evaluate f hS hw hq hqv]
  apply hS
  intro l hl
  rw [planeSign_neighborhood hp hpv hl,planeSign_neighborhood hq hqv hl]
  apply decide_eq_decide.mpr
  split_ifs with hh
  · exact he l hl hh
  · rfl

theorem planeCornerValue_zero_of_one_direction {a : ℕ} (f : PlaneStep a)
    {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    (z : ℝ × ℝ) (j : Fin 4)
    (hj : ∀ l∈S, cutForm a l.1 z=ordinary l.2 → l.1=j)
    {v : ℝ × ℝ} (hv : TransverseDirection a v) : planeCornerValue f z v=0 := by
  let w : ℝ × ℝ := (-1,1)
  have hw : TransverseDirection a w := plane_antidiagonal_transverse a
  have hcompare : ∀ {x y : ℝ × ℝ}, TransverseDirection a x → TransverseDirection a y →
      (cutForm a j x<0 ↔ cutForm a j y<0) → planeGerm f z x=planeGerm f z y := by
    intro x y hx hy he
    apply planeGerm_congr_incident f hS z hx hy
    intro l hl hz
    simpa only [hj l hl hz] using he
  by_cases he : (cutForm a j v<0 ↔ cutForm a j w<0)
  · have he' : (cutForm a j (-v)<0 ↔ cutForm a j (-w)<0) := by
      simp only [cutForm_neg,neg_lt_zero]
      constructor
      · intro h
        by_contra! hh
        have hw' := hw j
        have hh' : cutForm a j w<0 := lt_of_le_of_ne hh hw'
        have := he.mpr hh'; linarith
      · intro h
        by_contra! hh
        have hv' := hv j
        have hh' : cutForm a j v<0 := lt_of_le_of_ne hh hv'
        have := he.mp hh'; linarith
    have h₁ := hcompare hv hw he
    have h₂ := hcompare hv.neg hw.neg he'
    unfold planeCornerValue planePairValue
    change planeGerm f z v+planeGerm f z (-v)-(planeGerm f z w+planeGerm f z (-w))=0
    rw [h₁,h₂,sub_self]
  · have he₁ : (cutForm a j v<0 ↔ cutForm a j (-w)<0) := by
      rw [cutForm_neg,neg_lt_zero]
      have hv' := hv j
      have hw' := hw j
      constructor <;> intro hh
      · by_contra! ht
        have hwlt : cutForm a j w<0 := lt_of_le_of_ne ht hw'
        exact he (iff_of_true hh hwlt)
      · by_contra! ht
        have hvlt : 0 < cutForm a j v := lt_of_le_of_ne ht hv'.symm
        exact he (iff_of_false (not_lt_of_gt hvlt) (not_lt_of_gt hh))
    have he₂ : (cutForm a j (-v)<0 ↔ cutForm a j w<0) := by
      rw [cutForm_neg,neg_lt_zero]
      have hv' := hv j
      have hw' := hw j
      constructor <;> intro hh
      · by_contra! ht
        have hwlt : 0 < cutForm a j w := lt_of_le_of_ne ht hw'.symm
        exact he (iff_of_false (not_lt_of_gt hh) (not_lt_of_gt hwlt))
      · by_contra! ht
        have hvlt : cutForm a j v<0 := lt_of_le_of_ne ht hv'
        exact he (iff_of_true hvlt hh)
    have h₁ := hcompare hv hw.neg he₁
    have h₂ := hcompare hv.neg hw he₂
    unfold planeCornerValue planePairValue
    change planeGerm f z v+planeGerm f z (-v)-(planeGerm f z w+planeGerm f z (-w))=0
    rw [h₁,h₂]
    ring

theorem plane_line_intersection_unique {a : ℕ} (ha : 0<a) {i j : Fin 4} (hij : i≠j)
    {p q : ℝ × ℝ} (hi : cutForm a i p=cutForm a i q)
    (hj : cutForm a j p=cutForm a j q) : p=q := by
  have hd : ordinary (lineDet a i j)≠0 := fun hh =>
    lineDet_ne_zero ha i j hij (ordinary_injective (by simpa using hh))
  rw [cutForm_normal,cutForm_normal] at hi hj
  have h₁ : ordinary (lineDet a i j)*(p.1-q.1)=0 := by
    simp only [lineDet,map_sub,map_mul]
    linear_combination ordinary (lineNormal a j).2*hi-ordinary (lineNormal a i).2*hj
  have h₂ : ordinary (lineDet a i j)*(p.2-q.2)=0 := by
    simp only [lineDet,map_sub,map_mul]
    linear_combination ordinary (lineNormal a i).1*hj-ordinary (lineNormal a j).1*hi
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_left hd))
    (sub_eq_zero.mp ((mul_eq_zero.mp h₂).resolve_left hd))

noncomputable def planeLineIntersection (a : ℕ) (l k : PlaneCut) : ℝ × ℝ :=
  if h : ∃ z, cutForm a l.1 z=ordinary l.2 ∧ cutForm a k.1 z=ordinary k.2 then
    Classical.choose h else 0

theorem planeLineIntersection_eq {a : ℕ} (ha : 0<a) {l k : PlaneCut}
    (hdir : l.1≠k.1) {z : ℝ × ℝ}
    (hl : cutForm a l.1 z=ordinary l.2) (hk : cutForm a k.1 z=ordinary k.2) :
    planeLineIntersection a l k=z := by
  have he : ∃ z, cutForm a l.1 z=ordinary l.2 ∧ cutForm a k.1 z=ordinary k.2 := ⟨z,hl,hk⟩
  rw [planeLineIntersection,dite_eq_left he]
  have hh := Classical.choose_spec he
  exact plane_line_intersection_unique ha hdir (hh.1.trans hl.symm) (hh.2.trans hk.symm)

noncomputable def planeArrangementVertices (a : ℕ) (S : Finset PlaneCut) : Finset (ℝ × ℝ) :=
  (S.product S).image (fun lk => planeLineIntersection a lk.1 lk.2)

theorem planeCornerValue_exists_incident {a : ℕ} (f : PlaneStep a) {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    {z v : ℝ × ℝ} (hv : TransverseDirection a v) (hc : planeCornerValue f z v≠0) :
    ∃ l∈S, ∃ k∈S, l.1≠k.1 ∧ cutForm a l.1 z=ordinary l.2 ∧
      cutForm a k.1 z=ordinary k.2 := by
  by_contra! h
  by_cases hinc : ∃ l∈S, cutForm a l.1 z=ordinary l.2
  · obtain ⟨l,hl,hzl⟩ := hinc
    apply hc
    apply planeCornerValue_zero_of_one_direction f hS z l.1 _ hv
    intro k hk hzk
    by_contra hdir
    exact (h k hk l hl hdir hzk) hzl
  · apply hc
    apply planeCornerValue_zero_of_one_direction f hS z 0 _ hv
    intro l hl hzl
    exact (hinc ⟨l,hl,hzl⟩).elim

theorem planeCornerValue_mem_vertices {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    {z v : ℝ × ℝ} (hv : TransverseDirection a v) (hc : planeCornerValue f z v≠0) :
    z∈planeArrangementVertices a S := by
  obtain ⟨l,hl,k,hk,hdir,hzl,hzk⟩ := planeCornerValue_exists_incident f hS hv hc
  exact Finset.mem_image.mpr ⟨(l,k),Finset.mem_product.mpr ⟨hl,hk⟩,
    planeLineIntersection_eq ha hdir hzl hzk⟩

end PlaneCornerSupport

end SimpleAmenable
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

noncomputable def planeDirectionRep (a : ℕ) (σ : PlaneSectorIndex) : ℝ × ℝ :=
  if h : ∃ v, TransverseDirection a v ∧ planeDirectionSign a v=σ then
    Classical.choose h else (-1,1)

theorem planeDirectionRep_transverse (a : ℕ) (σ : PlaneSectorIndex) :
    TransverseDirection a (planeDirectionRep a σ) := by
  unfold planeDirectionRep
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact plane_antidiagonal_transverse a

theorem planeGerm_translate {a : ℕ} (f : PlaneStep a) (u : CutRing × CutRing)
    (z v : ℝ × ℝ) :
    planeGerm (PlaneStep.translate u f) z v=
      planeGerm f (z-(ordinary u.1,ordinary u.2)) v := by
  by_cases hv : TransverseDirection a v
  · apply planeGerm_eq hv
    obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f (z-(ordinary u.1,ordinary u.2)) v hv
    refine ⟨(fun p => p-(ordinary u.1,ordinary u.2)) ⁻¹' N,
      hN.preimage (continuous_id.sub continuous_const),hz,fun p hp hpv => ?_⟩
    have he : (GenericPlane.shift (-u) p).val=p.val-(ordinary u.1,ordinary u.2) := by
      ext <;> simp [GenericPlane.shift,sub_eq_add_neg]
    apply hf (GenericPlane.shift (-u) p)
    · rw [he]; exact hp
    · intro j
      have hj := hpv j
      rw [he,cutForm_sub,cutForm_sub]
      split_ifs with ht
      · rw [ite_eq_left ht] at hj; linarith
      · rw [ite_eq_right ht] at hj; linarith
  · simp [planeGerm,hv]

theorem planeCornerValue_translate {a : ℕ} (f : PlaneStep a) (u : CutRing × CutRing)
    (z v : ℝ × ℝ) :
    planeCornerValue (PlaneStep.translate u f) z v=
      planeCornerValue f (z-(ordinary u.1,ordinary u.2)) v := by
  simp only [planeCornerValue,planePairValue,planeGerm_translate]

noncomputable def planeVertexPosition (a : ℕ) (t : VertexType (commonVertexDenominator a))
    (u : Multiplicative (CutRing × CutRing)) : ℝ × ℝ :=
  vertexRepresentative (commonVertexDenominator a) t+(ordinary u.toAdd.1,ordinary u.toAdd.2)

theorem planeVertexPosition_injective (a : ℕ) (t : VertexType (commonVertexDenominator a)) :
    Function.Injective (planeVertexPosition a t) := by
  intro u v h
  have he := add_left_cancel h
  have h₁ := ordinary_injective (congrArg Prod.fst he)
  have h₂ := ordinary_injective (congrArg Prod.snd he)
  exact congrArg Multiplicative.ofAdd (Prod.ext h₁ h₂)

end PlaneCornerCoordinates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlanePeriodization
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
section PlanePeriodization

open Classical
namespace SquareStep
variable {a : ℕ}

theorem slice_finite (f : PlaneStep a) : Function.HasFiniteSupport (fun n => slice n f) := by
  obtain ⟨R,hR⟩ := PlaneStep.compactSupport f
  let N : ℤ := ⌈R+1⌉
  refine (Set.finite_Icc (-N,-N) (N,N)).subset ?_
  intro n hn
  have hp : ∃ p : GenericSquare a, (slice n f).val p ≠ 0 := by
    by_contra! h
    apply hn
    apply Subtype.ext
    exact funext h
  obtain ⟨p,hp⟩ := hp
  rw [slice_apply] at hp
  have hb : |p.val.1+(n.1:ℝ)| ≤ R ∧ |p.val.2+(n.2:ℝ)| ≤ R := by
    by_contra! h
    apply hp
    apply hR
    have hh : R < |p.val.1+(n.1:ℝ)| ∨ R < |p.val.2+(n.2:ℝ)| := by
      by_cases hx : |p.val.1+(n.1:ℝ)| ≤ R
      · exact Or.inr (h hx)
      · exact Or.inl (lt_of_not_ge hx)
    simpa only [GenericPlane.shift,intPair,Prod.fst_add,Prod.snd_add,map_intCast] using hh
  have hx : |(n.1:ℝ)| ≤ R+1 := by
    have ht := abs_add_le (p.val.1+(n.1:ℝ)) (-p.val.1)
    have he : p.val.1+(n.1:ℝ)+ -p.val.1=(n.1:ℝ) := by ring
    rw [he,abs_neg,abs_of_nonneg p.property.1.1] at ht
    linarith [p.property.1.2]
  have hy : |(n.2:ℝ)| ≤ R+1 := by
    have ht := abs_add_le (p.val.2+(n.2:ℝ)) (-p.val.2)
    have he : p.val.2+(n.2:ℝ)+ -p.val.2=(n.2:ℝ) := by ring
    rw [he,abs_neg,abs_of_nonneg p.property.2.1.1] at ht
    linarith [p.property.2.1.2]
  have hx' : -N ≤ n.1 ∧ n.1 ≤ N := by
    exact_mod_cast abs_le.mp (hx.trans (Int.le_ceil (R+1)))
  have hy' : -N ≤ n.2 ∧ n.2 ≤ N := by
    exact_mod_cast abs_le.mp (hy.trans (Int.le_ceil (R+1)))
  exact ⟨⟨hx'.1,hy'.1⟩,⟨hx'.2,hy'.2⟩⟩

noncomputable def periodize : PlaneStep a →ₗ[ℤ] SquareStep a where
  toFun f := ∑ᶠ n : ℤ×ℤ, slice n f
  map_add' f g := by
    simp only [map_add]
    exact finsum_add_distrib (slice_finite f) (slice_finite g)
  map_smul' c f := by
    simp only [map_smul]
    exact (map_finsum (DistribSMul.toAddMonoidHom (SquareStep a) c) (slice_finite f)).symm

noncomputable def eval (p : GenericSquare a) : SquareStep a →ₗ[ℤ] ℤ :=
  (LinearMap.proj p).comp (squareStepSubmodule a).subtype

theorem periodize_apply (f : PlaneStep a) (p : GenericSquare a) :
    (periodize f).val p = ∑ᶠ n : ℤ×ℤ, (slice n f).val p :=
  map_finsum (eval p) (slice_finite f)

end SquareStep
end PlanePeriodization

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PeriodizationCovariance
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
section PeriodizationCovariance

open Classical
namespace SquareStep
variable {a : ℕ}

theorem periodize_translate (f : PlaneStep a) (u : CutRing × CutRing) :
    periodize (PlaneStep.translate u f)=translate u (periodize f) := by
  apply Subtype.ext
  funext p
  simp only [translate_apply, periodize_apply]
  let k : ℤ×ℤ := (⌊p.val.1-ordinary u.1⌋,⌊p.val.2-ordinary u.2⌋)
  calc
    (∑ᶠ n : ℤ×ℤ, (slice n (PlaneStep.translate u f)).val p) =
        ∑ᶠ n : ℤ×ℤ, (slice (n+k) f).val (SimpleAmenable.translate a (-u) p) := by
      apply finsum_congr
      intro n
      simp only [slice_apply,PlaneStep.translate_apply]
      apply congrArg f.val
      apply Subtype.ext
      simp only [GenericPlane.shift,SimpleAmenable.translate_val,intPair,Prod.fst_add,Prod.snd_add,
        Prod.fst_neg,Prod.snd_neg,map_neg,map_intCast,Int.cast_add,Int.fract]
      dsimp [k]
      ext <;> simp only [Prod.fst_add,Prod.snd_add,Int.fract,map_add,map_intCast] <;> ring_nf
    _ = _ := finsum_comp_equiv (Equiv.addRight k)
      (f := fun n => (slice n f).val (SimpleAmenable.translate a (-u) p))

noncomputable def orbitProjection : Multiplicative (CutRing × CutRing) →*
    Multiplicative (ℤ×ℤ) where
  toFun u := Multiplicative.ofAdd (u.toAdd.1.im,u.toAdd.2.im)
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def orbitLift : Multiplicative (ℤ×ℤ) →*
    Multiplicative (CutRing × CutRing) where
  toFun n := Multiplicative.ofAdd ((n.toAdd.1:CutRing)*cutTau,(n.toAdd.2:CutRing)*cutTau)
  map_one' := by ext <;> simp
  map_mul' n m := by
    change Multiplicative.ofAdd
      (((n.toAdd.1+m.toAdd.1:ℤ):CutRing)*cutTau,((n.toAdd.2+m.toAdd.2:ℤ):CutRing)*cutTau) =
        Multiplicative.ofAdd (((n.toAdd.1:CutRing)*cutTau,(n.toAdd.2:CutRing)*cutTau) +
          ((m.toAdd.1:CutRing)*cutTau,(m.toAdd.2:CutRing)*cutTau))
    congr 1
    ext <;> simp [add_mul]

noncomputable def orbitRepresentation (a : ℕ) :
    Representation ℤ (Multiplicative (ℤ×ℤ)) (SquareStep a) :=
  (representation a).comp orbitLift

theorem representation_reduce (u : Multiplicative (CutRing × CutRing)) :
    representation a u = orbitRepresentation a (orbitProjection u) := by
  ext f p
  change f.val (SimpleAmenable.translate a (-u.toAdd) p) =
    f.val (SimpleAmenable.translate a (-((u.toAdd.1.im:CutRing)*cutTau,
      (u.toAdd.2.im:CutRing)*cutTau)) p)
  have he := translation_reduce a (-u.toAdd)
  have he' := Equiv.congr_fun he p
  simpa only [translation_apply,Prod.fst_neg,Prod.snd_neg,QuadraticAlgebra.im_neg,
    Int.cast_neg,neg_mul,Prod.neg_mk] using congrArg f.val he'

end SquareStep
end PeriodizationCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TorusCoefficientFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonCoefficientHomology

attribute [local instance 1200] Rep.hV2 Representation.instModuleAsModule TensorProduct.instModule
namespace SquareStep

noncomputable def coefficientRep (a : ℕ) (K : Type) [AddCommGroup K] [Module ℤ K] :
    Rep ℤ (Multiplicative (ℤ×ℤ)) :=
  Rep.of ((orbitRepresentation a).tprod (Representation.trivial ℤ _ K))

end SquareStep
end PolygonCoefficientHomology

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TrajectoryFinite
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Opposite AlgebraicTopology HomologicalComplex
namespace SimplicialDiagonal

noncomputable def rowsIso (X : I ⥤ SSet) : EilenbergZilber.bisimplicial (uncurry X) ≅ X :=
  NatIso.ofComponents (rowIso X) (by
    intro n m f
    ext k x
    simp [rowIso,EilenbergZilber.bisimplicial,uncurry,Functor.uncurry])
noncomputable def homologyRowIso (X : I ⥤ SSet) (q : ℕ) :
    TotalFiniteness.row (EilenbergZilber.twoComplex (uncurry X)) q ≅
      AlternatingFaceMapComplex.obj (X ⋙ SSet.homologyFunctor DiagonalResolution.Z q) :=
  BarHomology.rowIso (uncurry X) q ≪≫ (alternatingFaceMapComplex FreeChains.A).mapIso
    (Functor.isoWhiskerRight (rowsIso X) (SSet.homologyFunctor DiagonalResolution.Z q))
noncomputable def homologyRowHomologyIso (X : I ⥤ SSet) (p q : ℕ) :
    (TotalFiniteness.row (EilenbergZilber.twoComplex (uncurry X)) q).homology p ≅
      (AlternatingFaceMapComplex.obj (X ⋙ SSet.homologyFunctor DiagonalResolution.Z q)).homology p :=
  (homologyFunctor FreeChains.A FreeChains.c p).mapIso (homologyRowIso X q)
end SimplicialDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TranslationNerve
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology
namespace TranslationNerve
open TranslationFiltered FreeChains

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
noncomputable def coeffIso (n:ℕ) : (forgetRep P).obj ((complex P).X n) ≅
    (FreeChains.complex (nerve (C P))).X n := (MonoidAlgebra.coeffLinearEquiv ℤ).toModuleIso
lemma coeff_natural {n m:SimplexCategoryᵒᵖ} (f:n⟶m) :
    (coeffIso P n.unop.len).hom ≫ (ModuleCat.free ℤ).map ((nerve (C P)).map f) =
    (forgetRep P).map ((linear P).map f) ≫ (coeffIso P m.unop.len).hom := by
  ext x
  rfl
lemma coeff_d (m:ℕ) : (coeffIso P (m+1)).hom ≫ (FreeChains.complex (nerve (C P))).d (m+1) m =
    (forgetRep P).map ((complex P).d (m+1) m) ≫ (coeffIso P m).hom := by
  rw [show (FreeChains.complex (nerve (C P))).d (m+1) m =
      ∑ i:Fin (m+2),(-1:ℤ)^i.val • (ModuleCat.free ℤ).map ((nerve (C P)).δ i) from
      AlternatingFaceMapComplex.obj_d_eq _ m]
  rw [show (complex P).d (m+1) m=∑ i:Fin (m+2),(-1:ℤ)^i.val • (linear P).δ i from
      AlternatingFaceMapComplex.obj_d_eq _ m]
  dsimp only [coeffIso,FreeChains.complex,complex,linear]
  erw [Functor.map_sum]
  simp only [Preadditive.comp_sum,Preadditive.sum_comp,Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f => ((-1:ℤ)^i.val) • f)
    (coeff_natural P (SimplexCategory.δ i).op)
noncomputable def forgetIso : ((forgetRep P).mapHomologicalComplex c).obj (complex P) ≅
    FreeChains.complex (nerve (C P)) := by
  refine HomologicalComplex.Hom.isoOfComponents (coeffIso P) ?_
  rintro n m rfl
  exact coeff_d P m
noncomputable def aug0 : (complex P).X 0 ⟶ Rep.trivial ℤ (Q P) ℤ :=
  Rep.ofHom ⟨((coeffIso P 0).hom ≫ SimplicialAugment.aug0 (nerve (C P))).hom, by
    intro q
    ext s
    change (SimplicialAugment.aug0 (nerve (C P)))
        ((coeffIso P 0).hom (Representation.linearize ℤ (Q P) ((simplicial P).obj (op ⦋0⦌)) q
          (MonoidAlgebra.single s 1))) =
      (SimplicialAugment.aug0 (nerve (C P))) ((coeffIso P 0).hom (MonoidAlgebra.single s 1))
    rw [Representation.linearize_single]
    change (SimplicialAugment.aug0 (nerve (C P))) (ModuleCat.freeMk (s ⋙ translate P q)) =
      (SimplicialAugment.aug0 (nerve (C P))) (ModuleCat.freeMk s)
    exact (SimplicialAugment.aug0_mk (nerve (C P)) _).trans
      (SimplicialAugment.aug0_mk (nerve (C P)) _).symm⟩
lemma d_aug0 : (complex P).d 1 0 ≫ aug0 P=0 := by
  apply (forgetRep P).map_injective
  rw [Functor.map_comp,Functor.map_zero]
  change (forgetRep P).map ((complex P).d 1 0) ≫ (coeffIso P 0).hom ≫
    SimplicialAugment.aug0 (nerve (C P))=0
  have h := (forgetIso P).hom.comm 1 0
  change (coeffIso P 1).hom ≫ (FreeChains.complex (nerve (C P))).d 1 0 =
    (forgetRep P).map ((complex P).d 1 0) ≫ (coeffIso P 0).hom at h
  erw [←Category.assoc,←h,Category.assoc,SimplicialAugment.d_aug0,HasZeroMorphisms.comp_zero]
noncomputable def aug : complex P ⟶ (ChainComplex.single₀ _).obj (Rep.trivial ℤ (Q P) ℤ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨aug0 P,d_aug0 P⟩
lemma forget_aug : ((forgetRep P).mapHomologicalComplex c).map (aug P) ≫
    (HomologicalComplex.singleMapHomologicalComplex (forgetRep P) c 0).hom.app _ =
    (forgetIso P).hom ≫ SimplicialAugment.aug (nerve (C P)) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,Functor.mapHomologicalComplex_map_f]
  rfl
noncomputable instance nerve_aug_quasiIso : QuasiIso (SimplicialAugment.aug (nerve (C P))) where
  quasiIsoAt n := by
    cases n with
    | zero => rw [quasiIsoAt_iff_isIso_homologyMap]; infer_instance
    | succ n =>
      rw [quasiIsoAt_iff_isIso_homologyMap]
      have hX : IsZero ((FreeChains.complex (nerve (C P))).homology (n+1)) :=
        (FilteredNerve.positive_acyclic (C P) (n+1) (by omega)).of_iso
          ((HomologicalComplex.homologyFunctor A c (n+1)).mapIso (complexIso (nerve (C P)))).symm
      have hY : IsZero (((ChainComplex.single₀ A).obj Z).homology (n+1)) := by
        apply ShortComplex.isZero_homology_of_isZero_X₂
        exact HomologicalComplex.isZero_single_obj_X c 0 Z (n+1) (by omega)
      exact hX.isIso hY _
noncomputable instance aug_quasiIso : QuasiIso (aug P) := by
  rw [←HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forgetRep P)]
  have h : QuasiIso ((forgetIso P).hom ≫ SimplicialAugment.aug (nerve (C P))) := inferInstance
  rw [←forget_aug] at h
  exact quasiIso_of_comp_right
    (((forgetRep P).mapHomologicalComplex c).map (aug P))
    ((HomologicalComplex.singleMapHomologicalComplex (forgetRep P) c 0).hom.app _)
noncomputable def resolution : ProjectiveResolution (Rep.trivial ℤ (Q P) ℤ) where
  complex := complex P
  π := aug P
end TranslationNerve

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TranslationCoinvariants
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology
namespace TranslationNerve
open TranslationFiltered FreeChains

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
lemma orbit_d (m:ℕ) : (orbitIso P (m+1)).hom ≫ (FreeChains.complex (nerve (SingleObj P))).d (m+1) m =
    (Rep.coinvariantsFunctor ℤ (Q P)).map ((complex P).d (m+1) m) ≫ (orbitIso P m).hom := by
  rw [show (FreeChains.complex (nerve (SingleObj P))).d (m+1) m =
      ∑ i:Fin (m+2),(-1:ℤ)^i.val • (ModuleCat.free ℤ).map ((nerve (SingleObj P)).δ i) from
      AlternatingFaceMapComplex.obj_d_eq _ m]
  rw [show (complex P).d (m+1) m=∑ i:Fin (m+2),(-1:ℤ)^i.val • (linear P).δ i from
      AlternatingFaceMapComplex.obj_d_eq _ m]
  erw [Functor.map_sum,Preadditive.comp_sum,Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  erw [Functor.map_zsmul,Preadditive.comp_zsmul,Preadditive.zsmul_comp]
  exact congrArg (fun f => ((-1:ℤ)^i.val) • f) (orbit_natural P (SimplexCategory.δ i).op)
noncomputable def orbitChainIso : ((Rep.coinvariantsFunctor ℤ (Q P)).mapHomologicalComplex c).obj (complex P) ≅
    FreeChains.complex (nerve (SingleObj P)) := by
  refine HomologicalComplex.Hom.isoOfComponents (orbitIso P) ?_
  rintro n m rfl
  exact orbit_d P m

noncomputable def completionHomologyIso (n:ℕ) :
    (nerve (SingleObj P)).homology Z n ≅ groupHomology (Rep.trivial ℤ (Q P) ℤ) n := by
  classical
  let e : (resolution P).complex.coinvariantsTensorObj (Rep.trivial ℤ (Q P) ℤ) ≅
      FreeChains.complex (nerve (SingleObj P)) :=
    (NatIso.mapHomologicalComplex (unitCoinvariantsIso P) c).app (complex P) ≪≫ orbitChainIso P
  exact (HomologicalComplex.homologyFunctor A c n).mapIso (complexIso _) ≪≫
    ((HomologicalComplex.homologyFunctor A c n).mapIso e).symm ≪≫
    (groupHomologyIso (Rep.trivial ℤ (Q P) ℤ) n (resolution P)).symm
end TranslationNerve

end

end OAI
end



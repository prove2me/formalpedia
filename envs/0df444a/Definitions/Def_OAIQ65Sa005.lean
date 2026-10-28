-- Prove2me | Definitions.Def_OAIQ65Sa005
-- name    : OAIQ65Sa005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:31:47.450088+00:00
-- url     : https://prove2.me/theorems/b9f8150a-f766-41a1-9862-26af6b8545e8
-- title:
--   Definitions bundle OAIQ65Sa005 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 490 declarations of OpenAI's Lean: 165 definitions, 10 inductive types or structures, 6 instances and 309 theorems. The definitions and types are `OAI.IntervalBar.Diagram.outerFunctor`, `OAI.RestrictedNerve.constantDiagonalIso`, `OAI.RestrictedNerve.diagonalIso`, `OAI.RestrictedNerve.resolutionAugmentation`, `OAI.RestrictedNerve.verticalAugmentation`, `OAI.SimpleAmenable.AllowableVertexLine`, `OAI.SimpleAmenable.AxisAnchorFamily`, `OAI.SimpleAmenable.AxisAnchorFamily.prefixGroup`, `OAI.SimpleAmenable.AxisCutSequence`, `OAI.SimpleAmenable.AxisCutSequence.anchorCopy`, `OAI.SimpleAmenable.AxisCutSequence.atomCopy`, `OAI.SimpleAmenable.AxisCutSequence.atomPolygon`, `OAI.SimpleAmenable.AxisCutSequence.index`, `OAI.SimpleAmenable.AxisCutSequence.prefixCopy`, `OAI.SimpleAmenable.AxisCutSequence.suffix`, `OAI.SimpleAmenable.BarrierBits`, `OAI.SimpleAmenable.BarrierLineIndex`, `OAI.SimpleAmenable.BarrierMenu`, `OAI.SimpleAmenable.BarrierSignalSystem`, `OAI.SimpleAmenable.BarrierSignalSystem.eight`, `OAI.SimpleAmenable.BarrierSignalSystem.marks`, `OAI.SimpleAmenable.CommonFrame`, `OAI.SimpleAmenable.CommonFrame.restrict`, `OAI.SimpleAmenable.FinitePolygonPartition`, `OAI.SimpleAmenable.FlagDirections`, `OAI.SimpleAmenable.FlagSite`, `OAI.SimpleAmenable.FlagTrackPoint`, `OAI.SimpleAmenable.GenericPlane`, `OAI.SimpleAmenable.GenericPlane.shift`, `OAI.SimpleAmenable.HasPlaneArrangement`, `OAI.SimpleAmenable.HasSquareArrangement`, `OAI.SimpleAmenable.InFlagLattice`, `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.InitialCoverSystem.CoordinateWindowLaw`, `OAI.SimpleAmenable.InitialCoverSystem.LocalPatchTemplate`, `OAI.SimpleAmenable.InitialCoverSystem.PrimitiveFamilyLaw`, `OAI.SimpleAmenable.InitialCoverSystem.axisSector`, `OAI.SimpleAmenable.InitialCoverSystem.fullGeometricSector`, `OAI.SimpleAmenable.InitialCoverSystem.fullPrimitiveTable`, `OAI.SimpleAmenable.InitialCoverSystem.geometricSector` and 135 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Amenability_BarrierAlgorithm`, `SimpleAmenable_Amenability_BarrierCells`, `SimpleAmenable_Amenability_BarrierCore`, `SimpleAmenable_Amenability_BarrierFiniteMenu`, `SimpleAmenable_Amenability_BarrierLineGeometry`, `SimpleAmenable_Amenability_BarrierSignalSystem`, `SimpleAmenable_Amenability_BarrierSignals`, `SimpleAmenable_Amenability_PartitionArrows`, `SimpleAmenable_Arithmetic_ConcurrentDenominators`, `SimpleAmenable_Arithmetic_LatticeCounting`, `SimpleAmenable_Arithmetic_LatticeRange`, `SimpleAmenable_Arithmetic_LatticeRiemann`, `SimpleAmenable_Arithmetic_PolygonArithmetic`, `SimpleAmenable_Arithmetic_PropagationArithmetic`, `SimpleAmenable_Arithmetic_QuadraticRectangleCounts`, `SimpleAmenable_Arithmetic_QuadraticTiles`, `SimpleAmenable_CentralCovers_AssignmentGeneration`, `SimpleAmenable_CentralCovers_AxisSplitting`, `SimpleAmenable_CentralCovers_BooleanCoordinateGeneration`, `SimpleAmenable_CentralCovers_ConditionalBooleanGeneration`, `SimpleAmenable_CentralCovers_ConditionalFamilyLaws`, `SimpleAmenable_CentralCovers_CoordinateWindowBase`, `SimpleAmenable_CentralCovers_CrossingCellActions`, `SimpleAmenable_CentralCovers_DisjointPolygonAtoms`, `SimpleAmenable_CentralCovers_FullAlphabetGeneration`, `SimpleAmenable_CentralCovers_FullSector`, `SimpleAmenable_CentralCovers_FullSectorCompatibility`, `SimpleAmenable_CentralCovers_GeometricSectors`, `SimpleAmenable_CentralCovers_InitialCoverSystem`, `SimpleAmenable_CentralCovers_PerfectGeneratingFamilies`, `SimpleAmenable_CentralCovers_PrimitiveCopies`, `SimpleAmenable_CentralCovers_PrimitiveGeometricGeneration`, `SimpleAmenable_CentralCovers_PrimitiveTable`, `SimpleAmenable_CentralCovers_PrimitiveWords`, `SimpleAmenable_CentralCovers_SectorDifferenceRange`, `SimpleAmenable_CentralCovers_SmallFamilyGlobal`, `SimpleAmenable_CentralCovers_SmallStarRelators`, `SimpleAmenable_Configurations_FiveTrackGeneration`, `SimpleAmenable_Configurations_FlagExchangeAction`, `SimpleAmenable_Configurations_PointwisePolygonTables`, `SimpleAmenable_Configurations_Rectangles`, `SimpleAmenable_Configurations_SymmetricCharts`, `SimpleAmenable_Homology_ArithmeticTangentBasis`, `SimpleAmenable_Homology_ClippedLineSlide`, `SimpleAmenable_PolygonGeometry_AlignedGroups`, `SimpleAmenable_PolygonGeometry_AxisAnchorFamily`, `SimpleAmenable_PolygonGeometry_AxisCutSequences`, `SimpleAmenable_PolygonGeometry_CellGeometry`, `SimpleAmenable_PolygonGeometry_ChartBoundaryEndpoints`, `SimpleAmenable_PolygonGeometry_ClosedChartOverlap`, `SimpleAmenable_PolygonGeometry_CommonTranslatedCopies`, `SimpleAmenable_PolygonGeometry_ConcurrentAnchors`, `SimpleAmenable_PolygonGeometry_CoordinateWindowTarget`, `SimpleAmenable_PolygonGeometry_DirectionStripCounts`, `SimpleAmenable_PolygonGeometry_EvaluationTable`, `SimpleAmenable_PolygonGeometry_FiniteArrangementGerms`, `SimpleAmenable_PolygonGeometry_FiniteSectorPartition`, `SimpleAmenable_PolygonGeometry_FlagArrangementControl`, `SimpleAmenable_PolygonGeometry_FlagGerms`, `SimpleAmenable_PolygonGeometry_FlagSiteCounts`, `SimpleAmenable_PolygonGeometry_FlagSites`, `SimpleAmenable_PolygonGeometry_FlagTranslation`, `SimpleAmenable_PolygonGeometry_FullGroupAffineData`, `SimpleAmenable_PolygonGeometry_InitialPointwiseTable`, `SimpleAmenable_PolygonGeometry_LabelShiftedCharts`, `SimpleAmenable_PolygonGeometry_PeriodicSlotStars`, `SimpleAmenable_PolygonGeometry_PlaneStepFunctions`, `SimpleAmenable_PolygonGeometry_PolygonAction`, `SimpleAmenable_PolygonGeometry_ResolvedBoolean`, `SimpleAmenable_PolygonGeometry_RoutingIndependence`, `SimpleAmenable_PolygonGeometry_SectorControl`, `SimpleAmenable_PolygonGeometry_Sectors`, `SimpleAmenable_PolygonGeometry_SeparatedAxisSectors`, `SimpleAmenable_PolygonGeometry_SmallControlCalculus`, `SimpleAmenable_PolygonGeometry_SmallFamilyWords`, `SimpleAmenable_PolygonGeometry_SortedAxisCuts`, `SimpleAmenable_PolygonGeometry_SpatialChartGeometry`, `SimpleAmenable_PolygonGeometry_Supported`, `SimpleAmenable_PolygonGeometry_TangentChartTemplates`, `SimpleAmenable_PolygonGeometry_TangentWalkCenters`, `SimpleAmenable_PolygonGeometry_TorusStepFunctions`, `SimpleAmenable_PolygonGeometry_VaryingCellClassification`, `SimpleAmenable_PolygonGeometry_WindowCellPartition`, `SimpleAmenable_PolygonGeometry_WindowCells`, `SimpleAmenable_PolygonGeometry_WindowIntervals`, `SimpleAmenable_PolygonGeometry_WindowSubfamilies`, `SimpleAmenable_RandomFields_FieldHS`, `SimpleAmenable_RandomFields_PrimitiveCovariance`, `SimpleAmenable_RandomFields_SignalGoodRows`, `SimpleAmenable_Simplicial_FinitePowerGeneral`, `SimpleAmenable_Simplicial_ResolutionAugmentation`, `SimpleAmenable_Simplicial_RestrictedNerve`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa000`, `OAIQ65Sa001` and `OAIQ65Sa002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa007`, `OAIQ65Sa008`, `OAIQ65Sa009`, `OAIQ65Sa013` and `OAIQ65Sa014`; the statement `OAI.SimpleAmenable.primitive_laws_eventually`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa000
import Definitions.Def_OAIQ65Sa001
import Definitions.Def_OAIQ65Sa002

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AssignmentGeneration
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
section AssignmentGeneration
open scoped commutatorElement
variable {E Ω : Type*} [Group E]

theorem sectorMask_inter_commutator (U V : Set Ω) (s t : E) :
    sectorMask (U ∩ V) ⁅s,t⁆ = ⁅sectorMask U s,sectorMask V t⁆ := by
  classical
  ext ω
  by_cases hu : ω ∈ U <;> by_cases hv : ω ∈ V <;>
    simp [sectorMask, hu, hv, commutatorElement_def]

theorem sectorMask_complement (U : Set Ω) (s : E) :
    sectorMask Uᶜ s = sectorMask Set.univ s * (sectorMask U s)⁻¹ := by
  classical
  ext ω
  by_cases hu : ω ∈ U <;> simp [sectorMask, hu]

def SectorAvailable (K : Subgroup (Ω → E)) (U : Set Ω) : Prop :=
  ∀ s, sectorMask U s ∈ K

theorem sectorAvailable_inter [Group.IsPerfect E] (K : Subgroup (Ω → E))
    {U V : Set Ω} (hU : SectorAvailable K U) (hV : SectorAvailable K V) :
    SectorAvailable K (U ∩ V) := by
  let L := K.comap (sectorMask (U ∩ V))
  have hL : commutator E ≤ L := by
    rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro s _ t _
    change sectorMask (U ∩ V) ⁅s,t⁆ ∈ K
    rw [sectorMask_inter_commutator]
    exact Subgroup.commutator_le_self K (Subgroup.commutator_mem_commutator (hU s) (hV t))
  intro s
  exact hL (Group.IsPerfect.commutator_eq_top (G := E) ▸ Subgroup.mem_top s)

theorem sectorAvailable_compl (K : Subgroup (Ω → E))
    (hwhole : SectorAvailable K Set.univ) {U : Set Ω} (hU : SectorAvailable K U) :
    SectorAvailable K Uᶜ := by
  intro s
  rw [sectorMask_complement]
  exact K.mul_mem (hwhole s) (K.inv_mem (hU s))

theorem sectorAvailable_finsetInter [Group.IsPerfect E] {ι : Type*}
    (K : Subgroup (Ω → E)) (hwhole : SectorAvailable K Set.univ)
    (U : ι → Set Ω) (S : Finset ι) (hU : ∀ i ∈ S, SectorAvailable K (U i)) :
    SectorAvailable K (⋂ i ∈ S, U i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hwhole
  | @insert i S hi ih =>
    rw [Finset.set_biInter_insert]
    exact sectorAvailable_inter K (hU i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hU j (Finset.mem_insert_of_mem hj)))

theorem assignment_group_generated [Group.IsPerfect E] [Finite Ω]
    {ι : Type*} [Finite ι] (U : ι → Set Ω)
    (hsep : ∀ ω ν : Ω, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (K : Subgroup (Ω → E)) (hwhole : SectorAvailable K Set.univ)
    (hU : ∀ i, SectorAvailable K (U i)) : K = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  have hsingle (ω : Ω) : SectorAvailable K {ω} := by
    let V : ι → Set Ω := fun i => if ω ∈ U i then U i else (U i)ᶜ
    have hV (i : ι) : SectorAvailable K (V i) := by
      dsimp [V]
      split_ifs
      · exact hU i
      · exact sectorAvailable_compl K hwhole (hU i)
    have heq : (⋂ i ∈ Finset.univ, V i) = {ω} := by
      ext ν
      simp only [Set.mem_iInter, Finset.mem_univ, true_implies, Set.mem_singleton_iff]
      constructor
      · intro hν
        apply hsep ν ω
        intro i
        have ht := hν i
        by_cases hi : ω ∈ U i <;> simp_all [V]
      · intro hνω i
        subst ν
        by_cases hi : ω ∈ U i <;> simp [V, hi]
    rw [← heq]
    exact sectorAvailable_finsetInter K hwhole V Finset.univ (fun i _ => hV i)
  apply top_unique
  intro f _
  apply Subgroup.pi_mem_of_mulSingle_mem f
  intro ω
  convert hsingle ω (f ω) using 1
  all_goals try with_reducible_and_instances rfl
  ext ν
  by_cases h : ν = ω
  · subst ν
    simp
  · simp [sectorMask, h]

end AssignmentGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_PolygonArithmetic
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

section PolygonArithmetic

theorem ordinary_injective : Function.Injective ordinary := by
  intro x y h
  have hz : ordinary (x - y) = 0 := by simp [h]
  obtain ⟨hre, him⟩ := golden_coefficients_unique ((ordinary_apply (x - y)).symm.trans hz)
  apply QuadraticAlgebra.ext
  · exact sub_eq_zero.mp hre
  · exact sub_eq_zero.mp him

theorem conjugate_eq_ordinary_star (z : CutRing) : conjugate z = ordinary (star z) := by
  simp only [conjugate_apply, ordinary_apply, QuadraticAlgebra.re_star,
    QuadraticAlgebra.im_star, Int.cast_add, Int.cast_neg, one_mul]
  rw [← Real.one_sub_goldenConj]
  ring

theorem conjugate_injective : Function.Injective conjugate := by
  intro x y h
  have : star x = star y := ordinary_injective (by simpa only [conjugate_eq_ordinary_star] using h)
  simpa using congrArg star this

theorem cut_norm_identity (z : CutRing) :
    ordinary z * conjugate z = ((QuadraticAlgebra.norm z : ℤ) : ℝ) := by
  rw [conjugate_eq_ordinary_star, ← map_mul,
    ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  simp

theorem cut_norm_nonzero {z : CutRing} (hz : z ≠ 0) : QuadraticAlgebra.norm z ≠ 0 := by
  intro h
  have hx : ordinary z ≠ 0 := by simpa using ordinary_injective.ne hz
  have hy : conjugate z ≠ 0 := by simpa using conjugate_injective.ne hz
  exact mul_ne_zero hx hy (by simp [cut_norm_identity, h])

theorem one_le_abs_cut_norm {z : CutRing} (hz : z ≠ 0) :
    1 ≤ |ordinary z * conjugate z| := by
  rw [cut_norm_identity, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (cut_norm_nonzero hz)

theorem endpointLabel_embedding (z : CutRing) :
    (endpointLabel z : ℝ) = (ordinary z - conjugate z) / Real.sqrt 5 := by
  have hs : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply (eq_div_iff hs).mpr
  simp only [ordinary_apply, conjugate_apply, endpointLabel]
  rw [← Real.goldenRatio_sub_goldenConj]
  ring

end PolygonArithmetic

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_PropagationArithmetic
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
section PropagationArithmetic

@[simp] theorem endpointLabel_add (z w : CutRing) :
    endpointLabel (z+w) = endpointLabel z + endpointLabel w := rfl

@[simp] theorem endpointLabel_sub (z w : CutRing) :
    endpointLabel (z-w) = endpointLabel z - endpointLabel w := rfl

@[simp] theorem endpointLabel_intCast (k : ℤ) : endpointLabel (k : CutRing) = 0 := rfl

end PropagationArithmetic

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonAction
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
section PolygonAction

instance instCountableCutRing : Countable CutRing := Countable.of_equiv (ℤ × ℤ) (QuadraticAlgebra.equivProd 1 1).symm

theorem translation_period (a : ℕ) (u : CutRing × CutRing) (k : ℤ × ℤ) :
    translation a (u + ((k.1 : CutRing), (k.2 : CutRing))) = translation a u := by
  ext p
  apply Subtype.ext
  simp [translate_val]
  have h : ∀ x o : ℝ, Int.fract (Int.fract x + o) = Int.fract (x + o) := fun x o => by
    conv_lhs => rw [show Int.fract x + o = (x + o) - ((⌊x⌋ : ℤ) : ℝ) by rw [Int.fract]; ring]
    exact Int.fract_sub_intCast _ _
  exact ⟨h _ _, h _ _⟩

theorem translation_reduce (a : ℕ) (u : CutRing × CutRing) :
    translation a u = translation a
      ((u.1.im : CutRing) * cutTau, (u.2.im : CutRing) * cutTau) := by
  have hu : u = ((u.1.im : CutRing) * cutTau, (u.2.im : CutRing) * cutTau) +
      ((u.1.re : CutRing), (u.2.re : CutRing)) := by
    apply Prod.ext <;> apply QuadraticAlgebra.ext <;> simp [cutTau]
  calc
    _ = translation a (((u.1.im : CutRing) * cutTau, (u.2.im : CutRing) * cutTau) +
        ((u.1.re : CutRing), (u.2.re : CutRing))) := congrArg (translation a) hu
    _ = _ := translation_period _ _ (u.1.re, u.2.re)

end PolygonAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConditionalBooleanGeneration
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
section ConditionalBooleanGeneration

open scoped commutatorElement

noncomputable def trackTranslationAddHom (a m : ℕ) :
    (Fin m → CutRing × CutRing) →+ Additive (polygonFullGroup a m) where
  toFun d := Additive.ofMul (trackTranslation d)
  map_zero' := trackTranslation_zero
  map_add' := trackTranslation_add

theorem trackTranslation_zsmul {a m : ℕ} (n : ℤ) (d : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) (n • d) = (trackTranslation d)^n :=
  (trackTranslationAddHom a m).map_zsmul n d

theorem trackTranslation_reduce {a m : ℕ} (d : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) d = trackTranslation
      (fun i => (((d i).1.im : CutRing)*cutTau,((d i).2.im : CutRing)*cutTau)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change (p.1,translation a (d p.1) p.2) = _
  rw [translation_reduce]
  rfl

end ConditionalBooleanGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PerfectGeneratingFamilies
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
section PerfectGeneratingFamilies

variable {ι G H : Type*} [Group G] [Group H]

variable [Group.IsPerfect G]

theorem universal_generating_ranges {E : ι → Type*} [∀ i, Group (E i)]
    [∀ i, Group.IsPerfect (E i)] (f : ∀ i, E i →* G)
    (hf : (⨆ i, (f i).range) = ⊤) :
    (⨆ i, (universalMap (f i)).range) = ⊤ := by
  apply central_perfect_generating_ranges (universalProjection G)
    (universalProjection_central G) (fun i => universalMap (f i))
  have he (i : ι) : ((universalProjection G).comp (universalMap (f i))).range = (f i).range := by
    rw [universalMap_spec, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (universalProjection_surjective (E i)), ← MonoidHom.range_eq_map]
  simpa only [he] using hf

end PerfectGeneratingFamilies

end SimpleAmenable
end
end

end OAI
end

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

@[simp] theorem sourceLatticeFullMap_of (i : Fin m × Fin 2) :
    sourceLatticeFullMap a r m hm (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
      sourceGenerator a r m (Sum.inr i) := by
  change (sourceLatticeMap a r m hm (Multiplicative.ofAdd (FreeAbelianGroup.of i))).val = _
  rw [sourceLatticeMap,commutingFamilyHom_of]
  rfl

theorem sourceLatticeFullMap_balanced (i : Fin (m+1)) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single i v - Pi.single (Fin.last m) v) ∈
      (sourceLatticeFullMap a r m hm).range := by
  classical
  let K := (sourceLatticeFullMap a r m hm).range
  change _ ∈ K
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  let dx : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc (cutTau,0) - Pi.single (Fin.last m) (cutTau,0)
  let dy : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc (0,cutTau) - Pi.single (Fin.last m) (0,cutTau)
  have hx : trackTranslation (a := a) dx ∈ K :=
    ⟨_,sourceLatticeFullMap_of a r m hm (i,0)⟩
  have hy : trackTranslation (a := a) dy ∈ K := by
    refine ⟨Multiplicative.ofAdd (FreeAbelianGroup.of (i,1)),?_⟩
    simpa only [sourceGenerator,show (1 : Fin 2) ≠ 0 by decide,ite_false]
      using sourceLatticeFullMap_of a r m hm (i,1)
  have he : trackTranslation (a := a) (Pi.single i.castSucc v - Pi.single (Fin.last m) v) =
      trackTranslation (v.1.im • dx + v.2.im • dy) := by
    let d : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc v - Pi.single (Fin.last m) v
    change trackTranslation d = _
    rw [trackTranslation_reduce d]
    congr 1
    funext k
    by_cases hki : k = i.castSucc <;> by_cases hkl : k = Fin.last m <;>
      apply Prod.ext <;> simp [d,dx,dy,hki,hkl,zsmul_eq_mul]
  rw [he,trackTranslation_add,trackTranslation_zsmul,trackTranslation_zsmul]
  exact K.mul_mem (K.zpow_mem hx _) (K.zpow_mem hy _)

theorem sourceLatticeFullMap_difference (i j : Fin (m+1)) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single j v - Pi.single i v) ∈
      (sourceLatticeFullMap a r m hm).range := by
  have he : (Pi.single j v - Pi.single i v : Fin (m+1) → CutRing × CutRing) =
      (Pi.single j v - Pi.single (Fin.last m) v) -
        (Pi.single i v - Pi.single (Fin.last m) v) := by abel
  rw [he,trackTranslation_sub]
  exact (sourceLatticeFullMap a r m hm).range.mul_mem
    (sourceLatticeFullMap_balanced a r m hm j v)
    ((sourceLatticeFullMap a r m hm).range.inv_mem
      (sourceLatticeFullMap_balanced a r m hm i v))

theorem sourceLatticeFullMap_prescribed (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (u : Fin (m+1) → CutRing × CutRing) :
    ∃ k d, sourceLatticeFullMap a r m hm k = trackTranslation d ∧
      ∀ i ∈ I, d i = u i := by
  classical
  let d : Fin (m+1) → CutRing × CutRing :=
    ∑ i ∈ I, (Pi.single i (u i) - Pi.single b (u i))
  have hd : trackTranslation (a := a) d ∈ (sourceLatticeFullMap a r m hm).range := by
    dsimp only [d]
    clear hb
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,trackTranslation_add]
      exact (sourceLatticeFullMap a r m hm).range.mul_mem
        (sourceLatticeFullMap_difference a r m hm b i (u i)) ih
  obtain ⟨k,hk⟩ := hd
  refine ⟨k,d,hk,?_⟩
  intro i hi
  have hib : i ≠ b := fun h => hb (h ▸ hi)
  simp [d,Finset.sum_apply,Pi.sub_apply,Pi.single_apply,hib,hi]

end SourceLatticeRange

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_BooleanCoordinateGeneration
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
section BooleanCoordinateGeneration

noncomputable def coordinate {a : ℕ} (j : Fin 2) (p : GenericSquare a) : ℝ :=
  ![p.val.1,p.val.2] j

theorem coordinate_bounds {a : ℕ} (j : Fin 2) (p : GenericSquare a) :
    0 ≤ coordinate j p ∧ coordinate j p < 1 := by
  fin_cases j
  · exact p.property.1
  · exact p.property.2.1

theorem coordinate_translate {a : ℕ} (j : Fin 2) (z : CutRing) (p : GenericSquare a) :
    coordinate j (translate a (coordinateShift j z) p) =
      Int.fract (coordinate j p + ordinary z) := by
  fin_cases j <;> simp [coordinate,coordinateShift,translate_val]

noncomputable def coordinateArc (a : ℕ) (j : Fin 2) (z : CutRing) : Set (GenericSquare a) :=
  {p | coordinate j p < Int.fract (ordinary z)}

theorem fract_add_fracts (x y : ℝ) :
    Int.fract (Int.fract x + Int.fract y) = Int.fract (x+y) := by
  rw [fract_fract_add]
  change Int.fract (x+(y-(⌊y⌋ : ℝ))) = _
  rw [← add_sub_assoc,Int.fract_sub_intCast]

theorem coordinateArc_add {a : ℕ} (j : Fin 2) (u v : CutRing) :
    coordinateArc a j (u+v) =
      if Int.fract (ordinary u)+Int.fract (ordinary v) < 1 then
        symmDiff (coordinateArc a j u)
          (translate a (coordinateShift j (-u)) ⁻¹' coordinateArc a j v)
      else (symmDiff (coordinateArc a j u)
          (translate a (coordinateShift j (-u)) ⁻¹' coordinateArc a j v))ᶜ := by
  ext p
  have hc := arc_add_test (coordinate j p) (Int.fract (ordinary u)) (Int.fract (ordinary v))
    (coordinate_bounds j p) ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
      ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  rw [fract_add_fracts,fract_sub_fract] at hc
  split_ifs with h
  · simpa only [coordinateArc,Set.mem_ofPred_eq,Set.mem_symmDiff,Set.mem_preimage,
      coordinate_translate,map_neg,map_add,sub_eq_add_neg,Xor,h,ite_true] using hc
  · simpa only [coordinateArc,Set.mem_ofPred_eq,Set.mem_compl_iff,Set.mem_symmDiff,
      Set.mem_preimage,coordinate_translate,map_neg,map_add,sub_eq_add_neg,Xor,h,ite_false] using hc

theorem coordinateArc_neg {a : ℕ} (j : Fin 2) (u : CutRing)
    (hu : Int.fract (ordinary u) ≠ 0) :
    coordinateArc a j (-u) =
      (translate a (coordinateShift j u) ⁻¹' coordinateArc a j u)ᶜ := by
  ext p
  simp only [coordinateArc,Set.mem_ofPred_eq,Set.mem_compl_iff,Set.mem_preimage,
    coordinate_translate,map_neg,Int.fract_neg hu]
  rw [← fract_fract_add (coordinate j p) (ordinary u)]
  rw [Int.fract_eq_self.mpr (coordinate_bounds j p)]
  have he : Int.fract (coordinate j p + ordinary u) =
      Int.fract (coordinate j p + Int.fract (ordinary u)) := by
    rw [← fract_add_fracts,Int.fract_eq_self.mpr (coordinate_bounds j p)]
  rw [he]
  exact arc_neg_test _ _ (coordinate_bounds j p)
    ⟨lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hu),Int.fract_lt_one _⟩

theorem coordinateArc_zero_of_fract {a : ℕ} (j : Fin 2) (u : CutRing)
    (hu : Int.fract (ordinary u) = 0) : coordinateArc a j u = ∅ := by
  ext p
  simp only [coordinateArc,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_lt,hu]
  exact (coordinate_bounds j p).1

end BooleanCoordinateGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FiveTrackGeneration
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
section FiveTrackGeneration

theorem conditional_translation_conjugate {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (d : Fin m → CutRing × CutRing) (u : CutRing × CutRing)
    (hd : ∀ i, σ i ≠ i → d i = u) :
    conditionalHom (⟨translate a (-u) ⁻¹' U.val,
      polygon_preimage_translate (-u) U.property⟩ : polygonAlgebra a) σ =
      trackTranslation d * conditionalHom U σ * (trackTranslation d)⁻¹ := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨i,p⟩
  change conditionalPerm (⟨_,_⟩ : polygonAlgebra a) σ (i,p) =
    trackTranslationPerm d (conditionalPerm U σ ((trackTranslationPerm d).symm (i,p)))
  by_cases hi : σ i = i
  · simp [conditionalPerm,trackTranslationPerm,hi,← translate_add]
  · have hi' : σ (σ i) ≠ σ i := fun h => hi (σ.injective h)
    have hdi := hd i hi
    have hdsi := hd (σ i) hi'
    by_cases hp : translate a (-u) p ∈ U.val <;>
      simp_all [conditionalPerm,trackTranslationPerm,← translate_add]

end FiveTrackGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AlignedGroups
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

section SourceAlignedGroups

noncomputable def sourceAlignedGroup (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (M : ℕ) (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)) (I : Finset (Fin (m+1))) :
      Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  alignedGroup t (fun b : SmallConditional m => PresentedGroup.of (Sum.inl b))
    (fun b => b.2.val.support ⊆ I)

end SourceAlignedGroups

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_Supported
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
section LocalDisplacement

theorem ordinary_denseRange : DenseRange ordinary := by
  have hd : Dense (AddSubgroup.closure {Real.goldenRatio, (1 : ℝ)} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (by simpa using Real.goldenRatio_irrational)
  apply hd.mono
  change AddSubgroup.closure {Real.goldenRatio, (1 : ℝ)} ≤ ordinary.toAddMonoidHom.range
  apply (AddSubgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact ⟨cutTau, ordinary_cutTau⟩
  · have hx' : x = 1 := by simpa using hx
    subst x
    exact ⟨1,map_one ordinary⟩

theorem exists_cut_between {x y : ℝ} (hxy : x < y) :
    ∃ c : CutRing, x < ordinary c ∧ ordinary c < y :=
  ordinary_denseRange.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hxy)

theorem cutForm_continuous (a : ℕ) (j : Fin 4) : Continuous (cutForm a j) := by
  fin_cases j
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_snd.sub (continuous_const.mul continuous_fst)
  · exact continuous_fst.sub (continuous_const.mul continuous_snd)

theorem generic_coordinates_pos {a : ℕ} (p : GenericSquare a) :
    0 < p.val.1 ∧ 0 < p.val.2 := by
  constructor
  · exact lt_of_le_of_ne p.property.1.1 (by simpa [cutForm] using (p.property.2.2 0 0).symm)
  · exact lt_of_le_of_ne p.property.2.1.1 (by simpa [cutForm] using (p.property.2.2 1 0).symm)

noncomputable def translatedPolygon {a : ℕ} (u : CutRing × CutRing)
    (U : polygonAlgebra a) : polygonAlgebra a :=
  ⟨translation a u '' U.val,polygon_image_translation u U.property⟩

end LocalDisplacement
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveGeometricGeneration
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
section PrimitiveGeometricGeneration

theorem cutForm_sub (a : ℕ) (j : Fin 4) (p q : ℝ × ℝ) :
    cutForm a j (p-q) = cutForm a j p - cutForm a j q := by
  fin_cases j <;> simp [cutForm] <;> ring

noncomputable def ordinaryBox (l h : CutRing × CutRing) : Set (ℝ × ℝ) :=
  Set.Ioo (ordinary l.1) (ordinary h.1) ×ˢ Set.Ioo (ordinary l.2) (ordinary h.2)

theorem exists_box_in_open {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (p : ℝ × ℝ) (hp : p ∈ U) :
    ∃ l h : CutRing × CutRing, p ∈ ordinaryBox l h ∧ ordinaryBox l h ⊆ U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU p hp
  obtain ⟨l₁,hl₁,hlp⟩ := exists_cut_between (show p.1-ε < p.1 by linarith)
  obtain ⟨l₂,hl₂,hlq⟩ := exists_cut_between (show p.2-ε < p.2 by linarith)
  obtain ⟨h₁,hph,hh₁⟩ := exists_cut_between (show p.1 < p.1+ε by linarith)
  obtain ⟨h₂,hqh,hh₂⟩ := exists_cut_between (show p.2 < p.2+ε by linarith)
  refine ⟨(l₁,l₂),(h₁,h₂),⟨⟨hlp,hph⟩,⟨hlq,hqh⟩⟩,?_⟩
  rintro q ⟨⟨hqx,hqx'⟩,⟨hqy,hqy'⟩⟩
  apply hball
  change max (dist q.1 p.1) (dist q.2 p.2) < ε
  rw [max_lt_iff,Real.dist_eq,Real.dist_eq,abs_lt,abs_lt]
  constructor <;> constructor <;> linarith

end PrimitiveGeometricGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PointwisePolygonTables
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
section PointwisePolygonTables

variable {a m : ℕ}

theorem PolygonLabelling.tableHom_injective {Ω : Type*} [Fintype Ω]
    (v : PolygonLabelling a Ω) (hv : Function.Surjective v.label) :
    Function.Injective (v.tableHom (m := m)) := by
  intro s t h
  funext ω
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨p,hp⟩ := hv ω
  have he := congrArg (fun g : polygonAlternatingGroup a m => g.val.val (i,p)) h
  simpa only [v.tableHom_apply, hp] using congrArg Prod.fst he

theorem actualPolygonLabelling_surjective {ι : Type*} [Finite ι]
    (U : ι → polygonAlgebra a) : Function.Surjective (actualPolygonLabelling U).label := by
  rintro ⟨ω,p,rfl⟩
  exact ⟨p,rfl⟩

end PointwisePolygonTables

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InitialPointwiseTable
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
section SourceInitialPointwiseTable

variable {a m : ℕ} {ι : Type*} [Finite ι]

theorem actualPolygonTableHom_injective (U : ι → polygonAlgebra a) :
    Function.Injective (actualPolygonTableHom (m := m) U) := by
  classical
  let := Fintype.ofFinite (Set.range (polygonAssignment U))
  exact (actualPolygonLabelling U).tableHom_injective (actualPolygonLabelling_surjective U)

end SourceInitialPointwiseTable

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

structure InitialCoverSystem (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) (M : ℕ) where
  t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)
  c : alternatingGroup (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)
  t_base : ∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
    PresentedGroup.of (Sum.inr i)
  t_projection : (coverMap M (alternatingGenerator a r m hm)).comp t =
    sourceLatticeMap a r m hm
  t_stabilizers : ∀ s k, Commute (sourceLatticeMap a r m hm k)
    (alternatingGenerator a r m hm s) → Commute (t k) (PresentedGroup.of s)
  c_projection : (coverMap M (alternatingGenerator a r m hm)).comp c =
    conditionalAlternatingHom (wholePolygon a)
  c_base : ∀ b : {σ : Equiv.Perm (Fin (m+1)) // σ ∈ alternatingGroup (Fin (m+1)) ∧
    σ.support.card ≤ 5}, c ⟨b.val,b.property.1⟩ =
      PresentedGroup.of (sourceConditionalLabel m (0,b))
  constant_aligned : ∀ (s : alternatingGroup (Fin (m+1))) (I : Finset (Fin (m+1))),
    ∀ y ∈ sourceAlignedGroup a r m hm M t I,
      c s*y*(c s)⁻¹ ∈ sourceAlignedGroup a r m hm M t (I.map s.val.toEmbedding)
  disjoint_aligned : ∀ (I J : Finset (Fin (m+1))), Disjoint I J →
    ∀ x ∈ sourceAlignedGroup a r m hm M t I,
    ∀ y ∈ sourceAlignedGroup a r m hm M t J, Commute x y
  initialTable : (Set.range (polygonAssignment (initialTest a r)) →
    alternatingGroup (Fin (m+1))) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)
  initialTable_projection : (coverMap M (alternatingGenerator a r m hm)).comp initialTable =
    actualPolygonTableHom (initialTest a r)
  initialTable_injective : Function.Injective initialTable
  initialTable_input : ∀ b, initialTable (polygonTableInput (initialTest a r) b.1
    (⟨b.2.val,b.2.property.1⟩ : alternatingGroup (Fin (m+1)))) =
      PresentedGroup.of (sourceConditionalLabel m b)
  perfect : Group.IsPerfect (BoundedRelationCover M (alternatingGenerator a r m hm))

end InitialCoverSystem

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConditionalFamilyLaws
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
section ConditionalFamilyLaws

variable {ι E H Ω : Type*} [Group E] [Group H]

noncomputable def maskFamily (U : ι → Set Ω) : Option ι → E →* (Ω → E)
  | none => sectorMask Set.univ
  | some i => sectorMask (U i)

noncomputable def assignmentEval (U : ι → Set Ω) :
    FreeGroup (Option ι × E) →* (Ω → E) := copyFamilyEval (maskFamily U)

theorem assignmentEval_surjective [Group.IsPerfect E] [Finite ι] [Finite Ω]
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν) :
    Function.Surjective (assignmentEval (E := E) U) := by
  apply MonoidHom.range_eq_top.mp
  apply assignment_group_generated U hsep
  · intro s
    exact ⟨FreeGroup.of (none,s),copyFamilyEval_of _ _ _⟩
  · intro i s
    exact ⟨FreeGroup.of (some i,s),copyFamilyEval_of _ _ _⟩

end ConditionalFamilyLaws

section ActualFamilyLaws

variable {ι E H Q : Type*} [Group E] [Group H] [Group Q]

theorem centralOn_iff (q : H →* Q) (S : Subgroup H) :
    CentralOn q S ↔ ∀ x ∈ S, q x = 1 → ∀ y ∈ S, Commute x y := by
  constructor
  · intro h x hx hqx y hy
    exact (show Commute y x from congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (h (show ⟨x,hx⟩ ∈ (q.comp S.subtype).ker from hqx))
        ⟨y,hy⟩)).symm
  · intro h x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (h x.val x.property hx y.val y.property).symm.eq

theorem CentralOn.mono {q : H →* Q} {S T : Subgroup H}
    (h : CentralOn q T) (hst : S ≤ T) : CentralOn q S := by
  rw [centralOn_iff] at h ⊢
  intro x hx hqx y hy
  exact h x (hst hx) hqx y (hst hy)

end ActualFamilyLaws

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

noncomputable def initialConditional (j : Fin 5) :
    alternatingGroup (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.initialTable.comp (polygonTableInput (initialTest a r) j)

@[simp] theorem initialConditional_input (j : Fin 5)
    (s : alternatingGroup (Fin (m+1))) (hs : s.val.support.card ≤ 5) :
    B.initialConditional j s = PresentedGroup.of (sourceConditionalLabel m (j,⟨s.val,s.property,hs⟩)) :=
  B.initialTable_input (j,⟨s.val,s.property,hs⟩)

theorem initialConditional_projection (j : Fin 5) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.initialConditional j) =
    conditionalAlternatingHom (initialTest a r j) := by
  rw [initialConditional,← MonoidHom.comp_assoc,B.initialTable_projection]
  apply MonoidHom.ext
  intro s
  exact actualPolygonTableHom_input (initialTest a r) j s

noncomputable def initialAlphabet (I : Finset (Fin (m+1))) (j : Fin 5) :
    alternatingGroup I →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.initialConditional j).comp (subtypeAlternatingHom I)

noncomputable def translatedAlphabet (I : Finset (Fin (m+1))) (j : Fin 5)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    alternatingGroup I →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (MulAut.conj (B.t k)).toMonoidHom.comp (B.initialAlphabet I j)

theorem initialAlphabet_orbit_independent (I : Finset (Fin (m+1))) (j : Fin 5)
    (k l : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hkl : ∀ s : alternatingGroup I,
      sourceLatticeMap a r m hm k * conditionalAlternatingHom (initialTest a r j)
        (subtypeAlternatingHom I s) * (sourceLatticeMap a r m hm k)⁻¹ =
      sourceLatticeMap a r m hm l * conditionalAlternatingHom (initialTest a r j)
        (subtypeAlternatingHom I s) * (sourceLatticeMap a r m hm l)⁻¹) :
    B.translatedAlphabet I j k = B.translatedAlphabet I j l := by
  apply MonoidHom.eq_of_eqOn_dense alternatingGroup.closure_isThreeCycles_eq_top
  intro s hs
  have hc : (subtypeAlternatingHom I s).val.support.card ≤ 5 := by
    change (Equiv.Perm.ofSubtype s.val).support.card ≤ 5
    have hI : (Subtype.fintype (fun x : Fin (m+1) => x ∈ I)) =
        (inferInstance : Fintype I) := Subsingleton.elim _ _
    rw [Equiv.Perm.support_ofSubtype, Finset.card_map, hI, hs.card_support]
    decide
  change B.t k * B.initialConditional j (subtypeAlternatingHom I s) * (B.t k)⁻¹ =
    B.t l * B.initialConditional j (subtypeAlternatingHom I s) * (B.t l)⁻¹
  rw [B.initialConditional_input j _ hc]
  exact lifted_translation_orbit_independent (sourceLatticeMap a r m hm) B.t
    (alternatingGenerator a r m hm (sourceConditionalLabel m
      (j,⟨(subtypeAlternatingHom I s).val,(subtypeAlternatingHom I s).property,hc⟩)))
    _ (B.t_stabilizers _) k l (hkl s)

end InitialCoverSystem
end PrimitiveCopies

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CommonTranslatedCopies
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
section CommonTranslatedCopies

structure CommonFrame (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (u : CutRing × CutRing) where
  k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))
  d : Fin (m+1) → CutRing × CutRing
  projection : sourceLatticeFullMap a r m hm k = trackTranslation d
  common : ∀ i ∈ I, d i = u

noncomputable def commonFrame (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) (u : CutRing × CutRing) :
    CommonFrame a r m hm I u := by
  let h := sourceLatticeFullMap_prescribed a r m hm I b hb (fun _ => u)
  exact {
    k := h.choose
    d := h.choose_spec.choose
    projection := h.choose_spec.choose_spec.1
    common := h.choose_spec.choose_spec.2 }

noncomputable def spatialTranslate {a : ℕ} (u : CutRing × CutRing)
    (U : polygonAlgebra a) : polygonAlgebra a :=
  ⟨translate a (-u) ⁻¹' U.val,polygon_preimage_translate (-u) U.property⟩

namespace CommonFrame

variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {I : Finset (Fin (m+1))} {u : CutRing × CutRing}
    (F : CommonFrame a r m hm I u)

theorem conditional_projection (U : polygonAlgebra a) (s : alternatingGroup I) :
    sourceLatticeMap a r m hm F.k * conditionalAlternatingHom U (subtypeAlternatingHom I s) *
        (sourceLatticeMap a r m hm F.k)⁻¹ =
      conditionalAlternatingHom (spatialTranslate u U) (subtypeAlternatingHom I s) := by
  apply Subtype.ext
  change sourceLatticeFullMap a r m hm F.k * conditionalHom U (subtypeAlternatingHom I s).val *
    (sourceLatticeFullMap a r m hm F.k)⁻¹ = _
  rw [F.projection]
  apply (conditional_translation_conjugate U (subtypeAlternatingHom I s).val F.d u ?_).symm
  intro i hi
  exact F.common i ((Equiv.Perm.mem_range_ofSubtype_iff.mp ⟨s.val,rfl⟩)
    (Equiv.Perm.mem_support.mpr hi))

end CommonFrame

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem commonTranslatedAlphabet_projection {I : Finset (Fin (m+1))}
    {u : CutRing × CutRing} (F : CommonFrame a r m hm I u) (j : Fin 5) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.translatedAlphabet I j F.k) =
      (conditionalAlternatingHom (spatialTranslate u (initialTest a r j))).comp
        (subtypeAlternatingHom I) := by
  apply MonoidHom.ext
  intro s
  change coverMap M (alternatingGenerator a r m hm)
    (B.t F.k * B.initialConditional j (subtypeAlternatingHom I s) * (B.t F.k)⁻¹) = _
  rw [map_mul,map_mul,map_inv]
  rw [show coverMap M (alternatingGenerator a r m hm) (B.t F.k) =
    sourceLatticeMap a r m hm F.k from DFunLike.congr_fun B.t_projection F.k]
  rw [show coverMap M (alternatingGenerator a r m hm)
    (B.initialConditional j (subtypeAlternatingHom I s)) =
    conditionalAlternatingHom (initialTest a r j) (subtypeAlternatingHom I s) from
      DFunLike.congr_fun (B.initialConditional_projection j) (subtypeAlternatingHom I s)]
  exact F.conditional_projection _ s

theorem commonTranslatedAlphabet_independent {I : Finset (Fin (m+1))}
    {u v : CutRing × CutRing} (F : CommonFrame a r m hm I u)
    (G : CommonFrame a r m hm I v) (j : Fin 5)
    (huv : spatialTranslate u (initialTest a r j) = spatialTranslate v (initialTest a r j)) :
    B.translatedAlphabet I j F.k = B.translatedAlphabet I j G.k := by
  apply B.initialAlphabet_orbit_independent
  intro s
  rw [F.conditional_projection,G.conditional_projection,huv]

noncomputable def primitiveCopy (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (p : Fin 5 × (CutRing × CutRing)) :
    alternatingGroup I →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.translatedAlphabet I p.1 (commonFrame a r m hm I b hb p.2).k

theorem primitiveCopy_projection (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (p : Fin 5 × (CutRing × CutRing)) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.primitiveCopy I b hb p) =
      (conditionalAlternatingHom (spatialTranslate p.2 (initialTest a r p.1))).comp
        (subtypeAlternatingHom I) :=
  B.commonTranslatedAlphabet_projection (commonFrame a r m hm I b hb p.2) p.1

end InitialCoverSystem
end CommonTranslatedCopies

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveWords
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

section PrimitiveFamilyLaws

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {ι : Type*}

noncomputable def primitiveFamilyTests (P : ι → Fin 5 × (CutRing × CutRing)) :
    Option ι → polygonAlgebra a
  | none => wholePolygon a
  | some i => spatialTranslate (P i).2 (initialTest a r (P i).1)

namespace InitialCoverSystem

variable (B : InitialCoverSystem a r m hm M)

noncomputable def primitiveFamily (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) :
    Option ι → alternatingGroup I →* BoundedRelationCover M (alternatingGenerator a r m hm)
  | none => B.initialAlphabet I 0
  | some i => B.primitiveCopy I b hb (P i)

def PrimitiveFamilyLaw (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) : Prop :=
  CentralOn (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb P)).range

theorem primitiveFamily_projection (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) (i : Option ι) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.primitiveFamily I b hb P i) =
      (conditionalAlternatingHom (primitiveFamilyTests (a := a) (r := r) P i)).comp (subtypeAlternatingHom I) := by
  cases i with
  | none =>
    rw [primitiveFamily,initialAlphabet,← MonoidHom.comp_assoc,
      B.initialConditional_projection]
    rfl
  | some i => exact B.primitiveCopy_projection I b hb (P i)

end InitialCoverSystem

end PrimitiveFamilyLaws

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

@[simp] theorem initialTest_coordinate (a : ℕ) (r : CutRing) (j : Fin 2) :
    initialTest a r (coordinateTestIndex j) = coordinatePrimitive a j := by
  fin_cases j <;> rfl

noncomputable def coordinateWindowPrimitives (n : ℕ) (q : Fin 2 → ℤ) :
    Fin 2 × Fin (n-1) → Fin 5 × (CutRing × CutRing) := fun i =>
  (coordinateTestIndex i.1,coordinateShift i.1 (((q i.1 + (i.2.val : ℤ)) : CutRing)*cutTau))

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

def CoordinateWindowLaw (n : ℕ) : Prop :=
  ∀ (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) (q : Fin 2 → ℤ),
    B.PrimitiveFamilyLaw I b hb (coordinateWindowPrimitives n q)

end InitialCoverSystem

end CoordinateWindowTarget

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PrimitiveCovariance
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
section PrimitiveCovariance

@[simp] theorem spatialTranslate_zero {a : ℕ} (U : polygonAlgebra a) :
    spatialTranslate 0 U = U := by
  apply Subtype.ext
  ext x
  simp [spatialTranslate]

@[simp] theorem spatialTranslate_whole {a : ℕ} (u : CutRing × CutRing) :
    spatialTranslate u (wholePolygon a) = wholePolygon a := by
  apply Subtype.ext
  rfl

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem primitiveCopy_frame (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (p : Fin 5 × (CutRing × CutRing))
    (F : CommonFrame a r m hm I p.2) :
    B.primitiveCopy I b hb p = B.translatedAlphabet I p.1 F.k :=
  B.commonTranslatedAlphabet_independent (commonFrame a r m hm I b hb p.2) F p.1 rfl

end InitialCoverSystem
end PrimitiveCovariance

section FamilyCovariance

variable {ι E H Q : Type*} [Group E] [Group H] [Group Q]

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem PrimitiveFamilyLaw.reindex {κ : Type*} (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (v : κ → ι) :
    B.PrimitiveFamilyLaw I b hb (P ∘ v) := by
  apply CentralOn.mono h
  have he : B.primitiveFamily I b hb (P ∘ v) =
      B.primitiveFamily I b hb P ∘ Option.map v := by
    funext i
    cases i <;> rfl
  rw [he]
  exact copyFamilyEval_reindex_range _ _

end InitialCoverSystem
end FamilyCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CoordinateWindowBase
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
section CoordinateWindowBase

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem CoordinateWindowLaw.mono {n k : ℕ} (h : B.CoordinateWindowLaw n) (hk : k ≤ n) :
    B.CoordinateWindowLaw k := by
  intro I b hb q
  let v : Fin 2 × Fin (k-1) → Fin 2 × Fin (n-1) :=
    fun i => (i.1,Fin.castLE (by omega) i.2)
  exact PrimitiveFamilyLaw.reindex B I b hb (coordinateWindowPrimitives n q) (h I b hb q) v

end InitialCoverSystem

end CoordinateWindowBase

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_Sectors
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
section ActualSectors

variable {P E H Q Ω : Type*} [Group P] [Group E] [Group H] [Group Q]

section FamilyModel
variable {ι : Type*} (U : ι → Set Ω) (F : Option ι → E →* H)
    (q : H →* Q) (v : (Ω → E) →* Q)
    (hv : Function.Injective v)
    (hcompat : ∀ i, q.comp (F i) = v.comp (maskFamily U i))

include hcompat in
theorem copyFamilyEval_projection : q.comp (copyFamilyEval F) = v.comp (assignmentEval U) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  simpa only [MonoidHom.comp_apply,assignmentEval,copyFamilyEval_of] using
    DFunLike.congr_fun (hcompat i) s

noncomputable def actualFamilyModel : (copyFamilyEval F).range →* (Ω → E) :=
  (copyFamilyEval F).rangeRestrict.liftOfSurjective
    (copyFamilyEval F).rangeRestrict_surjective ⟨assignmentEval U, by
      intro w hw
      apply hv
      have hh := DFunLike.congr_fun (copyFamilyEval_projection U F q v hcompat) w
      change q (copyFamilyEval F w) = v (assignmentEval U w) at hh
      have hw' : copyFamilyEval F w = 1 := congrArg Subtype.val hw
      rw [hw',map_one] at hh
      simpa only [map_one] using hh.symm⟩

theorem actualFamilyModel_comp :
    (actualFamilyModel U F q v hv hcompat).comp (copyFamilyEval F).rangeRestrict =
      assignmentEval U :=
  (copyFamilyEval F).rangeRestrict.liftOfRightInverse_comp _ _ _

theorem actualFamilyModel_projection :
    q.comp (copyFamilyEval F).range.subtype = v.comp (actualFamilyModel U F q v hv hcompat) := by
  ext x
  obtain ⟨w,rfl⟩ := (copyFamilyEval F).rangeRestrict_surjective x
  have he := DFunLike.congr_fun (actualFamilyModel_comp U F q v hv hcompat) w
  change actualFamilyModel U F q v hv hcompat ((copyFamilyEval F).rangeRestrict w) =
    assignmentEval U w at he
  simp only [MonoidHom.comp_apply]
  rw [he]
  exact DFunLike.congr_fun (copyFamilyEval_projection U F q v hcompat) w

noncomputable def actualFamilyTable [Group.IsPerfect E] [Finite ι] [Finite Ω]
    (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (h : CentralOn q (copyFamilyEval F).range) : ActualLawfulTable q v where
  carrier := (copyFamilyEval F).range
  law := h
  model := actualFamilyModel U F q v hv hcompat
  onto := by
    intro s
    obtain ⟨w,rfl⟩ := assignmentEval_surjective U hsep s
    exact ⟨(copyFamilyEval F).rangeRestrict w,
      DFunLike.congr_fun (actualFamilyModel_comp U F q v hv hcompat) w⟩
  projection := actualFamilyModel_projection U F q v hv hcompat

end FamilyModel
end ActualSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveTable
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
section ActualPrimitiveTable

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {ι : Type*} [Finite ι]

noncomputable def actualAlphabetTableHom (I : Finset (Fin (m+1)))
    (U : ι → polygonAlgebra a) :
    (Set.range (polygonAssignment U) → alternatingGroup I) →* polygonAlternatingGroup a (m+1) :=
  (actualPolygonTableHom U).comp (tableAlphabetHom I)

theorem actualAlphabetTableHom_injective (I : Finset (Fin (m+1)))
    (U : ι → polygonAlgebra a) : Function.Injective (actualAlphabetTableHom I U) :=
  (actualPolygonTableHom_injective U).comp (tableAlphabetHom_injective I)

noncomputable def actualTestMask (U : ι → polygonAlgebra a) (i : ι) :
    Set (Set.range (polygonAssignment U)) := {ω | ω.val i = true}

omit [Finite ι] in
theorem actualTestMask_separates (U : ι → polygonAlgebra a)
    (ω ν : Set.range (polygonAssignment U))
    (h : ∀ i, ω ∈ actualTestMask U i ↔ ν ∈ actualTestMask U i) : ω = ν := by
  apply Subtype.ext
  funext i
  apply Bool.eq_iff_iff.mpr
  exact h i

theorem tableAlphabetHom_mask (I : Finset (Fin (m+1))) {Ω : Type*}
    (V : Set Ω) (s : alternatingGroup I) :
    tableAlphabetHom I (sectorMask V s) = sectorMask V (subtypeAlternatingHom I s) := by
  classical
  funext ω
  by_cases h : ω ∈ V <;> simp [tableAlphabetHom,sectorMask,h]

theorem actualPolygonTableHom_whole (U : ι → polygonAlgebra a)
    (s : alternatingGroup (Fin (m+1))) :
    actualPolygonTableHom U (sectorMask Set.univ s) =
      conditionalAlternatingHom (wholePolygon a) s := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [actualPolygonTableHom_apply]
  simp only [sectorMask_of_mem Set.univ s _ (Set.mem_univ _)]
  change (s.val p.1,p.2) = conditionalPerm (wholePolygon a) s.val p
  rw [conditionalPerm_apply]
  simp only [wholePolygon,Set.mem_univ,ite_true]

theorem actualAlphabetTableHom_masks (I : Finset (Fin (m+1)))
    (U : ι → polygonAlgebra a) (i : Option ι) :
    (actualAlphabetTableHom I U).comp (maskFamily (actualTestMask U) i) =
      (conditionalAlternatingHom (match i with
        | none => wholePolygon a
        | some j => U j)).comp (subtypeAlternatingHom I) := by
  apply MonoidHom.ext
  intro s
  cases i with
  | none =>
    change actualPolygonTableHom U (tableAlphabetHom I (sectorMask Set.univ s)) = _
    rw [tableAlphabetHom_mask,actualPolygonTableHom_whole]
    rfl
  | some j =>
    change actualPolygonTableHom U (tableAlphabetHom I (sectorMask (actualTestMask U j) s)) = _
    rw [tableAlphabetHom_mask]
    exact actualPolygonTableHom_input U j (subtypeAlternatingHom I s)

namespace InitialCoverSystem

variable (B : InitialCoverSystem a r m hm M)

noncomputable def primitiveTests (P : ι → Fin 5 × (CutRing × CutRing)) :
    ι → polygonAlgebra a := fun i => primitiveFamilyTests (r := r) P (some i)

noncomputable def primitiveTable (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) :
    ActualLawfulTable (coverMap M (alternatingGenerator a r m hm))
      (actualAlphabetTableHom I (primitiveTests (a := a) (r := r) P)) :=
  actualFamilyTable (actualTestMask (primitiveTests (a := a) (r := r) P)) (B.primitiveFamily I b hb P)
    (coverMap M (alternatingGenerator a r m hm)) (actualAlphabetTableHom I (primitiveTests (a := a) (r := r) P))
    (actualAlphabetTableHom_injective I (primitiveTests (a := a) (r := r) P))
    (fun i => by
      rw [B.primitiveFamily_projection,actualAlphabetTableHom_masks]
      cases i <;> rfl)
    (actualTestMask_separates (primitiveTests (a := a) (r := r) P)) h

end InitialCoverSystem
end ActualPrimitiveTable

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ResolvedBoolean
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
section ResolvedBoolean

variable {X ι : Type*}

variable {a : ℕ}

noncomputable def resolvedPolygonMask (U : ι → polygonAlgebra a)
    (V : Set (GenericSquare a)) : Set (Set.range (polygonAssignment U)) :=
  {ω | ∃ x, polygonAssignment U x = ω.val ∧ x ∈ V}

theorem polygonAssignment_eq_iff (U : ι → polygonAlgebra a) (x y : GenericSquare a) :
    polygonAssignment U x = polygonAssignment U y ↔
      ∀ i, x ∈ (U i).val ↔ y ∈ (U i).val := by
  classical
  constructor
  · intro h i
    have hi := congrFun h i
    simpa only [polygonAssignment,decide_eq_decide] using hi
  · intro h
    funext i
    exact decide_eq_decide.mpr (h i)

theorem resolvedPolygonMask_mem (U : ι → polygonAlgebra a)
    (V : Set (GenericSquare a)) (hV : ResolvedBy (fun i => (U i).val) V)
    (x : GenericSquare a) :
    (⟨polygonAssignment U x,⟨x,rfl⟩⟩ : Set.range (polygonAssignment U)) ∈
       resolvedPolygonMask U V ↔ x ∈ V := by
  constructor
  · rintro ⟨y,he,hy⟩
    exact (hV y x ((polygonAssignment_eq_iff U y x).mp he)).mp hy
  · intro hx
    exact ⟨x,rfl,hx⟩

theorem resolvedPolygonMask_disjoint (U : ι → polygonAlgebra a)
    {V W : Set (GenericSquare a)} (hV : ResolvedBy (fun i => (U i).val) V)
    (h : Disjoint V W) : Disjoint (resolvedPolygonMask U V) (resolvedPolygonMask U W) := by
  apply Set.disjoint_left.mpr
  rintro ω ⟨x,hx,hxV⟩ ⟨y,hy,hyW⟩
  have hyV := (hV x y ((polygonAssignment_eq_iff U x y).mp (hx.trans hy.symm))).mp hxV
  exact Set.disjoint_left.mp h hyV hyW

theorem resolvedPolygonMask_union (U : ι → polygonAlgebra a)
    (V W : Set (GenericSquare a)) :
    resolvedPolygonMask U (V ∪ W) = resolvedPolygonMask U V ∪ resolvedPolygonMask U W := by
  ext ω
  constructor
  · rintro ⟨x,he,hx | hx⟩
    · exact Or.inl ⟨x,he,hx⟩
    · exact Or.inr ⟨x,he,hx⟩
  · rintro (⟨x,he,hx⟩ | ⟨x,he,hx⟩)
    · exact ⟨x,he,Or.inl hx⟩
    · exact ⟨x,he,Or.inr hx⟩

end ResolvedBoolean

section FiniteCoordinateAlgebra

@[simp] theorem coordinateShift_add (j : Fin 2) (u v : CutRing) :
    coordinateShift j (u+v) = coordinateShift j u + coordinateShift j v := by
  fin_cases j <;> simp [coordinateShift]

@[simp] theorem coordinateShift_neg (j : Fin 2) (u : CutRing) :
    coordinateShift j (-u) = -coordinateShift j u := by
  fin_cases j <;> simp [coordinateShift]

theorem coordinateArc_tau {a : ℕ} (j : Fin 2) :
    coordinateArc a j cutTau = (coordinatePrimitive a j).val := by
  have hfloor : ⌊Real.goldenRatio⌋ = (1 : ℤ) :=
    Int.floor_eq_iff.mpr ⟨by norm_num; exact Real.one_lt_goldenRatio.le,
      by norm_num; exact Real.goldenRatio_lt_two⟩
  ext p
  have hp := (coordinate_bounds j p).1
  fin_cases j <;>
    simp [coordinateArc,coordinate,coordinatePrimitive,halfPlane,cutForm,
      Int.fract,hfloor,ordinary_cutTau] <;> intro _ <;> exact hp

theorem coordinate_preimage_add {a : ℕ} (j : Fin 2) (u v : CutRing)
    (V : Set (GenericSquare a)) :
    translate a (-coordinateShift j u) ⁻¹' (translate a (-coordinateShift j v) ⁻¹' V) =
      translate a (-coordinateShift j (u+v)) ⁻¹' V := by
  ext p
  simp only [Set.mem_preimage,coordinateShift_add,neg_add_rev,translate_add]

noncomputable def coordinateBetween (a : ℕ) (j : Fin 2) (u v : CutRing) :
    Set (GenericSquare a) :=
  translate a (-coordinateShift j u) ⁻¹' coordinateArc a j (v-u)

theorem coordinate_prefix_generated {a : ℕ}
    (B : BooleanSubalgebra (Set (GenericSquare a))) (j : Fin 2) (u : CutRing)
    (n : ℕ)
    (h : ∀ i : ℕ, i < n →
      (spatialTranslate (coordinateShift j (u+(i:CutRing)*cutTau))
        (coordinatePrimitive a j)).val ∈ B) :
    coordinateBetween a j u (u+(n:CutRing)*cutTau) ∈ B := by
  have hs {V W : Set (GenericSquare a)} (hV : V ∈ B) (hW : W ∈ B) : symmDiff V W ∈ B := by
    rw [Set.symmDiff_def]
    exact BooleanSubalgebra.sup_mem (BooleanSubalgebra.sdiff_mem hV hW)
      (BooleanSubalgebra.sdiff_mem hW hV)
  change translate a (-coordinateShift j u) ⁻¹' coordinateArc a j
      (u+(n:CutRing)*cutTau-u) ∈ B
  rw [add_sub_cancel_left]
  induction n with
  | zero =>
    rw [Nat.cast_zero,zero_mul,coordinateArc_zero_of_fract j 0 (by simp),Set.preimage_empty]
    exact BooleanSubalgebra.bot_mem
  | succ n ih =>
    have hi := ih (fun i hi => h i (by omega))
    rw [Nat.cast_succ,add_mul,one_mul,coordinateArc_add]
    have he := h n (by omega)
    change translate a (-coordinateShift j (u+(n:CutRing)*cutTau)) ⁻¹'
      (coordinatePrimitive a j).val ∈ B at he
    split_ifs
    · rw [Set.preimage_symmDiff,coordinateShift_neg,coordinate_preimage_add,
        coordinateArc_tau]
      exact hs hi he
    · rw [Set.preimage_compl,Set.preimage_symmDiff,coordinateShift_neg,
        coordinate_preimage_add,coordinateArc_tau]
      exact BooleanSubalgebra.compl_mem (hs hi he)

end FiniteCoordinateAlgebra

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GeometricSectors
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
section GeometricSectors

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {ι : Type*} [Finite ι]

theorem actualPolygonTableHom_resolved (U : ι → polygonAlgebra a)
    (V : polygonAlgebra a) (hV : ResolvedBy (fun i => (U i).val) V.val)
    (s : alternatingGroup (Fin (m+1))) :
    actualPolygonTableHom U (sectorMask (resolvedPolygonMask U V.val) s) =
      conditionalAlternatingHom V s := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [actualPolygonTableHom_apply]
  change ((sectorMask (resolvedPolygonMask U V.val) s
      ⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩).val p.1,p.2) = conditionalPerm V s.val p
  rw [conditionalPerm_apply]
  by_cases hp : p.2 ∈ V.val
  · rw [sectorMask_of_mem _ _ _ ((resolvedPolygonMask_mem U V.val hV p.2).mpr hp),ite_eq_left hp]
  · rw [sectorMask_of_not_mem _ _ _ (fun h => hp ((resolvedPolygonMask_mem U V.val hV p.2).mp h)),ite_eq_right hp]
    rfl

theorem actualAlphabetTableHom_resolved (I : Finset (Fin (m+1)))
    (U : ι → polygonAlgebra a) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (U i).val) V.val) :
    (actualAlphabetTableHom I U).comp (sectorMask (resolvedPolygonMask U V.val)) =
      (conditionalAlternatingHom V).comp (subtypeAlternatingHom I) := by
  apply MonoidHom.ext
  intro s
  change actualPolygonTableHom U (tableAlphabetHom I (sectorMask _ s)) = _
  rw [tableAlphabetHom_mask]
  exact actualPolygonTableHom_resolved U V hV (subtypeAlternatingHom I s)

namespace InitialCoverSystem

variable (B : InitialCoverSystem a r m hm M)

noncomputable def geometricSector (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup I) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.primitiveTable I b hb P h).sector (resolvedPolygonMask (primitiveTests (r := r) P) V.val)

theorem geometricSector_projection (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.geometricSector I b hb P h V) =
      ((conditionalAlternatingHom V).comp (subtypeAlternatingHom I)).comp
        (universalProjection (alternatingGroup I)) := by
  unfold geometricSector
  rw [ActualLawfulTable.sector_projection,actualAlphabetTableHom_resolved I _ V hV]

theorem geometricSector_mem (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup I)) :
    B.geometricSector I b hb P h V s ∈ (copyFamilyEval (B.primitiveFamily I b hb P)).range :=
  (B.primitiveTable I b hb P h).sector_mem _ s

omit [Finite ι] in

theorem primitiveFamily_range_reindex {κ : Type*} (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) (v : κ → ι) :
    (copyFamilyEval (B.primitiveFamily I b hb (P ∘ v))).range ≤
      (copyFamilyEval (B.primitiveFamily I b hb P)).range := by
  rw [copyFamilyEval_range,copyFamilyEval_range]
  apply iSup_le
  intro i
  cases i with
  | none => exact le_iSup (fun z => (B.primitiveFamily I b hb P z).range) none
  | some j => exact le_iSup (fun z => (B.primitiveFamily I b hb P z).range) (some (v j))

theorem geometricSector_reindex {κ : Type*} [Finite κ] (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) (v : κ → ι)
    (h : B.PrimitiveFamilyLaw I b hb P) (g : B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (P ∘ v) i).val) V.val) :
    B.geometricSector I b hb (P ∘ v) g V = B.geometricSector I b hb P h V := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb P)).range h
  · rintro x ⟨s,rfl⟩
    exact B.primitiveFamily_range_reindex I b hb P v
      (B.geometricSector_mem I b hb (P ∘ v) g V s)
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb P h V s
  · have hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val := by
      intro x y he
      exact hV x y (fun j => he (v j))
    rw [B.geometricSector_projection I b hb (P ∘ v) g V hV,
      B.geometricSector_projection I b hb P h V hV']

end InitialCoverSystem
end GeometricSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorControl
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

section AlphabetInclusion

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace CommonFrame
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {I J : Finset (Fin (m+1))} {u : CutRing × CutRing}

noncomputable def restrict (F : CommonFrame a r m hm J u) (hIJ : I ⊆ J) :
    CommonFrame a r m hm I u where
  k := F.k
  d := F.d
  projection := F.projection
  common := fun i hi => F.common i (hIJ hi)

end CommonFrame

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem initialAlphabet_inclusion {I J : Finset (Fin (m+1))} (hIJ : I ⊆ J) (j : Fin 5) :
    (B.initialAlphabet J j).comp (subalphabetHom hIJ) = B.initialAlphabet I j := by
  rw [initialAlphabet,MonoidHom.comp_assoc,subtypeAlternatingHom_comp]
  rfl

theorem primitiveCopy_inclusion {I J : Finset (Fin (m+1))} (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J) (p : Fin 5 × (CutRing × CutRing)) :
    (B.primitiveCopy J c hc p).comp (subalphabetHom hIJ) = B.primitiveCopy I b hb p := by
  let F := commonFrame a r m hm J c hc p.2
  rw [B.primitiveCopy_frame J c hc p F,B.primitiveCopy_frame I b hb p (F.restrict hIJ)]
  change ((MulAut.conj (B.t F.k)).toMonoidHom.comp (B.initialAlphabet J p.1)).comp _ =
    (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.initialAlphabet I p.1)
  rw [MonoidHom.comp_assoc,B.initialAlphabet_inclusion hIJ]

theorem primitiveFamily_inclusion {ι : Type*} {I J : Finset (Fin (m+1))} (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J)
    (P : ι → Fin 5 × (CutRing × CutRing)) (i : Option ι) :
    (B.primitiveFamily J c hc P i).comp (subalphabetHom hIJ) = B.primitiveFamily I b hb P i := by
  cases i with
  | none => exact B.initialAlphabet_inclusion hIJ 0
  | some i => exact B.primitiveCopy_inclusion hIJ b c hb hc (P i)

end InitialCoverSystem
end AlphabetInclusion

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
section WindowIntervals

@[simp] theorem coordinateShift_sub (j : Fin 2) (u v : CutRing) :
    coordinateShift j (u-v) = coordinateShift j u-coordinateShift j v := by
  rw [sub_eq_add_neg,coordinateShift_add,coordinateShift_neg,sub_eq_add_neg]

theorem coordinateBetween_reverse {a : ℕ} (j : Fin 2) (u v : CutRing)
    (h : Int.fract (ordinary (v-u)) ≠ 0) :
    coordinateBetween a j v u = (coordinateBetween a j u v)ᶜ := by
  unfold coordinateBetween
  rw [show u-v = -(v-u) by ring,coordinateArc_neg j (v-u) h,Set.preimage_compl]
  congr 1
  ext p
  simp only [Set.mem_preimage]
  rw [← translate_add]
  rw [coordinateShift_sub]
  abel_nf

theorem coordinateBetween_empty {a : ℕ} (j : Fin 2) (u v : CutRing)
    (h : Int.fract (ordinary (v-u)) = 0) : coordinateBetween a j u v = ∅ := by
  rw [coordinateBetween,coordinateArc_zero_of_fract j _ h,Set.preimage_empty]

theorem coordinateBetween_period {a : ℕ} (j : Fin 2) (u v : CutRing) (p q : ℤ) :
    coordinateBetween a j (u+p) (v+q) = coordinateBetween a j u v := by
  unfold coordinateBetween
  have he : coordinateArc a j (v+q-(u+p)) = coordinateArc a j (v-u) := by
    ext x
    simp only [coordinateArc,Set.mem_ofPred_eq,map_sub,map_add,map_intCast]
    rw [show ordinary v+(q:ℝ)-(ordinary u+(p:ℝ)) = ordinary v-ordinary u+((q-p:ℤ):ℝ) by push_cast; ring]
    rw [Int.fract_add_intCast]
  rw [he]
  ext x
  simp only [Set.mem_preimage]
  have ht : translate a (-coordinateShift j (u+p)) x = translate a (-coordinateShift j u) x := by
    change translation a (-coordinateShift j (u+p)) x = translation a (-coordinateShift j u) x
    fin_cases j
    · have hp := DFunLike.congr_fun (translation_period a (-u,0) (-p,0)) x
      simpa [coordinateShift,add_comm] using hp
    · have hp := DFunLike.congr_fun (translation_period a (0,-u) (0,-p)) x
      simpa [coordinateShift,add_comm] using hp
  rw [ht]

end WindowIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SmallFamilyWords
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
section SmallFamilyWords

variable {α ι Ω H : Type*} [Fintype α] [DecidableEq α] [Group H]

theorem alphabetAssignment_mask (I : Finset α) (U : ι → Set Ω) (i : Option ι) :
    (alphabetAssignment I).comp (maskFamily U i) =
      (maskFamily U i).comp (subtypeAlternatingHom I) := by
  classical
  ext s ω
  cases i with
  | none => simp [alphabetAssignment,maskFamily,sectorMask]
  | some i => by_cases h : ω ∈ U i <;> simp [alphabetAssignment,maskFamily,sectorMask,h]

noncomputable def smallFamilyModel (U : ι → Set Ω) :
    SmallFamilyWord α ι →* (Ω → alternatingGroup α) :=
  smallFamilyEval (fun I i => (maskFamily U i).comp (subtypeAlternatingHom I.val))

theorem smallFamilyModel_support (U : ι → Set Ω) (S : Finset α)
    (w : SmallFamilyWord α ι) (hw : w ∈ smallFamilyLocal S) :
    ∀ ω, ((smallFamilyModel U w) ω).val.support ⊆ S := by
  apply (alphabetAssignment_range S _).mp
  have hh : smallFamilyLocal (ι := ι) S ≤
      ((alphabetAssignment (Ω := Ω) S).range).comap (smallFamilyModel U) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨l,hl,rfl⟩
    apply (alphabetAssignment_range S _).mpr
    intro ω
    classical
    have hs := (subtypeAlternatingHom_mem_range l.1.val _).mp ⟨l.2.2,rfl⟩
    change ((maskFamily U l.2.1 (subtypeAlternatingHom l.1.val l.2.2)) ω).val.support ⊆ S
    cases l.2.1 with
    | none => simpa [maskFamily,sectorMask] using hs.trans hl
    | some i =>
      by_cases h : ω ∈ U i
      · simpa [maskFamily,sectorMask,h] using hs.trans hl
      · simp [maskFamily,sectorMask,h]
  exact hh hw

end SmallFamilyWords

section SmallFamilyComplete
variable {α ι Ω H : Type*} [Fintype α] [DecidableEq α] [Group H]

theorem smallFamilyModel_mask_mem (U : ι → Set Ω) (S : Finset α) (hS : 5 ≤ S.card)
    (i : Option ι) (s : alternatingGroup S) :
    maskFamily U i (subtypeAlternatingHom S s) ∈
      (smallFamilyLocal S).map (smallFamilyModel U) := by
  let K := ((smallFamilyLocal S).map (smallFamilyModel U)).comap
    ((maskFamily U i).comp (subtypeAlternatingHom S))
  have hK : K = ⊤ := by
    apply top_unique
    rw [← subalphabet_five_generate S hS]
    apply iSup_le
    intro I x hx
    obtain ⟨t,rfl⟩ := hx
    let I' : FiveAlphabet α := ⟨I.val,Finset.subset_univ _,I.property.2⟩
    refine ⟨FreeGroup.of ⟨I',i,t⟩,smallFamilyLocal_of _ I.property.1,?_⟩
    change maskFamily U i (subtypeAlternatingHom I.val t) =
      maskFamily U i (subtypeAlternatingHom S (subalphabetHom I.property.1 t))
    exact congrArg (maskFamily U i)
      (DFunLike.congr_fun (subtypeAlternatingHom_comp I.property.1) t).symm
  exact (show s ∈ K from hK ▸ Subgroup.mem_top s)

theorem smallFamilyModel_complete [Finite ι] [Finite Ω]
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (S : Finset α) (hS : 5 ≤ S.card) (g : Ω → alternatingGroup α)
    (hg : ∀ ω, (g ω).val.support ⊆ S) :
    ∃ w ∈ smallFamilyLocal S, smallFamilyModel U w = g := by
  let : Group.IsPerfect (alternatingGroup S) := alphabetPerfect S hS
  obtain ⟨t,ht⟩ := (alphabetAssignment_range S g).mpr hg
  let K := ((smallFamilyLocal S).map (smallFamilyModel U)).comap (alphabetAssignment S)
  have hm (i : Option ι) (s : alternatingGroup S) : maskFamily U i s ∈ K := by
    change alphabetAssignment S (maskFamily U i s) ∈
      (smallFamilyLocal S).map (smallFamilyModel U)
    rw [← MonoidHom.comp_apply,alphabetAssignment_mask]
    exact smallFamilyModel_mask_mem U S hS i s
  have hK : K = ⊤ := assignment_group_generated U hsep K (hm none) (fun i => hm (some i))
  have htK : t ∈ K := hK ▸ Subgroup.mem_top t
  change alphabetAssignment S t ∈ (smallFamilyLocal S).map (smallFamilyModel U) at htK
  rwa [ht] at htK

end SmallFamilyComplete

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SmallFamilyGlobal
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
section SmallFamilyGlobal

variable {D H Q T : Type*} [Group D] [Group H] [Group Q] [Group T]

theorem centralOn_range_iff_hasCentralLaw (q : H →* Q) (e : D →* H)
    (v : D →* T) (ρ : T →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) :
    CentralOn q e.range ↔ HasCentralLaw v e.rangeRestrict := by
  have hk (w : D) : q (e w) = 1 ↔ v w = 1 := by
    have hh := DFunLike.congr_fun he w
    change q (e w) = ρ (v w) at hh
    rw [hh,← map_one ρ]
    exact hρ.eq_iff
  rw [hasCentralLaw_iff]
  constructor
  · intro h w hw
    exact h ((hk w).mpr hw)
  · intro h x hx
    obtain ⟨w,hw⟩ := x.property
    have hx' : q (e w) = 1 := by
      change q x.val = 1 at hx
      simpa only [hw] using hx
    have ht := h w ((hk w).mp hx')
    have heq : e.rangeRestrict w = x := Subtype.ext hw
    rwa [heq] at ht

variable {α ι Ω : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω]

theorem smallFamily_centralOn
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (q : H →* Q) (ρ : (Ω → alternatingGroup α) →* Q) (hρ : Function.Injective ρ)
    (hproj : ∀ I i, q.comp (F I i) =
      ρ.comp ((maskFamily U i).comp (subtypeAlternatingHom I.val)))
    (K : Finset α → Subgroup H)
    (hlaw : ∀ S, S.card ≤ 15 → CentralOn q (K S))
    (hcontain : ∀ S, S.card ≤ 15 → ∀ I, I.val ⊆ S → ∀ i, (F I i).range ≤ K S)
    (hα : 5 ≤ Fintype.card α) : CentralOn q (smallFamilyEval F).range := by
  classical
  let e := smallFamilyEval F
  let v := smallFamilyModel (α := α) U
  have he : q.comp e = ρ.comp v := by
    apply FreeGroup.ext_hom
    rintro ⟨I,i,s⟩
    simpa only [e,v,MonoidHom.comp_apply,smallFamilyModel,smallFamilyEval_of] using
      DFunLike.congr_fun (hproj I i) s
  apply (centralOn_range_iff_hasCentralLaw q e v ρ hρ he).mpr
  let : Group.IsPerfect e.range := smallFamilyEval_perfect F
  obtain ⟨E,_hEsub,hE⟩ := Finset.exists_subset_card_eq (show 5 ≤ (Finset.univ : Finset α).card by simpa using hα)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < E.card by omega)
  obtain ⟨y,hy,hyx⟩ := Finset.exists_mem_ne (show 1 < E.card by omega) x
  let a : SwapLabel α := ⟨Equiv.swap x y,x,y,Ne.symm hyx,rfl⟩
  have ha : a.val.support ⊆ E := by
    change (Equiv.swap x y).support ⊆ E
    rw [Equiv.Perm.support_swap (Ne.symm hyx)]
    exact Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩
  refine small_support_assignment_law (smallFamilyLocal (ι := ι)) smallFamilyLocal_mono
    v e.rangeRestrict e.rangeRestrict_surjective smallFamilyLocal_generate
    (smallFamilyModel_support U) ?_ E hE a ha ?_
  · intro S hS d hd hv z hz
    apply Commute.of_map (f := e.range.subtype) Subtype.val_injective
    have hle := smallFamilyLocal_map_le F S (K S) (hcontain S hS)
    apply (centralOn_iff q (K S)).mp (hlaw S hS) (e d) (hle ⟨d,hd,rfl⟩)
    · have hh := DFunLike.congr_fun he d
      change q (e d) = ρ (v d) at hh
      rw [hh,hv,map_one]
    · exact hle ⟨z,hz,rfl⟩
  · intro S hS _ g hg
    exact smallFamilyModel_complete U hsep S hS g hg

end SmallFamilyGlobal

section GlobalPrimitiveTable

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]

noncomputable def smallPrimitiveInputs (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (I : FiveAlphabet (Fin (m+1))) :
    Option ι → alternatingGroup I.val →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.primitiveFamily I.val (smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega))
    (smallAlphabetBalance_notMem hlarge I.val (by rw [I.property.2]; omega)) P

noncomputable def smallPrimitiveCarrier (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (S : Finset (Fin (m+1))) :
    Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  if hS : S.card ≤ 15 then
    (copyFamilyEval (B.primitiveFamily S (smallAlphabetBalance hlarge S hS)
      (smallAlphabetBalance_notMem hlarge S hS) P)).range
  else ⊥

theorem smallPrimitiveInputs_projection (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (I : FiveAlphabet (Fin (m+1))) (i : Option ι) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.smallPrimitiveInputs hlarge P I i) =
    (actualPolygonTableHom (primitiveTests (a := a) (r := r) P)).comp
      ((maskFamily (actualTestMask (primitiveTests (a := a) (r := r) P)) i).comp
        (subtypeAlternatingHom I.val)) := by
  rw [smallPrimitiveInputs,B.primitiveFamily_projection]
  have he := actualAlphabetTableHom_masks I.val (primitiveTests (a := a) (r := r) P) i
  change ((actualPolygonTableHom _).comp (alphabetAssignment I.val)).comp _ = _ at he
  rw [MonoidHom.comp_assoc,alphabetAssignment_mask] at he
  exact he.symm

omit [Finite ι] in
theorem smallPrimitiveInputs_local (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (S : Finset (Fin (m+1))) (hS : S.card ≤ 15)
    (I : FiveAlphabet (Fin (m+1))) (hIS : I.val ⊆ S) (i : Option ι) :
    (B.smallPrimitiveInputs hlarge P I i).range ≤ B.smallPrimitiveCarrier hlarge P S := by
  rw [smallPrimitiveCarrier,dite_eq_left hS]
  rintro x ⟨s,rfl⟩
  rw [copyFamilyEval_range]
  apply le_iSup (fun j => (B.primitiveFamily S (smallAlphabetBalance hlarge S hS)
    (smallAlphabetBalance_notMem hlarge S hS) P j).range) i
  refine ⟨subalphabetHom hIS s,?_⟩
  exact DFunLike.congr_fun (B.primitiveFamily_inclusion hIS _ _ _ _ P i) s

theorem fullPrimitiveFamily_central (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  apply smallFamily_centralOn (actualTestMask (primitiveTests (a := a) (r := r) P))
    (actualTestMask_separates _) (B.smallPrimitiveInputs hlarge P) _
    (actualPolygonTableHom _) (actualPolygonTableHom_injective _)
    (B.smallPrimitiveInputs_projection hlarge P) (B.smallPrimitiveCarrier hlarge P) ?_
    (B.smallPrimitiveInputs_local hlarge P) (by simpa using (by omega : 5 ≤ m+1))
  intro S hS
  rw [smallPrimitiveCarrier,dite_eq_left hS]
  exact h S hS _ _

end InitialCoverSystem
end GlobalPrimitiveTable

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_EvaluationTable
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
section EvaluationTable
variable {D H Q T : Type*} [Group D] [Group H] [Group Q] [Group T]

noncomputable def evaluationTable {Ω E : Type*} [Group E]
    (q : H →* Q) (e : D →* H) (v : D →* (Ω → E))
    (ρ : (Ω → E) →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) (hv : Function.Surjective v)
    (h : CentralOn q e.range) : ActualLawfulTable q ρ where
  carrier := e.range
  law := h
  model := evaluationModel q e v ρ hρ he
  onto := by
    intro s
    obtain ⟨w,rfl⟩ := hv s
    exact ⟨e.rangeRestrict w,DFunLike.congr_fun (evaluationModel_comp q e v ρ hρ he) w⟩
  projection := evaluationModel_projection q e v ρ hρ he

end EvaluationTable

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
section FullAlphabetGeneration
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem universal_five_alphabet_generate [Group.IsPerfect (alternatingGroup α)]
    (hα : 5 ≤ Fintype.card α) :
    (⨆ I : FiveAlphabet α, (universalMap (subtypeAlternatingHom I.val)).range) = ⊤ :=
  universal_generating_ranges (fun I : FiveAlphabet α => subtypeAlternatingHom I.val)
    (five_alphabet_generate hα)

end FullAlphabetGeneration

section FullPrimitiveSectors

variable {α ι Ω : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω]

theorem smallFamilyModel_surjective (U : ι → Set Ω)
    (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (hα : 5 ≤ Fintype.card α) : Function.Surjective (smallFamilyModel (α := α) U) := by
  intro g
  obtain ⟨w,_,hw⟩ := smallFamilyModel_complete U hsep Finset.univ (by simpa using hα) g
    (fun ω => Finset.subset_univ _)
  exact ⟨w,hw⟩

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem fullPrimitiveProjection (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) :
    (coverMap M (alternatingGenerator a r m hm)).comp
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)) =
    (actualPolygonTableHom (primitiveTests (a := a) (r := r) P)).comp
      (smallFamilyModel (actualTestMask (primitiveTests (a := a) (r := r) P))) := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  simpa only [MonoidHom.comp_apply,smallFamilyModel,smallFamilyEval_of] using
    DFunLike.congr_fun (B.smallPrimitiveInputs_projection hlarge P I i) s

noncomputable def fullPrimitiveTable (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    ActualLawfulTable (coverMap M (alternatingGenerator a r m hm))
      (actualPolygonTableHom (primitiveTests (a := a) (r := r) P)) :=
  evaluationTable _ (smallFamilyEval (B.smallPrimitiveInputs hlarge P))
    (smallFamilyModel _) (actualPolygonTableHom _) (actualPolygonTableHom_injective _)
    (B.fullPrimitiveProjection hlarge P)
    (smallFamilyModel_surjective _ (actualTestMask_separates _)
      (by simpa using (by omega : 5 ≤ m+1)))
    (B.fullPrimitiveFamily_central hlarge P h)

omit [Finite ι] in

theorem primitiveFamily_range_full (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (J : Finset (Fin (m+1))) (hJ : 5 ≤ J.card) (b : Fin (m+1)) (hb : b ∉ J) :
    (copyFamilyEval (B.primitiveFamily J b hb P)).range ≤
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  rw [copyFamilyEval_range]
  apply iSup_le
  intro i
  rw [MonoidHom.range_eq_map,← subalphabet_five_generate J hJ,Subgroup.map_iSup]
  apply iSup_le
  intro I
  rw [← MonoidHom.range_comp]
  rintro x ⟨t,rfl⟩
  let I' : FiveAlphabet (Fin (m+1)) := ⟨I.val,Finset.subset_univ _,I.property.2⟩
  refine ⟨FreeGroup.of ⟨I',i,t⟩,?_⟩
  rw [smallFamilyEval_of]
  exact (DFunLike.congr_fun (B.primitiveFamily_inclusion I.property.1 _ _ _ _ P i) t).symm

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

noncomputable def fullGeometricSector (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a) : UniversalExtension (alternatingGroup (Fin (m+1))) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.fullPrimitiveTable hlarge P h).sector
    (resolvedPolygonMask (primitiveTests (a := a) (r := r) P) V.val)

theorem fullGeometricSector_projection (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.fullGeometricSector hlarge P h V) =
      (conditionalAlternatingHom V).comp (universalProjection (alternatingGroup (Fin (m+1)))) := by
  rw [fullGeometricSector,ActualLawfulTable.sector_projection]
  congr 1
  ext s : 1
  exact actualPolygonTableHom_resolved _ V hV s

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

theorem fullGeometricSector_mem (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup (Fin (m+1)))) :
    B.fullGeometricSector hlarge P h V s ∈
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range :=
  (B.fullPrimitiveTable hlarge P h).sector_mem _ s

theorem fullGeometricSector_inclusion (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (g : B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (B.fullGeometricSector hlarge P h V).comp (universalMap (subtypeAlternatingHom I)) =
      B.geometricSector I b hb P g V := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range
    (B.fullPrimitiveFamily_central hlarge P h)
  · rintro x ⟨s,rfl⟩
    exact B.fullGeometricSector_mem hlarge P h V _
  · rintro x ⟨s,rfl⟩
    exact B.primitiveFamily_range_full hlarge P I hI b hb
      (B.geometricSector_mem I b hb P g V s)
  · rw [← MonoidHom.comp_assoc,B.fullGeometricSector_projection hlarge P h V hV,
      B.geometricSector_projection I b hb P g V hV,MonoidHom.comp_assoc,universalMap_spec,
      MonoidHom.comp_assoc]

end InitialCoverSystem
end FullSectorCompatibility

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SmallControlCalculus
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
section SmallControlCalculus
variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

abbrev TrackStar (α : Type*) [Fintype α] [DecidableEq α] :=
  UniversalExtension (alternatingGroup α)

def SmallControlled (c : alternatingGroup α →* H) (f g : TrackStar α →* H) : Prop :=
  ∀ I : ControlAlphabet α,
    SameActionOn (g.comp (universalMap (subtypeAlternatingHom I.val)))
      ((c.comp (universalProjection (alternatingGroup α))).comp
        (universalMap (subtypeAlternatingHom I.val))) f.range

end SmallControlCalculus

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowSubfamilies
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
section WindowSubfamilies

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem geometricSector_subfamily {ι κ : Type*} [Finite ι] [Finite κ]
    (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (v : κ → ι) (hv : P ∘ v = Q)
    (h : B.PrimitiveFamilyLaw I b hb P) (g : B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val) :
    B.geometricSector I b hb Q g V = B.geometricSector I b hb P h V := by
  subst Q
  exact B.geometricSector_reindex I b hb P v h g V hV

end InitialCoverSystem
end WindowSubfamilies

section CircularIntervals

theorem coordinateArc_mem (a : ℕ) (j : Fin 2) (z : CutRing) :
    coordinateArc a j z ∈ polygonAlgebra a := by
  have he : coordinateArc a j z = halfPlane a (Fin.castLE (by omega) j)
      (z-(⌊ordinary z⌋:ℤ)) := by
    ext p
    have hc : cutForm a (Fin.castLE (by omega) j) p.val = coordinate j p := by
      fin_cases j <;> rfl
    simp only [coordinateArc,halfPlane,Set.mem_ofPred_eq,hc,map_sub,map_intCast]
    rfl
  rw [he]
  exact halfPlane_mem _ _ _

theorem coordinateBetween_mem (a : ℕ) (j : Fin 2) (u v : CutRing) :
    coordinateBetween a j u v ∈ polygonAlgebra a :=
  polygon_preimage_translate (-coordinateShift j u) (coordinateArc_mem a j (v-u))

noncomputable def coordinateInterval (a : ℕ) (j : Fin 2) (u v : CutRing) : polygonAlgebra a :=
  ⟨coordinateBetween a j u v,coordinateBetween_mem a j u v⟩

theorem mem_coordinateBetween_iff {a : ℕ} (j : Fin 2) (u v : CutRing)
    (h₀ : ordinary u ≤ ordinary v) (h₁ : ordinary v-ordinary u < 1)
    (p : GenericSquare a) :
    p ∈ coordinateBetween a j u v ↔
      ∃ k : ℤ, ordinary u ≤ coordinate j p+(k:ℝ) ∧ coordinate j p+(k:ℝ) < ordinary v := by
  change coordinate j (translate a (-coordinateShift j u) p) < Int.fract (ordinary (v-u)) ↔ _
  rw [← coordinateShift_neg,coordinate_translate,map_neg,map_sub,
    Int.fract_eq_self.mpr ⟨sub_nonneg.mpr h₀,h₁⟩]
  change Int.fract (coordinate j p-ordinary u) < ordinary v-ordinary u ↔ _
  constructor
  · intro h
    refine ⟨-⌊coordinate j p-ordinary u⌋,?_,?_⟩
    · have hn := Int.fract_nonneg (coordinate j p-ordinary u)
      simp only [Int.fract,Int.cast_neg] at *
      linarith
    · simp only [Int.fract,Int.cast_neg] at *
      linarith
  · rintro ⟨k,hk₀,hk₁⟩
    have he : Int.fract (coordinate j p-ordinary u+(k:ℝ)) =
        coordinate j p-ordinary u+(k:ℝ) :=
      Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩
    rw [Int.fract_add_intCast] at he
    rw [he]
    linarith

theorem coordinateInterval_disjoint {a : ℕ} (j : Fin 2) (u v w z : CutRing)
    (huv : ordinary u ≤ ordinary v) (hvw : ordinary v ≤ ordinary w)
    (hwz : ordinary w ≤ ordinary z) (hlen : ordinary z-ordinary u < 1) :
    Disjoint (coordinateInterval a j u v).val (coordinateInterval a j w z).val := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  obtain ⟨k,hk₀,hk₁⟩ := (mem_coordinateBetween_iff j u v huv (by linarith) p).mp hp
  obtain ⟨l,hl₀,hl₁⟩ := (mem_coordinateBetween_iff j w z hwz (by linarith) p).mp hq
  have hk : (k:ℝ)-(l:ℝ) < 1 := by linarith
  have hl : (l:ℝ)-(k:ℝ) < 1 := by linarith
  have hk' : k-l < (1:ℤ) := by exact_mod_cast hk
  have hl' : l-k < (1:ℤ) := by exact_mod_cast hl
  have he : k = l := by omega
  subst l
  linarith

end CircularIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullSector
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

section FullWindowCoherence

variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem universal_five_alphabet_hom_ext (hα : 5 ≤ Fintype.card α)
    (f g : UniversalExtension (alternatingGroup α) →* H)
    (h : ∀ I : FiveAlphabet α, f.comp (universalMap (subtypeAlternatingHom I.val)) =
      g.comp (universalMap (subtypeAlternatingHom I.val))) : f = g := by
  have he : (⊤ : Subgroup (UniversalExtension (alternatingGroup α))) ≤ f.eqLocus g := by
    rw [← universal_five_alphabet_generate hα]
    apply iSup_le
    intro I x hx
    obtain ⟨s,rfl⟩ := hx
    exact DFunLike.congr_fun (h I) s
  ext s
  exact he (Subgroup.mem_top s)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_subfamily (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (v : κ → ι) (hv : P ∘ v = Q)
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val) :
    B.fullGeometricSector hlarge Q g V = B.fullGeometricSector hlarge P h V := by
  apply universal_five_alphabet_hom_ext (by simp; omega)
  intro I
  let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
  have hb : b ∉ I.val := smallAlphabetBalance_notMem hlarge I.val _
  have hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val := by
    subst Q
    intro x y he
    exact hV x y (fun i => he (v i))
  rw [B.fullGeometricSector_inclusion hlarge Q g I.val (by rw [I.property.2]) b hb
      (g _ (by rw [I.property.2]; omega) b hb) V hV,
    B.fullGeometricSector_inclusion hlarge P h I.val (by rw [I.property.2]) b hb
      (h _ (by rw [I.property.2]; omega) b hb) V hV']
  exact B.geometricSector_subfamily I.val b hb P Q v hv _ _ V hV

noncomputable def windowSector (hlarge : 15 < m+1) (n : ℕ)
    (h : B.CoordinateWindowLaw n) (q : Fin 2 → ℤ) (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup (Fin (m+1))) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (coordinateWindowPrimitives n q) (fun I _ b hb => h I b hb q) V

end InitialCoverSystem
end FullWindowCoherence

section AxisWindows

noncomputable def axisWindowPrimitives (j : Fin 2) (k : ℕ) (p : ℤ) :
    Fin (k-1) → Fin 5 × (CutRing × CutRing) := fun i =>
  (coordinateTestIndex j,coordinateShift j (((p+(i.val:ℤ)):CutRing)*cutTau))

theorem axisInterval_resolved {a : ℕ} {r : CutRing} (j : Fin 2) (k : ℕ) (p : ℤ)
    (u v : CutRing) (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) i).val) (coordinateInterval a j u v).val := by
  let A := resolvedAlgebra (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
    (axisWindowPrimitives j k p) i).val)
  have hbetween (s t : ℕ) (hst : s ≤ t) (ht : t < k) :
      coordinateBetween a j (((p+(s:ℤ)):CutRing)*cutTau)
        (((p+(t:ℤ)):CutRing)*cutTau) ∈ A := by
    have hh := coordinate_prefix_generated A j (((p+(s:ℤ)):CutRing)*cutTau) (t-s)
    have he : (((p+(s:ℤ)):CutRing)*cutTau)+((t-s:ℕ):CutRing)*cutTau =
        (((p+(t:ℤ)):CutRing)*cutTau) := by
      push_cast
      rw [Nat.cast_sub hst]
      ring
    rw [he] at hh
    apply hh
    intro i hi
    have hi' : s+i < k-1 := by omega
    have hh := resolved_test (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) z).val) ⟨s+i,hi'⟩
    change (spatialTranslate (coordinateShift j (((p+((s+i:ℕ):ℤ)):CutRing)*cutTau))
      (initialTest a r (coordinateTestIndex j))).val ∈ A at hh
    rw [initialTest_coordinate] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 3
    push_cast
    ring
  have hall (s t : ℕ) (hs : s < k) (ht : t < k) :
      coordinateBetween a j (((p+(s:ℤ)):CutRing)*cutTau)
        (((p+(t:ℤ)):CutRing)*cutTau) ∈ A := by
    by_cases hst : s ≤ t
    · exact hbetween s t hst ht
    · let u' : CutRing := ((p+(s:ℤ)):CutRing)*cutTau
      let v' : CutRing := ((p+(t:ℤ)):CutRing)*cutTau
      by_cases he : Int.fract (ordinary (v'-u')) = 0
      · rw [coordinateBetween_empty j u' v' he]
        exact BooleanSubalgebra.bot_mem
      · have hh := hbetween t s (by omega) hs
        rw [coordinateBetween_reverse j u' v' he] at hh
        simpa only [compl_compl] using BooleanSubalgebra.compl_mem hh
  let s := (endpointLabel u-p).toNat
  let t := (endpointLabel v-p).toNat
  have hs : (s:ℤ) = endpointLabel u-p := Int.toNat_of_nonneg (by omega)
  have ht : (t:ℤ) = endpointLabel v-p := Int.toNat_of_nonneg (by omega)
  have hu' : u = (((p+(s:ℤ)):CutRing)*cutTau)+(u.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [cutTau,hs,endpointLabel]
  have hv' : v = (((p+(t:ℤ)):CutRing)*cutTau)+(v.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [cutTau,ht,endpointLabel]
  change coordinateBetween a j u v ∈ A
  rw [hu',hv',coordinateBetween_period]
  exact hall s t (by omega) (by omega)

theorem axisWindowEmbedding_spec (j : Fin 2) (n k : ℕ) (q : Fin 2 → ℤ) (p : ℤ)
    (hs : q j ≤ p) (he : p+(k:ℤ) ≤ q j+n) :
    coordinateWindowPrimitives n q ∘ axisWindowEmbedding j n k q p hs he =
      axisWindowPrimitives j k p := by
  funext i
  apply Prod.ext
  · rfl
  · change coordinateShift j (((q j+(((p-q j).toNat+i.val:ℕ):ℤ)):CutRing)*cutTau) = _
    have hh : ((p-q j).toNat:ℤ) = p-q j := Int.toNat_of_nonneg (by omega)
    simp only [Nat.cast_add,hh]
    congr 2
    push_cast
    ring

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem axisFamilyLaw (n : ℕ) (h : B.CoordinateWindowLaw n) (j : Fin 2)
    (k : ℕ) (hk : k ≤ n) (p : ℤ) (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) : B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives j k p) :=
  PrimitiveFamilyLaw.reindex B I b hb (coordinateWindowPrimitives k (fun _ => p))
    (CoordinateWindowLaw.mono B h hk I b hb (fun _ => p)) (fun i => (j,i))

noncomputable def axisSector (hlarge : 15 < m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup (Fin (m+1))) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (axisWindowPrimitives j k p)
    (fun I _ b hb => B.axisFamilyLaw n h j k hk p I b hb) V

theorem axisSector_in_window (hlarge : 15 < m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (q : Fin 2 → ℤ)
    (hs : q j ≤ p) (he : p+(k:ℤ) ≤ q j+n) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) i).val) V.val) :
    B.axisSector hlarge n h j k hk p V = B.windowSector hlarge n h q V :=
  B.fullGeometricSector_subfamily hlarge _ _ (axisWindowEmbedding j n k q p hs he)
    (axisWindowEmbedding_spec j n k q p hs he) _ _ V hV

end InitialCoverSystem
end AxisWindows

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ArithmeticTangentBasis
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

section FiniteTangentChains

noncomputable def integerSteps (k : ℤ) (u : CutRing) : List CutRing :=
  if 0 ≤ k then List.replicate k.toNat u else List.replicate (-k).toNat (-u)

@[simp]theorem integerSteps_sum (k : ℤ) (u : CutRing) :
    (integerSteps k u).sum = (k : CutRing)*u := by
  by_cases hk : 0 ≤ k
  · have hc : (k.toNat : CutRing) = (k : CutRing) := by
      exact_mod_cast Int.toNat_of_nonneg hk
    simp [integerSteps,hk,List.sum_replicate,nsmul_eq_mul,hc]
  · have hn : 0 ≤ -k := by omega
    have hc : ((-k).toNat : CutRing) = -(k : CutRing) := by
      exact_mod_cast Int.toNat_of_nonneg hn
    simp [integerSteps,hk,List.sum_replicate,nsmul_eq_mul,hc]

@[simp]theorem endpointLabel_list_sum (xs : List CutRing) :
    (endpointLabel xs.sum : ℝ) = (xs.map (fun z => (endpointLabel z : ℝ))).sum := by
  induction xs with
  | nil => simp [endpointLabel]
  | cons x xs ih => simpa only [List.sum_cons,endpointLabel_add,Int.cast_add,
      List.map_cons] using congrArg (fun r => (endpointLabel x : ℝ)+r) ih

end FiniteTangentChains

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_LatticeCounting
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

section QuantitativeArithmetic

theorem quadratic_lattice_cover (u : CutRing) (hu : u ≠ 0) (x y : ℝ) :
    ∃ z : CutRing, |ordinary z - x| ≤ 3 * |ordinary u| ∧
      |conjugate z - y| ≤ 2 * |conjugate u| := by
  have huo : ordinary u ≠ 0 := by simpa using ordinary_injective.ne hu
  have huc : conjugate u ≠ 0 := by simpa using conjugate_injective.ne hu
  have hd : Real.goldenRatio - Real.goldenConj ≠ 0 := by
    rw [Real.goldenRatio_sub_goldenConj]
    exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  let b := (x / ordinary u - y / conjugate u) /
    (Real.goldenRatio - Real.goldenConj)
  let a := x / ordinary u - b * Real.goldenRatio
  have hb : b * (Real.goldenRatio - Real.goldenConj) =
      x / ordinary u - y / conjugate u := div_mul_cancel₀ _ hd
  have ha₁ : a + b * Real.goldenRatio = x / ordinary u := by dsimp [a]; ring
  have ha₂ : a + b * Real.goldenConj = y / conjugate u := by dsimp [a]; nlinarith [hb]
  have hx : ordinary u * (a + b * Real.goldenRatio) = x := by
    rw [ha₁]; exact mul_div_cancel₀ _ huo
  have hy : conjugate u * (a + b * Real.goldenConj) = y := by
    rw [ha₂]; exact mul_div_cancel₀ _ huc
  let z : CutRing := u * ((⌊a⌋ : CutRing) + (⌊b⌋ : CutRing) * cutTau)
  have ho : ordinary z - x = ordinary u *
      (((⌊a⌋ : ℝ) - a) + ((⌊b⌋ : ℝ) - b) * Real.goldenRatio) := by
    dsimp [z]
    simp only [map_mul,map_add,map_intCast,ordinary_cutTau]
    rw [← hx]; ring
  have hc : conjugate z - y = conjugate u *
      (((⌊a⌋ : ℝ) - a) + ((⌊b⌋ : ℝ) - b) * Real.goldenConj) := by
    dsimp [z]
    simp only [map_mul,map_add,map_intCast,conjugate_cutTau]
    rw [← hy]; ring
  have hr : |Real.goldenRatio| ≤ 2 := by
    rw [abs_of_pos Real.goldenRatio_pos]
    exact Real.goldenRatio_lt_two.le
  have hb' : |Real.goldenConj| ≤ 1 := by
    rw [abs_of_neg Real.goldenConj_neg]
    linarith [Real.neg_one_lt_goldenConj]
  have bound (t : ℝ) (B : ℝ) (ht : |t| ≤ B) :
      |((⌊a⌋ : ℝ) - a) + ((⌊b⌋ : ℝ) - b)*t| ≤ 1+B := by
    calc
      _ ≤ |(⌊a⌋ : ℝ)-a| + |((⌊b⌋ : ℝ)-b)*t| := abs_add_le _ _
      _ = |(⌊a⌋ : ℝ)-a| + |(⌊b⌋ : ℝ)-b| *|t| := by rw [abs_mul]
      _ ≤ 1 + 1*B := by gcongr; exact floor_error a; exact floor_error b
      _ = _ := by ring
  refine ⟨z,?_,?_⟩
  · rw [ho,abs_mul]
    have := mul_le_mul_of_nonneg_left (bound _ _ hr) (abs_nonneg (ordinary u))
    nlinarith
  · rw [hc,abs_mul]
    have := mul_le_mul_of_nonneg_left (bound _ _ hb') (abs_nonneg (conjugate u))
    nlinarith

theorem scaled_quadratic_lattice_cover (L : ℝ) (hL : 1 ≤ L) (x y : ℝ) :
    ∃ z : CutRing, |ordinary z - x| ≤ 6 / L ∧
      |conjugate z - y| ≤ 2 * L := by
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hL Real.one_lt_goldenRatio
  let u : CutRing := (cutTau - 1)^k
  have hτ : 0 < Real.goldenRatio^k := pow_pos Real.goldenRatio_pos _
  have ho : ordinary u = (Real.goldenRatio^k)⁻¹ := by
    simp only [u,map_pow,map_sub,ordinary_cutTau,map_one]
    rw [← inv_pow]
    congr 1
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hc : |conjugate u| = Real.goldenRatio^k := by
    simp only [u,map_pow,map_sub,conjugate_cutTau,map_one,abs_pow]
    congr 1
    rw [abs_of_neg (by linarith [Real.goldenConj_neg] : Real.goldenConj - 1 < 0)]
    linarith [Real.goldenRatio_add_goldenConj]
  have hu : u ≠ 0 := by
    intro h
    have he : ordinary u = 0 := by rw [h,map_zero]
    rw [ho] at he
    exact (inv_ne_zero hτ.ne') he
  obtain ⟨z,hz,hz'⟩ := quadratic_lattice_cover u hu x y
  refine ⟨z,hz.trans ?_,hz'.trans ?_⟩
  · rw [ho,abs_of_pos (inv_pos.mpr hτ)]
    have hL0 : 0 < L := by linarith
    have hnear : L < 2*Real.goldenRatio^k := by
      rw [pow_succ] at hk'
      nlinarith [Real.goldenRatio_lt_two]
    apply (le_div_iff₀ hL0).mpr
    have he : (Real.goldenRatio^k)⁻¹ * Real.goldenRatio^k = 1 := inv_mul_cancel₀ hτ.ne'
    nlinarith [mul_lt_mul_of_pos_left hnear (inv_pos.mpr hτ)]
  · rw [hc]
    linarith

theorem coordinate_window_net (n : ℕ) (hn : 1 ≤ n) (q : ℤ) (t : ℝ) :
    ∃ z : CutRing, q ≤ endpointLabel z ∧ endpointLabel z < q + n ∧
      |ordinary z - t| ≤ 100 / (n : ℝ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  by_cases hn32 : 32 ≤ n
  · have hn32' : (32:ℝ) ≤ n := by exact_mod_cast hn32
    let c : ℝ := (q:ℝ) + (n:ℝ)/2
    obtain ⟨z,ho,hb⟩ := scaled_quadratic_lattice_cover ((n:ℝ)/16) (by linarith)
      t (t-c*Real.sqrt 5)
    have ho' : |ordinary z-t| ≤ 96/(n:ℝ) := by
      convert ho using 1; field_simp; ring
    have hb' : |conjugate z-(t-c*Real.sqrt 5)| ≤ (n:ℝ)/8 := by
      convert hb using 1 <;> first | rfl | ring
    have hs : 1 ≤ Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),Real.sqrt_nonneg 5]
    have hsmall : 96/(n:ℝ) ≤ (n:ℝ)/8 := by
      apply (div_le_iff₀ hn0).mpr
      nlinarith
    have hlabel : |(endpointLabel z:ℝ)-c| ≤ (n:ℝ)/4 := by
      have he : ((endpointLabel z:ℝ)-c)*Real.sqrt 5 =
          (ordinary z-t)-(conjugate z-(t-c*Real.sqrt 5)) := by
        have he := (eq_div_iff (ne_of_gt (lt_of_lt_of_le zero_lt_one hs))).mp
          (endpointLabel_embedding z)
        nlinarith [he]
      have htri : |(ordinary z-t)-(conjugate z-(t-c*Real.sqrt 5))| ≤
          |ordinary z-t| + |conjugate z-(t-c*Real.sqrt 5)| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (ordinary z-t) 0 (conjugate z-(t-c*Real.sqrt 5))
      rw [← he,abs_mul,abs_of_nonneg (le_trans zero_le_one hs)] at htri
      nlinarith [abs_nonneg ((endpointLabel z:ℝ)-c)]
    have hlow : (q:ℝ) ≤ (endpointLabel z:ℝ) := by
      have hh := (abs_le.mp hlabel).1
      dsimp [c] at hh
      linarith
    have hhigh : (endpointLabel z:ℝ) < (q:ℝ)+(n:ℝ) := by
      have hh := (abs_le.mp hlabel).2
      dsimp [c] at hh
      linarith
    refine ⟨z,by exact_mod_cast hlow,by exact_mod_cast hhigh,ho'.trans ?_⟩
    apply div_le_div_of_nonneg_right (by norm_num) hn0.le
  · let z : CutRing := ⟨⌊t-(q:ℝ)*Real.goldenRatio⌋,q⟩
    refine ⟨z,le_rfl,by change q < q+(n:ℤ); omega,?_⟩
    have he : ordinary z-t = (⌊t-(q:ℝ)*Real.goldenRatio⌋:ℝ)-
        (t-(q:ℝ)*Real.goldenRatio) := by simp only [ordinary_apply,z]; ring
    rw [he]
    apply (floor_error _).trans
    apply (le_div_iff₀ hn0).mpr
    have : (n:ℝ) < 32 := by exact_mod_cast (lt_of_not_ge hn32)
    linarith

end QuantitativeArithmetic

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SpatialChartGeometry
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

section ChartTransforms

@[simp] theorem spatialTranslate_inter {a : ℕ} (z : CutRing × CutRing)
    (U V : polygonAlgebra a) : spatialTranslate z (U ⊓ V) =
      spatialTranslate z U ⊓ spatialTranslate z V := rfl

@[simp] theorem spatialTranslate_compl {a : ℕ} (z : CutRing × CutRing)
    (U : polygonAlgebra a) : spatialTranslate z Uᶜ = (spatialTranslate z U)ᶜ := rfl

end ChartTransforms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TangentChartTemplates
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
section TangentChartTemplates

@[simp] theorem initialTest_slope (a : ℕ) (r : CutRing) (d : Fin 2) :
    initialTest a r (slopeTestIndex d) = clippedSlopePrimitive a r (slopeDirection d) := by
  fin_cases d <;> rfl

noncomputable def tangentOffset (a : ℕ) (d : Fin 2) (e : CutRing) : CutRing × CutRing :=
  if d=0 then (e,cutTau^a*e) else (cutTau^a*e,e)

@[simp] theorem tangentOffset_zero (a : ℕ) (d : Fin 2) : tangentOffset a d 0 = 0 := by
  simp [tangentOffset]

@[simp] theorem tangentOffset_add (a : ℕ) (d : Fin 2) (e f : CutRing) :
    tangentOffset a d (e+f) = tangentOffset a d e+tangentOffset a d f := by
  fin_cases d <;> simp [tangentOffset,mul_add]

@[simp] theorem integralCutForm_tangentOffset (a : ℕ) (d : Fin 2) (e : CutRing) :
    integralCutForm a (slopeDirection d) (tangentOffset a d e) = 0 := by
  fin_cases d <;> simp [slopeDirection,tangentOffset,integralCutForm]

end TangentChartTemplates

section TangentChartAction

@[simp] theorem integralCutForm_zero (a : ℕ) (j : Fin 4) :
    integralCutForm a j (0 : CutRing × CutRing) = 0 := by
  fin_cases j <;> simp [integralCutForm]

@[simp] theorem integralCutForm_add (a : ℕ) (j : Fin 4) (u v : CutRing × CutRing) :
    integralCutForm a j (u+v) = integralCutForm a j u+integralCutForm a j v := by
  fin_cases j <;> simp [integralCutForm,mul_add] <;> ring

end TangentChartAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LabelShiftedCharts
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
section LabelShiftedCharts

noncomputable def pointCoordinate (z : CutRing × CutRing) (j : Fin 2) : CutRing :=
  if j=0 then z.1 else z.2

noncomputable def pointLabel (z : CutRing × CutRing) (j : Fin 2) : ℤ := endpointLabel (pointCoordinate z j)

@[simp] theorem pointCoordinate_add (z w : CutRing × CutRing) (j : Fin 2) :
    pointCoordinate (z+w) j = pointCoordinate z j+pointCoordinate w j := by
  fin_cases j <;> rfl

@[simp] theorem pointLabel_add (z w : CutRing × CutRing) (j : Fin 2) :
    pointLabel (z+w) j = pointLabel z j+pointLabel w j := by
  simp only [pointLabel,pointCoordinate_add,endpointLabel_add]

@[simp] theorem endpointLabel_int_mul_tau (i : ℤ) :
    endpointLabel ((i : CutRing)*cutTau) = i := by simp [endpointLabel,cutTau]

@[simp] theorem coordinateWindow_pointLabel (k : ℕ) (p : Fin 2 → ℤ)
    (i : Fin 2 × Fin (k-1)) :
    pointLabel (coordinateWindowPrimitives k p i).2 i.1 = p i.1+(i.2.val:ℤ) := by
  simp only [coordinateWindowPrimitives,pointLabel,pointCoordinate,coordinateShift]
  split <;> rw [← Int.cast_add, endpointLabel_int_mul_tau]

end LabelShiftedCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TangentWalkCenters
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
section TangentWalkCenters

@[simp] theorem pointCoordinate_zero (j : Fin 2) : pointCoordinate (0 : CutRing × CutRing) j = 0 := by
  simp [pointCoordinate]

@[simp] theorem pointCoordinate_sub (z w : CutRing × CutRing) (j : Fin 2) :
    pointCoordinate (z-w) j = pointCoordinate z j-pointCoordinate w j := by
  fin_cases j <;> rfl

@[simp] theorem pointLabel_zero (j : Fin 2) : pointLabel (0 : CutRing × CutRing) j = 0 := by
  simp [pointLabel,endpointLabel]

@[simp] theorem pointLabel_sub (z w : CutRing × CutRing) (j : Fin 2) :
    pointLabel (z-w) j = pointLabel z j-pointLabel w j := by
  simp only [pointLabel,pointCoordinate_sub,endpointLabel_sub]

end TangentWalkCenters

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

@[simp] theorem endpointLabel_neg (z : CutRing) : endpointLabel (-z) = -endpointLabel z := rfl

end SymmetricCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_Rectangles
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
section OldRectangles

structure LabelledRectangle (n : ℕ) where
  length : Fin 2 → ℕ
  length_le : ∀ j, length j ≤ n
  start : Fin 2 → ℤ
  lower : Fin 2 → CutRing
  upper : Fin 2 → CutRing
  ordered : ∀ j, ordinary (lower j) ≤ ordinary (upper j)
  lower_label : ∀ j, start j ≤ endpointLabel (lower j) ∧ endpointLabel (lower j) < start j+length j
  upper_label : ∀ j, start j ≤ endpointLabel (upper j) ∧ endpointLabel (upper j) < start j+length j

end OldRectangles

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowCells
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
section WindowCells

noncomputable def cutFraction (z : CutRing) : CutRing := z-(⌊ordinary z⌋:ℤ)

@[simp] theorem ordinary_cutFraction (z : CutRing) :
    ordinary (cutFraction z) = Int.fract (ordinary z) := by
  simp only [cutFraction,map_sub,map_intCast,Int.fract]

@[simp] theorem endpointLabel_cutFraction (z : CutRing) :
    endpointLabel (cutFraction z) = endpointLabel z := by
  simp [cutFraction,endpointLabel_sub]

@[simp] theorem endpointLabel_labelTau (q : ℤ) :
    endpointLabel ((q:CutRing)*cutTau) = q := by
  simp [endpointLabel,cutTau,QuadraticAlgebra.im_mul]

@[simp] theorem cutFraction_zero : cutFraction 0 = 0 := by
  simp [cutFraction]

noncomputable def windowEndpointSet (n : ℕ) : Finset CutRing := by
  classical
  exact Finset.univ.image fun i : Fin n => cutFraction ((i.val:CutRing)*cutTau)

theorem windowEndpointSet_card (n : ℕ) : (windowEndpointSet n).card = n := by
  classical
  rw [windowEndpointSet,Finset.card_image_of_injective]
  · simp
  · intro i j hij
    have hh := congrArg endpointLabel hij
    simp only [endpointLabel_cutFraction] at hh
    have he (k : ℕ) : endpointLabel ((k:CutRing)*cutTau) = (k:ℤ) := by
      exact_mod_cast endpointLabel_labelTau (k:ℤ)
    simp only [he] at hh
    exact Fin.ext (by omega)

@[instance_reducible] noncomputable def cutOrdinaryOrder : LinearOrder CutRing :=
  LinearOrder.lift' ordinary ordinary_injective

attribute [local instance] cutOrdinaryOrder

noncomputable def windowInterior (n : ℕ) : Fin n ↪o CutRing :=
  (windowEndpointSet n).orderEmbOfFin (windowEndpointSet_card n)

theorem windowInterior_mem (n : ℕ) (i : Fin n) :
    windowInterior n i ∈ windowEndpointSet n := Finset.orderEmbOfFin_mem _ _ _

theorem windowInterior_bounds (n : ℕ) (i : Fin n) :
    0 ≤ ordinary (windowInterior n i) ∧ ordinary (windowInterior n i) < 1 := by
  have hh := windowInterior_mem n i
  simp only [windowEndpointSet,Finset.mem_image,Finset.mem_univ,true_and] at hh
  obtain ⟨j,hj⟩ := hh
  rw [← hj,ordinary_cutFraction]
  exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

noncomputable def windowCut (n : ℕ) (q : ℤ) (i : Fin (n+1)) : CutRing :=
  (q:CutRing)*cutTau+if hi : i.val < n then windowInterior n ⟨i.val,hi⟩ else 1

@[simp] theorem cutFraction_eq_self (z : CutRing)
    (hz : 0 ≤ ordinary z ∧ ordinary z < 1) : cutFraction z = z := by
  apply ordinary_injective
  rw [ordinary_cutFraction,Int.fract_eq_self.mpr hz]

theorem cutFraction_label (z : CutRing) :
    cutFraction z = cutFraction ((endpointLabel z:CutRing)*cutTau) := by
  have he : z = ((endpointLabel z:CutRing)*cutTau)+(z.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [endpointLabel,cutTau]
  apply ordinary_injective
  simp only [ordinary_cutFraction]
  conv_lhs => rw [he,map_add,map_intCast,Int.fract_add_intCast]

theorem windowEndpointSet_of_bounds (n : ℕ) (z : CutRing)
    (hl : 0 ≤ endpointLabel z ∧ endpointLabel z < n)
    (ho : 0 ≤ ordinary z ∧ ordinary z < 1) : z ∈ windowEndpointSet n := by
  classical
  have hi : (endpointLabel z).toNat < n := by omega
  have he : ((endpointLabel z).toNat:ℤ) = endpointLabel z := Int.toNat_of_nonneg hl.1
  apply Finset.mem_image.mpr
  refine ⟨⟨(endpointLabel z).toNat,hi⟩,Finset.mem_univ _,?_⟩
  change cutFraction (((endpointLabel z).toNat:CutRing)*cutTau) = z
  have hc : ((endpointLabel z).toNat:CutRing) = (endpointLabel z:CutRing) := by
    exact_mod_cast he
  rw [hc,← cutFraction_label,cutFraction_eq_self z ho]

theorem windowCut_bounds (n : ℕ) (q : ℤ) (i : Fin (n+1)) :
    ordinary ((q:CutRing)*cutTau) ≤ ordinary (windowCut n q i) ∧
      ordinary (windowCut n q i) ≤ ordinary ((q:CutRing)*cutTau)+1 := by
  unfold windowCut
  split_ifs with hi
  · simp only [map_add]
    have hh := windowInterior_bounds n ⟨i.val,hi⟩
    constructor <;> linarith
  · simp only [map_add,map_one]
    constructor <;> linarith

theorem windowCut_no_between (n : ℕ) (q : ℤ) (i : Fin n) (z : CutRing)
    (hz : q ≤ endpointLabel z ∧ endpointLabel z < q+n) :
    ¬(ordinary (windowCut n q i.castSucc) < ordinary z ∧
      ordinary z < ordinary (windowCut n q i.succ)) := by
  rintro ⟨hlo,hup⟩
  let z' : CutRing := z-(q:CutRing)*cutTau
  have hzl : 0 ≤ endpointLabel z' ∧ endpointLabel z' < n := by
    simp only [z',endpointLabel_sub,endpointLabel_labelTau]
    omega
  have hzo : 0 ≤ ordinary z' ∧ ordinary z' < 1 := by
    simp only [z',map_sub]
    have hh := (windowCut_bounds n q i.castSucc).1
    have hh' := (windowCut_bounds n q i.succ).2
    constructor <;> linarith
  have hmem := windowEndpointSet_of_bounds n z' hzl hzo
  have hx : z' ∈ Set.range (windowInterior n) := by
    change z' ∈ Set.range ((windowEndpointSet n).orderEmbOfFin (windowEndpointSet_card n))
    rw [Finset.range_orderEmbOfFin]; exact hmem
  obtain ⟨j,hj⟩ := hx
  have hlow : ordinary (windowInterior n i) < ordinary (windowInterior n j) := by
    simp only [windowCut,Fin.val_castSucc,dite_eq_left i.isLt,map_add] at hlo
    rw [hj]
    dsimp only [z']
    rw [map_sub]
    linarith
  have hij : i < j := (windowInterior n).lt_iff_lt.mp hlow
  have hin : i.val+1 < n := by have h := j.isLt; change i.val < j.val at hij; omega
  have hupper : ordinary (windowInterior n j) < ordinary (windowInterior n ⟨i.val+1,hin⟩) := by
    simp only [windowCut,Fin.val_succ,dite_eq_left hin,map_add] at hup
    rw [hj]
    dsimp only [z']
    rw [map_sub]
    linarith
  have hji : j < (⟨i.val+1,hin⟩:Fin n) := (windowInterior n).lt_iff_lt.mp hupper
  change j.val < i.val+1 at hji
  change i.val < j.val at hij
  omega

theorem windowCut_mesh (n : ℕ) (q : ℤ) (i : Fin n) :
    ordinary (windowCut n q i.succ)-ordinary (windowCut n q i.castSucc) ≤ 200/(n:ℝ) := by
  by_contra hbad
  have hn : 1 ≤ n := by have hh := i.isLt; omega
  have hg : 200/(n:ℝ) < ordinary (windowCut n q i.succ)-ordinary (windowCut n q i.castSucc) := lt_of_not_ge hbad
  obtain ⟨z,hzl,hzu,hz⟩ := coordinate_window_net n hn q
    ((ordinary (windowCut n q i.castSucc)+ordinary (windowCut n q i.succ))/2)
  have hab := abs_le.mp hz
  have hden : 200/(n:ℝ)=2*(100/(n:ℝ)) := by ring
  rw [hden] at hg
  exact windowCut_no_between n q i z ⟨hzl,hzu⟩ ⟨by linarith,by linarith⟩

end WindowCells

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

noncomputable def orientedPoint (d : Fin 2) (x y : CutRing) : CutRing × CutRing :=
  if d=0 then (x,y) else (y,x)

@[simp] theorem orientedPoint_coordinate (d j : Fin 2) (x y : CutRing) :
    pointCoordinate (orientedPoint d x y) j = if j=d then x else y := by
  fin_cases d <;> fin_cases j <;> simp [orientedPoint,pointCoordinate]

@[simp] theorem orientedPoint_label (d j : Fin 2) (x y : CutRing) :
    pointLabel (orientedPoint d x y) j = if j=d then endpointLabel x else endpointLabel y := by
  simp only [pointLabel,orientedPoint_coordinate]
  split <;> rfl

@[simp] theorem orientedPoint_tangent (a : ℕ) (d : Fin 2) (x y b : CutRing) :
    orientedPoint d x y+tangentOffset a d (b-x) = orientedPoint d b (y+cutTau^a*(b-x)) := by
  fin_cases d <;> simp [orientedPoint,tangentOffset]

structure OldStripPair (n : ℕ) (d : Fin 2) where
  left : LabelledRectangle n
  right : LabelledRectangle n
  lo : CutRing
  cutLeft : CutRing
  cutRight : CutRing
  hi : CutRing
  bottom : CutRing
  top : CutRing
  left_lower : ∀ j, left.lower j = if j=d then lo else bottom
  left_upper : ∀ j, left.upper j = if j=d then cutLeft else top
  right_lower : ∀ j, right.lower j = if j=d then cutRight else bottom
  right_upper : ∀ j, right.upper j = if j=d then hi else top
  ordered_left : ordinary lo ≤ ordinary cutLeft
  ordered_gap : ordinary cutLeft < ordinary cutRight
  ordered_right : ordinary cutRight ≤ ordinary hi
  ordered_cross : ordinary bottom ≤ ordinary top
  left_length : ∀ j, left.length j ≤ if j=d then n*9/10 else n/4
  right_length : ∀ j, right.length j ≤ if j=d then n*9/10 else n/4

namespace OldStripPair
variable {n : ℕ} {d : Fin 2} (P : OldStripPair n d)

noncomputable def displacement : CutRing := P.cutRight-P.cutLeft

@[simp] theorem displacement_ordinary : ordinary P.displacement = ordinary P.cutRight-ordinary P.cutLeft := by
  simp [displacement]

end OldStripPair

end SeparatedOldRectangles

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CellGeometry
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
section CellGeometry

theorem coordinateInterval_union {a : ℕ} (j : Fin 2) (u v w : CutRing)
    (huv : ordinary u ≤ ordinary v) (hvw : ordinary v ≤ ordinary w)
    (hlen : ordinary w-ordinary u < 1) :
    coordinateInterval a j u w = coordinateInterval a j u v ⊔ coordinateInterval a j v w := by
  apply Subtype.ext
  ext p
  change p ∈ coordinateBetween a j u w ↔ p ∈ coordinateBetween a j u v ∨ p ∈ coordinateBetween a j v w
  rw [mem_coordinateBetween_iff j u w (huv.trans hvw) hlen,
    mem_coordinateBetween_iff j u v huv (by linarith),
    mem_coordinateBetween_iff j v w hvw (by linarith)]
  constructor
  · rintro ⟨k,hk,hk'⟩
    by_cases hh : coordinate j p+(k:ℝ) < ordinary v
    · exact Or.inl ⟨k,hk,hh⟩
    · exact Or.inr ⟨k,le_of_not_gt hh,hk'⟩
  · rintro (⟨k,hk,hk'⟩|⟨k,hk,hk'⟩)
    · exact ⟨k,hk,hk'.trans_le hvw⟩
    · exact ⟨k,huv.trans hk,hk'⟩

end CellGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteSectorPartition
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
section FiniteSectorPartition

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Fintype κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_union (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hd : Disjoint V.val W.val) (s : TrackStar (Fin (m+1))) :
    B.fullGeometricSector hlarge P h (V ⊔ W) s =
      B.fullGeometricSector hlarge P h V s * B.fullGeometricSector hlarge P h W s := by
  unfold fullGeometricSector
  change (B.fullPrimitiveTable hlarge P h).sector (resolvedPolygonMask _ (V.val ∪ W.val)) s = _
  rw [resolvedPolygonMask_union]
  exact DFunLike.congr_fun ((B.fullPrimitiveTable hlarge P h).sector_union
    (resolvedPolygonMask_disjoint _ hV hd)) s

end InitialCoverSystem

end FiniteSectorPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AxisSplitting
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
section AxisSplitting
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_split (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u v w : CutRing)
    (huv : ordinary u ≤ ordinary v) (hvw : ordinary v ≤ ordinary w)
    (hlen : ordinary w-ordinary u < 1)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (s : TrackStar (Fin (m+1))) :
    B.axisSector hlarge n g d k hk p (coordinateInterval a d u w) s =
      B.axisSector hlarge n g d k hk p (coordinateInterval a d u v) s *
      B.axisSector hlarge n g d k hk p (coordinateInterval a d v w) s := by
  rw [coordinateInterval_union d u v w huv hvw hlen]
  exact B.fullGeometricSector_union hlarge _ _ _ _ (axisInterval_resolved d k p u v hu hv)
    (coordinateInterval_disjoint d u v v w huv le_rfl hvw hlen) s

end InitialCoverSystem
end AxisSplitting

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SeparatedAxisSectors
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

section AxisCoherence

@[simp] theorem coordinateInterval_self {a : ℕ} (d : Fin 2) (u : CutRing) :
    coordinateInterval a d u u = ⊥ := by
  apply Subtype.ext
  exact coordinateBetween_empty d u u (by simp)

noncomputable def endpointPairStart (u v : CutRing) : ℤ := min (endpointLabel u) (endpointLabel v)
noncomputable def endpointPairLength (u v : CutRing) : ℕ :=
  (max (endpointLabel u) (endpointLabel v)-endpointPairStart u v).toNat+1

theorem endpointPairLength_cast (u v : CutRing) :
    (endpointPairLength u v : ℤ) = max (endpointLabel u) (endpointLabel v)-endpointPairStart u v+1 := by
  have hh : 0 ≤ max (endpointLabel u) (endpointLabel v)-endpointPairStart u v := by
    simp only [endpointPairStart]; omega
  simp only [endpointPairLength,Nat.cast_add,Nat.cast_one,Int.toNat_of_nonneg hh]

theorem endpointPair_labels (u v : CutRing) :
    (endpointPairStart u v ≤ endpointLabel u ∧ endpointLabel u < endpointPairStart u v+endpointPairLength u v) ∧
    (endpointPairStart u v ≤ endpointLabel v ∧ endpointLabel v < endpointPairStart u v+endpointPairLength u v) := by
  rw [endpointPairLength_cast]
  simp only [endpointPairStart]
  omega

theorem endpointPair_in_window (u v : CutRing) (p : ℤ) (k : ℕ)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) :
    p ≤ endpointPairStart u v ∧ endpointPairStart u v+endpointPairLength u v ≤ p+k ∧
      endpointPairLength u v ≤ k := by
  have hh := endpointPairLength_cast u v
  simp only [endpointPairStart] at hh ⊢
  omega

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_subwindow (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (p q : ℤ)
    (hs : p ≤ q) (he : q+l ≤ p+k) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (axisWindowPrimitives d k p) i).val) V.val)
    (hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (axisWindowPrimitives d l q) i).val) V.val) :
    B.axisSector hlarge n g d k hk p V = B.axisSector hlarge n g d l hl q V := by
  rw [B.axisSector_in_window hlarge n g d k hk p (fun _ => p) le_rfl (by omega) V hV,
    B.axisSector_in_window hlarge n g d l hl q (fun _ => p) hs (by omega) V hV']

theorem axisInterval_copy_eq (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (p q : ℤ) (u v : CutRing)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hu' : q ≤ endpointLabel u ∧ endpointLabel u < q+l)
    (hv' : q ≤ endpointLabel v ∧ endpointLabel v < q+l) :
    B.axisSector hlarge n g d k hk p (coordinateInterval a d u v) =
      B.axisSector hlarge n g d l hl q (coordinateInterval a d u v) := by
  have hp := endpointPair_in_window u v p k hu hv
  have hq := endpointPair_in_window u v q l hu' hv'
  have hend := endpointPair_labels u v
  rw [B.axisSector_subwindow hlarge n g d k (endpointPairLength u v) hk (by omega)
      p (endpointPairStart u v) hp.1 hp.2.1 _ (axisInterval_resolved d k p u v hu hv)
      (axisInterval_resolved d _ _ u v hend.1 hend.2),
    B.axisSector_subwindow hlarge n g d l (endpointPairLength u v) hl (by omega)
      q (endpointPairStart u v) hq.1 hq.2.1 _ (axisInterval_resolved d l q u v hu' hv')
      (axisInterval_resolved d _ _ u v hend.1 hend.2)]

end InitialCoverSystem
end AxisCoherence

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AxisCutSequences
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
section AxisCutSequences

structure AxisCutSequence (n K : ℕ) where
  cut : Fin (K+1) → CutRing
  strictMono : StrictMono (fun i => ordinary (cut i))
  length : Fin (K+1) → ℕ
  start : Fin (K+1) → ℤ
  length_le : ∀ i, length i ≤ n*9/10
  lower_label : ∀ i, start i ≤ endpointLabel (cut 0) ∧ endpointLabel (cut 0) < start i+length i
  upper_label : ∀ i, start i ≤ endpointLabel (cut (Fin.last K)) ∧ endpointLabel (cut (Fin.last K)) < start i+length i
  cut_label : ∀ i, start i ≤ endpointLabel (cut i) ∧ endpointLabel (cut i) < start i+length i

namespace AxisCutSequence
variable {n K : ℕ} (D : AxisCutSequence n K)

def index (_D : AxisCutSequence n K) (i : ℕ) : Fin (K+1) := ⟨min i K,by omega⟩
@[simp] theorem index_zero : D.index 0 = 0 := by ext; simp [index]
@[simp] theorem index_fin (i : Fin (K+1)) : D.index i.val = i := by ext; simp [index]; omega

theorem ordered (i : Fin (K+1)) :
    ordinary (D.cut 0) ≤ ordinary (D.cut i) ∧ ordinary (D.cut i) ≤ ordinary (D.cut (Fin.last K)) :=
  ⟨D.strictMono.monotone (Fin.zero_le i),D.strictMono.monotone (Fin.le_last i)⟩

theorem length_old (i : Fin (K+1)) : D.length i ≤ n := by have hh := D.length_le i; omega

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

noncomputable def anchorCopy : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.axisSector hlarge n g d (D.length 0) (D.length_old 0) (D.start 0)
    (coordinateInterval a d (D.cut 0) (D.cut (Fin.last K)))

noncomputable def prefixCopy (i : ℕ) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.axisSector hlarge n g d (D.length (D.index i)) (D.length_old _) (D.start (D.index i))
    (coordinateInterval a d (D.cut 0) (D.cut (D.index i)))

noncomputable def suffix (i : ℕ) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.axisSector hlarge n g d (D.length (D.index i)) (D.length_old _) (D.start (D.index i))
    (coordinateInterval a d (D.cut (D.index i)) (D.cut (Fin.last K)))

theorem anchorCopy_eq (i : Fin (K+1)) :
    D.anchorCopy B hlarge g d =
      B.axisSector hlarge n g d (D.length i) (D.length_old i) (D.start i)
        (coordinateInterval a d (D.cut 0) (D.cut (Fin.last K))) :=
  B.axisInterval_copy_eq hlarge n g d _ _ _ _ _ _ _ _
    (D.lower_label 0) (D.upper_label 0) (D.lower_label i) (D.upper_label i)

theorem prefix_suffix (hlen : ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1) (i : ℕ)
    (s : TrackStar (Fin (m+1))) :
    D.anchorCopy B hlarge g d s = D.prefixCopy B hlarge g d i s*D.suffix B hlarge g d i s := by
  rw [D.anchorCopy_eq B hlarge g d (D.index i)]
  exact B.axisSector_split hlarge n g d _ _ _ _ _ _
    (D.ordered _).1 (D.ordered _).2 hlen (D.lower_label _) (D.cut_label _) s

end AxisCutSequence
end AxisCutSequences

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_DisjointPolygonAtoms
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
section DisjointPolygonAtoms
variable {a m : ℕ} {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
theorem polygonTableInput_disjoint (U : Ω → polygonAlgebra a)
    (hd : Pairwise fun i j => Disjoint (U i).val (U j).val) :
    Pairwise fun i j => ∀ s t : alternatingGroup (Fin m),
      Commute (polygonTableInput U i s) (polygonTableInput U j t) := by
  intro i j hij s t
  apply sectorMask_commute
  apply Set.disjoint_left.mpr
  rintro ⟨ω,p,rfl⟩ hi hj
  have hi' : p ∈ (U i).val := by simpa [polygonAssignment] using hi
  have hj' : p ∈ (U j).val := by simpa [polygonAssignment] using hj
  exact Set.disjoint_left.mp (hd hij) hi' hj'

noncomputable def polygonDisjointTable (U : Ω → polygonAlgebra a)
    (hd : Pairwise fun i j => Disjoint (U i).val (U j).val) :
    (Ω → alternatingGroup (Fin m)) →* polygonAlternatingGroup a m :=
  (actualPolygonTableHom U).comp (MonoidHom.noncommPiCoprod
    (fun i => polygonTableInput U i) (polygonTableInput_disjoint U hd))

@[simp] theorem polygonDisjointTable_single [DecidableEq Ω] (U : Ω → polygonAlgebra a)
    (hd : Pairwise fun i j => Disjoint (U i).val (U j).val) (i : Ω) (s : alternatingGroup (Fin m)) :
    polygonDisjointTable U hd (Pi.mulSingle i s) = conditionalAlternatingHom (U i) s := by
  simp only [polygonDisjointTable,MonoidHom.comp_apply,MonoidHom.noncommPiCoprod_mulSingle,
    actualPolygonTableHom_input]

end DisjointPolygonAtoms

section AxisCutAtoms
namespace AxisCutSequence
variable {n K : ℕ} (D : AxisCutSequence n K)
    {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)
    (hlen : ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1)
    (hc : ∀ i j : ℕ, i ≤ j → ∀ x y,
      Commute (D.prefixCopy B hlarge g d i x) (D.suffix B hlarge g d j y))

noncomputable def atomCopy (i : Fin K) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  cutDifference (D.anchorCopy B hlarge g d) (D.prefixCopy B hlarge g d)
    (D.suffix B hlarge g d) (D.prefix_suffix B hlarge g d hlen) hc i.val

noncomputable def atomPolygon (i : Fin K) : polygonAlgebra a :=
  coordinateInterval a d (D.cut i.castSucc) (D.cut i.succ)

end AxisCutSequence
end AxisCutAtoms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SortedAxisCuts
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
section SortedAxisCuts
attribute [local instance] cutOrdinaryOrder

noncomputable def labelLift (u : CutRing) (q : ℤ) : CutRing :=
  u+cutFraction ((q:CutRing)*cutTau-u)

@[simp] theorem endpointLabel_labelLift (u : CutRing) (q : ℤ) : endpointLabel (labelLift u q)=q := by
  simp [labelLift,endpointLabel_add,endpointLabel_sub]

end SortedAxisCuts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AxisAnchorFamily
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
section AxisAnchorFamily

structure AxisAnchorFamily (n l : ℕ) (q : ℤ) where
  count : Fin l → ℕ
  cuts : ∀ i, AxisCutSequence n (count i)
  lower : ∀ i, (cuts i).cut 0 = windowCut l q i.castSucc
  upper : ∀ i, (cuts i).cut (Fin.last (count i)) = windowCut l q i.succ

namespace AxisAnchorFamily
variable {n l : ℕ} {q : ℤ} (A : AxisAnchorFamily n l q)

theorem intervalLength (hl : 201 ≤ l) (i : Fin l) :
    ordinary ((A.cuts i).cut (Fin.last (A.count i)))-ordinary ((A.cuts i).cut 0) < 1 := by
  rw [A.lower,A.upper]
  have hl' : (200:ℝ) < l := by exact_mod_cast (show 200 < l by omega)
  exact (windowCut_mesh l q i).trans_lt ((div_lt_one (by linarith)).mpr hl')

end AxisAnchorFamily
end AxisAnchorFamily

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SectorDifferenceRange
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

section AnchorGeneration
namespace AxisAnchorFamily
variable {n l : ℕ} {q : ℤ} (A : AxisAnchorFamily n l q)
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

noncomputable def prefixGroup : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  ⨆ i : Fin l, ⨆ j : Fin (A.count i+1), ((A.cuts i).prefixCopy B hlarge g d j.val).range

end AxisAnchorFamily
end AnchorGeneration

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

noncomputable def alphabetStarLift (I : FiveAlphabet α) (s : alternatingGroup I.val) :
    TrackStar α := universalMap (subtypeAlternatingHom I.val)
      (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))

@[simp] theorem alphabetStarLift_projection (I : FiveAlphabet α) (s : alternatingGroup I.val) :
    universalProjection (alternatingGroup α) (alphabetStarLift I s)=subtypeAlternatingHom I.val s := by
  have h := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val))
    (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))
  simpa only [MonoidHom.comp_apply,alphabetStarLift,
    Classical.choose_spec (universalProjection_surjective (alternatingGroup I.val) s)] using h

end SmallStarRelators

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClosedChartOverlap
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

section FullTangentOverlap

noncomputable def orderedCutMax (x y : CutRing) : CutRing :=
  if ordinary x ≤ ordinary y then y else x
noncomputable def orderedCutMin (x y : CutRing) : CutRing :=
  if ordinary x ≤ ordinary y then x else y

@[simp] theorem ordinary_orderedCutMax (x y : CutRing) :
    ordinary (orderedCutMax x y) = max (ordinary x) (ordinary y) := by
  unfold orderedCutMax
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

@[simp] theorem ordinary_orderedCutMin (x y : CutRing) :
    ordinary (orderedCutMin x y) = min (ordinary x) (ordinary y) := by
  unfold orderedCutMin
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

end FullTangentOverlap

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ClippedLineSlide
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
section ClippedLineSlide

noncomputable def tangentCoefficient (a : ℕ) (d j : Fin 2) : ℝ :=
  ordinary (pointCoordinate (tangentOffset a d 1) j)

@[simp] theorem tangentOffset_coordinate (a : ℕ) (d j : Fin 2) (x : CutRing) :
    ordinary (pointCoordinate (tangentOffset a d x) j) = tangentCoefficient a d j*ordinary x := by
  fin_cases d <;> fin_cases j <;> simp [tangentCoefficient,pointCoordinate,tangentOffset]

end ClippedLineSlide

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_ConcurrentDenominators
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
section ConcurrentDenominators

noncomputable def lineNormal (a : ℕ) (j : Fin 4) : CutRing × CutRing :=
  ![(1,0),(0,1),(-(cutTau^a),1),(1,-(cutTau^a))] j

noncomputable def lineDet (a : ℕ) (i j : Fin 4) : CutRing :=
  (lineNormal a i).1*(lineNormal a j).2-(lineNormal a j).1*(lineNormal a i).2

theorem cutForm_normal (a : ℕ) (j : Fin 4) (z : ℝ × ℝ) :
    cutForm a j z = ordinary (lineNormal a j).1*z.1+ordinary (lineNormal a j).2*z.2 := by
  fin_cases j <;> simp [cutForm,lineNormal] <;> ring

theorem lineDet_ne_zero {a : ℕ} (ha : 0<a) (i j : Fin 4) (hij : i ≠ j) :
    lineDet a i j ≠ 0 := by
  have hp : 1 < ordinary (cutTau^a) := by
    simpa using one_lt_pow₀ Real.one_lt_goldenRatio (show a≠0 by omega)
  have hn : cutTau^a ≠ 0 := by
    intro he; have hh := congrArg ordinary he; simp only [map_zero] at hh; linarith
  have hm : 1-cutTau^a*cutTau^a ≠ 0 := by
    intro he; have hh := congrArg ordinary he
    simp only [map_sub,map_one,map_mul,map_zero] at hh
    nlinarith
  have hm' : cutTau^a*cutTau^a-1 ≠ 0 := by
    intro he; apply hm; linear_combination -he
  fin_cases i <;> fin_cases j <;>
    simp_all [lineDet,lineNormal]

theorem intersection_pair_denominator (a : ℕ) (i j : Fin 4)
    (c d : CutRing) (z : ℝ × ℝ)
    (hi : cutForm a i z = ordinary c) (hj : cutForm a j z = ordinary d) :
    ∃ u v : CutRing,
      ordinary u=((QuadraticAlgebra.norm (lineDet a i j) : ℤ) : ℝ)*z.1 ∧
      ordinary v=((QuadraticAlgebra.norm (lineDet a i j) : ℤ) : ℝ)*z.2 := by
  let δ := lineDet a i j
  let x := c*(lineNormal a j).2-d*(lineNormal a i).2
  let y := (lineNormal a i).1*d-(lineNormal a j).1*c
  have hx : ordinary x=ordinary δ*z.1 := by
    rw [cutForm_normal] at hi hj
    simp only [x,δ,lineDet,map_sub,map_mul]
    linear_combination -(ordinary (lineNormal a j).2)*hi+(ordinary (lineNormal a i).2)*hj
  have hy : ordinary y=ordinary δ*z.2 := by
    rw [cutForm_normal] at hi hj
    simp only [y,δ,lineDet,map_sub,map_mul]
    linear_combination -(ordinary (lineNormal a i).1)*hj+(ordinary (lineNormal a j).1)*hi
  refine ⟨x*star δ,y*star δ,?_,?_⟩ <;>
    simp only [map_mul,hx,hy,← conjugate_eq_ordinary_star]
  · rw [← cut_norm_identity δ]; ring
  · rw [← cut_norm_identity δ]; ring

noncomputable def commonVertexDenominator (a : ℕ) : ℕ :=
  (∏ i : Fin 4, ∏ j : Fin 4,
    if i=j then (1 : ℤ) else QuadraticAlgebra.norm (lineDet a i j)).natAbs

theorem commonVertexDenominator_pos {a : ℕ} (ha : 0<a) : 0 < commonVertexDenominator a := by
  apply Int.natAbs_pos.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split_ifs with h
  · norm_num
  · exact cut_norm_nonzero (lineDet_ne_zero ha i j h)

theorem pair_norm_dvd_vertexDenominator (a : ℕ) (i j : Fin 4) (hij : i≠j) :
    QuadraticAlgebra.norm (lineDet a i j) ∣ (commonVertexDenominator a : ℤ) := by
  apply Int.dvd_natAbs.mpr
  have hi := Finset.dvd_prod_of_mem
    (fun i : Fin 4 => ∏ j : Fin 4, if i=j then (1 : ℤ) else QuadraticAlgebra.norm (lineDet a i j))
    (Finset.mem_univ i)
  have hj := Finset.dvd_prod_of_mem
    (fun j : Fin 4 => if i=j then (1 : ℤ) else QuadraticAlgebra.norm (lineDet a i j))
    (Finset.mem_univ j)
  have hh : QuadraticAlgebra.norm (lineDet a i j) ∣
      ∏ j : Fin 4, if i=j then (1 : ℤ) else QuadraticAlgebra.norm (lineDet a i j) := by
    simpa only [ite_eq_right hij] using hj
  exact hh.trans hi

theorem all_intersections_common_denominator {a : ℕ} (_ha : 0<a)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing) (z : ℝ × ℝ)
    (hi : cutForm a i z = ordinary c) (hj : cutForm a j z = ordinary d) :
    ∃ u v : CutRing,
      ordinary u=(commonVertexDenominator a : ℝ)*z.1 ∧
      ordinary v=(commonVertexDenominator a : ℝ)*z.2 := by
  obtain ⟨u,v,hu,hv⟩ := intersection_pair_denominator a i j c d z hi hj
  obtain ⟨k,hk⟩ := pair_norm_dvd_vertexDenominator a i j hij
  have hkr : (commonVertexDenominator a : ℝ)=
      ((QuadraticAlgebra.norm (lineDet a i j) : ℤ) : ℝ)*(k : ℝ) := by exact_mod_cast hk
  refine ⟨(k : CutRing)*u,(k : CutRing)*v,?_,?_⟩ <;>
    simp only [map_mul,map_intCast,hu,hv,hkr] <;> ring

end ConcurrentDenominators

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentAnchors
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
section ConcurrentAnchors

def AllowableVertexLine (a : ℕ) (z : ℝ × ℝ) (j : Fin 4) : Prop :=
  ∃ c : CutRing, cutForm a j z=ordinary c

end ConcurrentAnchors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_VaryingCellClassification
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
section VaryingCellClassification

@[simp] theorem integralCutForm_axis (a : ℕ) (j : Fin 2) (u : CutRing × CutRing) :
    integralCutForm a (axisDirection j) u=pointCoordinate u j := by
  fin_cases j <;> rfl

@[simp] theorem cutForm_axis (a : ℕ) (j : Fin 2) (z : ℝ × ℝ) :
    cutForm a (axisDirection j) z=realCoordinate z j := by
  fin_cases j <;> rfl

end VaryingCellClassification

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CrossingCellActions
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
section CrossingCellActions

@[simp] theorem integralCutForm_neg (a : ℕ) (j : Fin 4) (z : CutRing × CutRing) :
    integralCutForm a j (-z) = -integralCutForm a j z := by
  fin_cases j <;> simp [integralCutForm] <;> ring

end CrossingCellActions

section LocalPatchTemplates
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι J : Type*}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

structure LocalPatchTemplate (hlarge : 15 < m+1)
    (F : Option ι → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)) where
  index : Type
  [finite_index : Finite index]
  tests : index → Fin 5 × (CutRing × CutRing)
  lawful : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb tests
  margin : polygonAlgebra a
  predicates : ι → polygonAlgebra a
  margin_resolved : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) tests i).val) margin.val
  predicates_resolved : ∀ j, ResolvedBy (fun i => (primitiveTests (a := a) (r := r) tests i).val) (predicates j).val
  controlled : ∀ j, SmallControlled B.c (f j) (B.fullGeometricSector hlarge tests lawful margin)
  action : ∀ i (I : FiveAlphabet (Fin (m+1))) s j, ∀ x ∈ (f j).range,
    F (some i) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (F (some i) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector hlarge tests lawful (predicates i)
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector hlarge tests lawful (predicates i)
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹

attribute [instance] LocalPatchTemplate.finite_index

end InitialCoverSystem
end LocalPatchTemplates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteArrangementGerms
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
section FiniteArrangementGerms

theorem avoidsCuts_rectangle (a : ℕ) (l₁ r₁ l₂ r₂ : ℝ)
    (h₁ : l₁ < r₁) (h₂ : l₂ < r₂) :
    ∃ p : ℝ × ℝ, p.1 ∈ Set.Ioo l₁ r₁ ∧ p.2 ∈ Set.Ioo l₂ r₂ ∧ AvoidsCuts a p := by
  obtain ⟨x, hx, hx'⟩ := exists_interval_avoiding_countable l₁ r₁ h₁
    (Set.range ordinary) (Set.countable_range ordinary)
  let t := Real.goldenRatio ^ a
  have ht : t ≠ 0 := ne_of_gt (pow_pos Real.goldenRatio_pos a)
  let S := Set.range ordinary ∪ Set.range (fun z : CutRing => ordinary z + t*x) ∪
    Set.range (fun z : CutRing => (x - ordinary z)/t)
  have hS : S.Countable := ((Set.countable_range ordinary).union
    (Set.countable_range _)).union (Set.countable_range _)
  obtain ⟨y, hy, hy'⟩ := exists_interval_avoiding_countable l₂ r₂ h₂ S hS
  have hav : AvoidsCuts a (x,y) := by
    intro j z hz
    fin_cases j
    · exact hx' ⟨z, by simpa [cutForm] using hz.symm⟩
    · apply hy'
      exact Or.inl (Or.inl ⟨z, by simpa [cutForm] using hz.symm⟩)
    · apply hy'
      apply Or.inl ∘ Or.inr
      refine ⟨z, ?_⟩
      change ordinary z + t*x = y
      change y - t*x = ordinary z at hz
      linarith
    · apply hy'
      apply Or.inr
      refine ⟨z, ?_⟩
      apply (div_eq_iff ht).mpr
      change x - t*y = ordinary z at hz
      linarith
  exact ⟨(x,y),hx,hy,hav⟩

theorem avoidsCuts_dense (a : ℕ) : Dense {p : ℝ × ℝ | AvoidsCuts a p} := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨z,hz⟩
  obtain ⟨l,h,hl,hsub⟩ := exists_box_in_open hU z hz
  obtain ⟨p,hp₁,hp₂,hp⟩ := avoidsCuts_rectangle a
    (ordinary l.1) (ordinary h.1) (ordinary l.2) (ordinary h.2)
    (hl.1.1.trans hl.1.2) (hl.2.1.trans hl.2.2)
  exact ⟨p,hsub ⟨hp₁,hp₂⟩,hp⟩

theorem cutForm_smul (a : ℕ) (j : Fin 4) (t : ℝ) (p : ℝ × ℝ) :
    cutForm a j (t • p) = t * cutForm a j p := by
  fin_cases j <;> simp [cutForm] <;> ring

def strictLineCell {ι : Type*} (a : ℕ) (j : ι → Fin 4) (c : ι → ℝ)
    (σ : ι → Bool) : Set (ℝ × ℝ) :=
  {p | ∀ i, if σ i then cutForm a (j i) p < c i else c i < cutForm a (j i) p}

theorem strictLineCell_open {ι : Type*} [Finite ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → ℝ) (σ : ι → Bool) :
    IsOpen (strictLineCell a j c σ) := by
  classical
  have he : strictLineCell a j c σ = ⋂ i, {p | if σ i then cutForm a (j i) p < c i else c i < cutForm a (j i) p} := by
    ext p; simp only [strictLineCell,Set.mem_ofPred_eq,Set.mem_iInter]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  cases σ i
  · exact isOpen_lt continuous_const (cutForm_continuous a (j i))
  · exact isOpen_lt (cutForm_continuous a (j i)) continuous_const

theorem finite_arrangement_germ {ι : Type*} [Finite ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → ℝ) (z y : ℝ × ℝ) (σ : ι → Bool)
    (hactive : ∀ i, cutForm a (j i) z=c i →
      if σ i then cutForm a (j i) y < c i else c i < cutForm a (j i) y)
    (hinactive : ∀ i, cutForm a (j i) z≠c i →
      if σ i then cutForm a (j i) z < c i else c i < cutForm a (j i) z)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ p ∈ N, p ∈ strictLineCell a j c σ ∧ AvoidsCuts a p := by
  classical
  let U : Set (ℝ × ℝ) := N ∩ ⋂ i, if cutForm a (j i) z=c i then Set.univ
    else {p | if σ i then cutForm a (j i) p < c i else c i < cutForm a (j i) p}
  have hU : IsOpen U := by
    apply hN.inter
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : cutForm a (j i) z=c i
    · rw [ite_eq_left hi]; exact isOpen_univ
    · rw [ite_eq_right hi]
      cases σ i
      · exact isOpen_lt continuous_const (cutForm_continuous a (j i))
      · exact isOpen_lt (cutForm_continuous a (j i)) continuous_const
  have hzU : z ∈ U := by
    refine ⟨hz,Set.mem_iInter.mpr fun i => ?_⟩
    by_cases hi : cutForm a (j i) z=c i
    · rw [ite_eq_left hi]; trivial
    · rw [ite_eq_right hi]; exact hinactive i hi
  let ray : ℝ → ℝ × ℝ := fun t => z+t • (y-z)
  have hray : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
  have he : ray ⁻¹' U ∈ nhds (0:ℝ) := by
    apply hray.continuousAt.preimage_mem_nhds
    simpa [ray] using hU.mem_nhds hzU
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp he
  let t := ε/2
  have ht : 0<t := by dsimp [t]; positivity
  have htU : ray t ∈ U := hεU (by
    change dist t 0 < ε
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    dsimp [t]; linarith)
  have hcell : ray t ∈ strictLineCell a j c σ := by
    intro i
    by_cases hi : cutForm a (j i) z=c i
    · have ha := hactive i hi
      have heq : cutForm a (j i) (ray t)=c i+t*(cutForm a (j i) y-c i) := by
        simp only [ray,cutForm_add,cutForm_smul,cutForm_sub,hi]
      cases hσ : σ i <;> simp only [hσ,Bool.false_eq_true,↓reduceIte] at ha ⊢
      · rw [heq]; nlinarith
      · rw [heq]; nlinarith
    · have hh := Set.mem_iInter.mp htU.2 i
      simpa only [ite_eq_right hi,Set.mem_ofPred_eq] using hh
  obtain ⟨p,hp,hpg⟩ := (avoidsCuts_dense a).inter_open_nonempty
    (N ∩ strictLineCell a j c σ) (hN.inter (strictLineCell_open a j c σ))
    ⟨ray t,htU.1,hcell⟩
  exact ⟨p,hp.1,hp.2,hpg⟩

end FiniteArrangementGerms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_RoutingIndependence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

noncomputable def orderedOffsets {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (u : Fin 5 → CutRing × CutRing) : Fin m → CutRing × CutRing :=
  Function.extend ι u 0

@[simp] theorem orderedOffsets_apply {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (u : Fin 5 → CutRing × CutRing) (j : Fin 5) : orderedOffsets ι u (ι j)=u j :=
  ι.injective.extend_apply u 0 j

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

noncomputable def orbitRepresentative (u : CutRing × CutRing) : CutRing × CutRing :=
  ((u.1.im : CutRing)*cutTau,(u.2.im : CutRing)*cutTau)

theorem cut_im_eq_of_fract_eq (x : ℝ) (u v : CutRing)
    (he : Int.fract (x+ordinary u)=Int.fract (x+ordinary v)) : u.im=v.im := by
  obtain ⟨n,hn⟩ := Int.fract_eq_fract.mp he
  have huv : u-v=(n : CutRing) := by
    apply ordinary_injective
    simp only [map_sub,map_intCast]
    linarith
  have him : u.im-v.im=0 := by simpa using congrArg (fun z : CutRing => z.im) huv
  omega

theorem orbitRepresentative_eq_of_translate_eq {a : ℕ} {u v : CutRing × CutRing}
    (x : GenericSquare a) (he : translate a u x=translate a v x) :
    orbitRepresentative u=orbitRepresentative v := by
  have hx := congrArg (fun p : GenericSquare a => p.val.1) he
  have hy := congrArg (fun p : GenericSquare a => p.val.2) he
  have hu := cut_im_eq_of_fract_eq x.val.1 u.1 v.1 hx
  have hv := cut_im_eq_of_fract_eq x.val.2 u.2 v.2 hy
  simp only [orbitRepresentative,hu,hv]

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierCells
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
section BarrierCells
open Classical Set

noncomputable def arrangementAtom {ι : Type*} [Fintype ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → CutRing) (σ : ι → Bool) : polygonAlgebra a :=
  Finset.univ.inf (fun i => if σ i then ⟨halfPlane a (j i) (c i),halfPlane_mem _ _ _⟩
    else (⟨halfPlane a (j i) (c i),halfPlane_mem _ _ _⟩ : polygonAlgebra a)ᶜ)

noncomputable def arrangementPattern {ι : Type*} (a : ℕ)
    (j : ι → Fin 4) (c : ι → CutRing) (p : GenericSquare a) : ι → Bool :=
  fun i => decide (cutForm a (j i) p.val<ordinary (c i))

theorem generic_mem_squareInterior {a : ℕ} (p : GenericSquare a) : p.val∈squareInterior :=
  ⟨⟨(generic_coordinates_pos p).1,p.property.1.2⟩,
    ⟨(generic_coordinates_pos p).2,p.property.2.1.2⟩⟩

def SupportedBarriers {ι : Type*} (a : ℕ) (j : ι → Fin 4) (c : ι → CutRing)
    (B : Set (ℝ×ℝ)) : Prop :=
  ∀p∈B,∃i,cutForm a (j i) p=ordinary (c i)

noncomputable def barrierComponentCell {a : ℕ} (B : Set (ℝ×ℝ)) (x : ℝ×ℝ) :
    Set (GenericSquare a) := {p | p.val∈connectedComponentIn (barrierRegion B) x}

end BarrierCells

section BarrierPartitions
open Classical Set

structure FinitePolygonPartition (a : ℕ) where
  cells : Finset (polygonAlgebra a)
  nonempty : ∀C∈cells,C.val.Nonempty
  cover : ∀p : GenericSquare a,∃! C,C∈cells ∧ p∈C.val

end BarrierPartitions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_QuadraticRectangleCounts
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
section QuadraticRectangleCounts
open Classical

theorem conjugateStrip_floor_inj (y b : ℝ) (hb : 0<b) :
    Set.InjOn (fun u : CutRing => ⌊b*ordinary u⌋)
      {u | conjugate u∈Set.Icc y (y+b)} := by
  intro u hu w hw he
  change ⌊b*ordinary u⌋=⌊b*ordinary w⌋ at he
  by_contra hne
  have hn := one_le_abs_cut_norm (sub_ne_zero.mpr hne)
  simp only [map_sub,abs_mul] at hn
  have hc : |conjugate u-conjugate w|≤b := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1,hu.2,hw.1,hw.2]
  have h₁ := Int.floor_le (b*ordinary u)
  have h₂ := Int.lt_floor_add_one (b*ordinary u)
  have h₃ := Int.floor_le (b*ordinary w)
  have h₄ := Int.lt_floor_add_one (b*ordinary w)
  rw [he] at h₁ h₂
  have hlt : |b*(ordinary u-ordinary w)|<1 := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  rw [abs_mul,abs_of_pos hb] at hlt
  nlinarith [abs_nonneg (ordinary u-ordinary w)]

def cutRectangle (x y a b : ℝ) : Set CutRing :=
  {u | ordinary u∈Set.Icc x (x+a) ∧ conjugate u∈Set.Icc y (y+b)}

theorem cutRectangle_finite (x y a b : ℝ) (hb : 0<b) : (cutRectangle x y a b).Finite := by
  have him : ((fun u : CutRing => ⌊b*ordinary u⌋) '' cutRectangle x y a b).Finite := by
    apply (Set.finite_Icc ⌊b*x⌋ ⌊b*(x+a)⌋).subset
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨Int.floor_mono (mul_le_mul_of_nonneg_left hu.1.1 hb.le),
      Int.floor_mono (mul_le_mul_of_nonneg_left hu.1.2 hb.le)⟩
  exact him.of_finite_image (fun _ hu _ hw he =>
    conjugateStrip_floor_inj y b hb hu.2 hw.2 he)

end QuadraticRectangleCounts

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

def GenericPlane (a : ℕ) := {p : ℝ × ℝ // AvoidsCuts a p}

namespace GenericPlane
noncomputable def shift {a : ℕ} (u : CutRing × CutRing) (p : GenericPlane a) :
    GenericPlane a := ⟨p.val+(ordinary u.1,ordinary u.2),avoidsCuts_translate p.property u⟩
@[simp] theorem shift_zero {a : ℕ} (p : GenericPlane a) : shift 0 p=p := by
  apply Subtype.ext
  simp [shift]
@[simp] theorem shift_add {a : ℕ} (u v : CutRing × CutRing) (p : GenericPlane a) :
    shift u (shift v p)=shift (u+v) p := by
  apply Subtype.ext
  simp only [shift,Prod.fst_add,Prod.snd_add,map_add]
  ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> ring
end GenericPlane

abbrev PlaneCut := Fin 4 × CutRing

noncomputable def planeSign {a : ℕ} (l : PlaneCut) (p : GenericPlane a) : Bool :=
  decide (cutForm a l.1 p.val < ordinary l.2)

def HasPlaneArrangement {a : ℕ} (f : GenericPlane a → ℤ) : Prop :=
  ∃ S : Finset PlaneCut, ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f p=f q

def PlaneCompactSupport {a : ℕ} (f : GenericPlane a → ℤ) : Prop :=
  ∃ R : ℝ, ∀ p, R < |p.val.1| ∨ R < |p.val.2| → f p=0

noncomputable def planeStepSubmodule (a : ℕ) : Submodule ℤ (GenericPlane a → ℤ) where
  carrier := {f | HasPlaneArrangement f ∧ PlaneCompactSupport f}
  zero_mem' := by
    refine ⟨⟨∅,fun _ _ _ => rfl⟩,⟨0,fun _ _ => rfl⟩⟩
  add_mem' := by
    classical
    rintro f g ⟨⟨S,hS⟩,⟨R,hR⟩⟩ ⟨⟨T,hT⟩,⟨Q,hQ⟩⟩
    constructor
    · refine ⟨S∪T,fun p q hpq => ?_⟩
      exact congrArg₂ (·+·) (hS p q (fun l hl => hpq l (Finset.mem_union_left T hl)))
        (hT p q (fun l hl => hpq l (Finset.mem_union_right S hl)))
    · refine ⟨max R Q,fun p hp => ?_⟩
      have h₁ : R < |p.val.1| ∨ R < |p.val.2| := hp.imp
        (lt_of_le_of_lt (le_max_left _ _)) (lt_of_le_of_lt (le_max_left _ _))
      have h₂ : Q < |p.val.1| ∨ Q < |p.val.2| := hp.imp
        (lt_of_le_of_lt (le_max_right _ _)) (lt_of_le_of_lt (le_max_right _ _))
      change f p+g p=0
      rw [hR p h₁,hQ p h₂,add_zero]
  smul_mem' := by
    rintro c f ⟨⟨S,hS⟩,⟨R,hR⟩⟩
    refine ⟨⟨S,fun p q hpq => congrArg (c • ·) (hS p q hpq)⟩,⟨R,fun p hp => ?_⟩⟩
    change c • f p=0
    rw [hR p hp,smul_zero]

noncomputable abbrev PlaneStep (a : ℕ) : Type := ↥(planeStepSubmodule a)

namespace PlaneStep
variable {a : ℕ}

theorem hasArrangement (f : PlaneStep a) : HasPlaneArrangement f.val := f.property.1
theorem compactSupport (f : PlaneStep a) : PlaneCompactSupport f.val := f.property.2

@[simp] theorem translated_sign (l : PlaneCut) (u : CutRing × CutRing)
    (p : GenericPlane a) : planeSign l (GenericPlane.shift (-u) p)=
      planeSign (l.1,l.2+integralCutForm a l.1 u) p := by
  unfold planeSign
  apply decide_eq_decide.mpr
  have he : integralCutForm a l.1 (-u) = -integralCutForm a l.1 u := by
    rcases l with ⟨j,c⟩
    fin_cases j <;> simp [integralCutForm] <;> ring
  simp only [GenericPlane.shift,cutForm_add,cutForm_ordinary,he,map_neg,map_add]
  constructor <;> intro h <;> linarith

theorem translated_arrangement (f : PlaneStep a) (u : CutRing × CutRing) :
    HasPlaneArrangement (fun p => f.val (GenericPlane.shift (-u) p)) := by
  classical
  obtain ⟨S,hS⟩ := hasArrangement f
  refine ⟨S.image (fun l => (l.1,l.2+integralCutForm a l.1 u)),fun p q hpq => ?_⟩
  apply hS
  intro l hl
  rw [translated_sign,translated_sign]
  exact hpq _ (Finset.mem_image_of_mem _ hl)

theorem translated_compact (f : PlaneStep a) (u : CutRing × CutRing) :
    PlaneCompactSupport (fun p => f.val (GenericPlane.shift (-u) p)) := by
  obtain ⟨R,hR⟩ := compactSupport f
  refine ⟨R + |ordinary u.1|+|ordinary u.2|,fun p hp => ?_⟩
  apply hR
  have h₁ : |p.val.1| ≤ |p.val.1-ordinary u.1|+|ordinary u.1| := by
    simpa using abs_add_le (p.val.1-ordinary u.1) (ordinary u.1)
  have h₂ : |p.val.2| ≤ |p.val.2-ordinary u.2|+|ordinary u.2| := by
    simpa using abs_add_le (p.val.2-ordinary u.2) (ordinary u.2)
  change R < |p.val.1+ordinary (-u).1| ∨ R < |p.val.2+ordinary (-u).2|
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg]
  rcases hp with hp|hp
  · left; linarith [abs_nonneg (ordinary u.2)]
  · right; linarith [abs_nonneg (ordinary u.1)]

noncomputable def translate (u : CutRing × CutRing) : PlaneStep a →ₗ[ℤ] PlaneStep a where
  toFun f := ⟨fun p => f.val (GenericPlane.shift (-u) p),
    translated_arrangement f u,translated_compact f u⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem translate_apply (u : CutRing × CutRing) (f : PlaneStep a) (p : GenericPlane a) :
    (translate u f).val p=f.val (GenericPlane.shift (-u) p) := rfl

end PlaneStep

end PlaneStepFunctions

section PlaneArrangementGerms

open Classical

def TransverseDirection (a : ℕ) (v : ℝ × ℝ) : Prop :=
  ∀ j : Fin 4, cutForm a j v ≠ 0

noncomputable def planeSector (a : ℕ) (z v : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ j : Fin 4, if cutForm a j v < 0 then cutForm a j p < cutForm a j z
      else cutForm a j z < cutForm a j p}

theorem planeSector_generic {a : ℕ} {z v : ℝ × ℝ} (hv : TransverseDirection a v)
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hz : z∈N) :
    ∃ p : GenericPlane a, p.val∈N ∧ p.val∈planeSector a z v := by
  let σ : Fin 4 → Bool := fun j => decide (cutForm a j v < 0)
  have hactive (j : Fin 4) (_ : cutForm a j z=cutForm a j z) :
      if σ j then cutForm a j (z+v) < cutForm a j z
      else cutForm a j z < cutForm a j (z+v) := by
    simp only [σ,cutForm_add]
    split_ifs with h
    · have : cutForm a j v<0 := of_decide_eq_true h
      linarith
    · have hh : 0 < cutForm a j v := lt_of_le_of_ne
        (le_of_not_gt (of_decide_eq_false (Bool.eq_false_iff.mpr h))) (hv j).symm
      linarith
  obtain ⟨p,hp,hσ,hpg⟩ := finite_arrangement_germ a id (fun j => cutForm a j z)
    z (z+v) σ hactive (fun _ hh => (hh rfl).elim) N hN hz
  refine ⟨⟨p,hpg⟩,hp,?_⟩
  intro j
  have hh := hσ j
  simpa [σ] using hh

noncomputable def arrangementNeighborhood (a : ℕ) (S : Finset PlaneCut) (z : ℝ × ℝ) :
    Set (ℝ × ℝ) := ⋂ l∈S, if cutForm a l.1 z=ordinary l.2 then Set.univ
      else if cutForm a l.1 z<ordinary l.2 then {p | cutForm a l.1 p<ordinary l.2}
      else {p | ordinary l.2 < cutForm a l.1 p}

theorem arrangementNeighborhood_open (a : ℕ) (S : Finset PlaneCut) (z : ℝ × ℝ) :
    IsOpen (arrangementNeighborhood a S z) := by
  apply isOpen_biInter_finset
  intro l hl
  split_ifs
  · exact isOpen_univ
  · exact isOpen_lt (cutForm_continuous a l.1) continuous_const
  · exact isOpen_lt continuous_const (cutForm_continuous a l.1)

theorem self_mem_arrangementNeighborhood (a : ℕ) (S : Finset PlaneCut) (z : ℝ × ℝ) :
    z∈arrangementNeighborhood a S z := by
  apply Set.mem_iInter₂.mpr
  intro l hl
  split_ifs with he ht
  · trivial
  · exact ht
  · exact lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm he)

theorem planeSign_neighborhood {a : ℕ} {S : Finset PlaneCut} {z v : ℝ × ℝ}
    {p : GenericPlane a} (hN : p.val∈arrangementNeighborhood a S z)
    (hv : p.val∈planeSector a z v) {l : PlaneCut} (hl : l∈S) :
    planeSign l p=decide (if cutForm a l.1 z=ordinary l.2 then cutForm a l.1 v<0
      else cutForm a l.1 z<ordinary l.2) := by
  unfold planeSign
  apply decide_eq_decide.mpr
  by_cases he : cutForm a l.1 z=ordinary l.2
  · rw [ite_eq_left he]
    have hh := hv l.1
    rw [he] at hh
    by_cases ht : cutForm a l.1 v<0
    · rw [ite_eq_left ht] at hh
      exact iff_of_true hh ht
    · rw [ite_eq_right ht] at hh
      exact iff_of_false (not_lt_of_gt hh) ht
  · rw [ite_eq_right he]
    have hh := Set.mem_iInter₂.mp hN l hl
    rw [ite_eq_right he] at hh
    by_cases ht : cutForm a l.1 z<ordinary l.2
    · rw [ite_eq_left ht] at hh
      exact iff_of_true hh ht
    · rw [ite_eq_right ht] at hh
      exact iff_of_false (not_lt_of_gt hh) ht

def IsPlaneGerm {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ) (n : ℤ) : Prop :=
  ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z∈N ∧
    ∀ p : GenericPlane a, p.val∈N → p.val∈planeSector a z v → f.val p=n

theorem exists_planeGerm {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ)
    (hv : TransverseDirection a v) : ∃ n : ℤ, IsPlaneGerm f z v n := by
  obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
  obtain ⟨p,hp,hpv⟩ := planeSector_generic hv (arrangementNeighborhood_open a S z)
    (self_mem_arrangementNeighborhood a S z)
  refine ⟨f.val p,arrangementNeighborhood a S z,arrangementNeighborhood_open a S z,
    self_mem_arrangementNeighborhood a S z,fun q hq hqv => ?_⟩
  apply hS
  intro l hl
  rw [planeSign_neighborhood hq hqv hl,planeSign_neighborhood hp hpv hl]

theorem IsPlaneGerm.unique {a : ℕ} {f : PlaneStep a} {z v : ℝ × ℝ} {m n : ℤ}
    (hv : TransverseDirection a v) (hm : IsPlaneGerm f z v m) (hn : IsPlaneGerm f z v n) :
    m=n := by
  obtain ⟨N,hN,hz,hf⟩ := hm
  obtain ⟨M,hM,hz',hg⟩ := hn
  obtain ⟨p,hp,hpv⟩ := planeSector_generic hv (hN.inter hM) ⟨hz,hz'⟩
  exact (hf p hp.1 hpv).symm.trans (hg p hp.2 hpv)

noncomputable def planeGerm {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ) : ℤ :=
  if hv : TransverseDirection a v then Classical.choose (exists_planeGerm f z v hv) else 0

theorem planeGerm_spec {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ)
    (hv : TransverseDirection a v) : IsPlaneGerm f z v (planeGerm f z v) := by
  rw [planeGerm,dite_eq_left hv]
  exact Classical.choose_spec (exists_planeGerm f z v hv)

theorem planeGerm_eq {a : ℕ} {f : PlaneStep a} {z v : ℝ × ℝ} {n : ℤ}
    (hv : TransverseDirection a v) (hn : IsPlaneGerm f z v n) : planeGerm f z v=n :=
  (planeGerm_spec f z v hv).unique hv hn

@[simp] theorem planeGerm_zero {a : ℕ} (z v : ℝ × ℝ) :
    planeGerm (0 : PlaneStep a) z v=0 := by
  by_cases hv : TransverseDirection a v
  · exact planeGerm_eq hv ⟨Set.univ,isOpen_univ,Set.mem_univ z,fun _ _ _ => rfl⟩
  · simp [planeGerm,hv]

@[simp] theorem planeGerm_add {a : ℕ} (f g : PlaneStep a) (z v : ℝ × ℝ) :
    planeGerm (f+g) z v=planeGerm f z v+planeGerm g z v := by
  by_cases hv : TransverseDirection a v
  · obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
    obtain ⟨M,hM,hz',hg⟩ := planeGerm_spec g z v hv
    apply planeGerm_eq hv
    refine ⟨N∩M,hN.inter hM,⟨hz,hz'⟩,fun p hp hpv => ?_⟩
    exact congrArg₂ (·+·) (hf p hp.1 hpv) (hg p hp.2 hpv)
  · simp [planeGerm,hv]

@[simp] theorem planeGerm_smul {a : ℕ} (c : ℤ) (f : PlaneStep a) (z v : ℝ × ℝ) :
    planeGerm (c • f) z v=c • planeGerm f z v := by
  by_cases hv : TransverseDirection a v
  · obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
    apply planeGerm_eq hv
    exact ⟨N,hN,hz,fun p hp hpv => congrArg (c • ·) (hf p hp hpv)⟩
  · simp [planeGerm,hv]

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

noncomputable def squareSign {a : ℕ} (l : PlaneCut) (p : GenericSquare a) : Bool :=
  decide (cutForm a l.1 p.val < ordinary l.2)

def HasSquareArrangement {a : ℕ} {K : Type*} (f : GenericSquare a → K) : Prop :=
  ∃ S : Finset PlaneCut, ∀ p q, (∀ l∈S, squareSign l p=squareSign l q) → f p=f q

theorem polygon_hasSquareArrangement {a : ℕ} {U : Set (GenericSquare a)}
    (hU : U ∈ polygonAlgebra a) : HasSquareArrangement (fun p => decide (p∈U)) := by
  refine polygon_induction (P := fun U => HasSquareArrangement (fun p => decide (p∈U)))
    ?_ ?_ ?_ ?_ hU
  · intro j z
    exact ⟨{(j,z)},fun p q h => h _ (Finset.mem_singleton_self _)⟩
  · exact ⟨∅,fun _ _ _ => rfl⟩
  · rintro U V ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S∪T,fun p q h => ?_⟩
    have h₁ := decide_eq_decide.mp (hS p q (fun l hl => h l (Finset.mem_union_left T hl)))
    have h₂ := decide_eq_decide.mp (hT p q (fun l hl => h l (Finset.mem_union_right S hl)))
    exact decide_eq_decide.mpr (or_congr h₁ h₂)
  · rintro U ⟨S,hS⟩
    refine ⟨S,fun p q h => ?_⟩
    exact decide_eq_decide.mpr (not_congr (decide_eq_decide.mp (hS p q h)))

theorem squareArrangement_precomp {a : ℕ} {K : Type*} {f : GenericSquare a → K}
    (hf : HasSquareArrangement f) (t : GenericSquare a → GenericSquare a)
    (ht : ∀ l, HasSquareArrangement (fun p => squareSign l (t p))) :
    HasSquareArrangement (f ∘ t) := by
  choose S hS using ht
  obtain ⟨T,hT⟩ := hf
  refine ⟨T.biUnion S,fun p q hpq => hT (t p) (t q) (fun l hl => ?_)⟩
  exact hS l p q (fun k hk => hpq k (Finset.mem_biUnion.mpr ⟨l,hl,hk⟩))

theorem squareArrangement_translate {a : ℕ} {K : Type*} {f : GenericSquare a → K}
    (hf : HasSquareArrangement f) (u : CutRing × CutRing) :
    HasSquareArrangement (fun p => f (translate a u p)) := by
  apply squareArrangement_precomp hf
  intro l
  exact polygon_hasSquareArrangement (polygon_preimage_translate u (halfPlane_mem a l.1 l.2))

noncomputable def squareStepSubmodule (a : ℕ) : Submodule ℤ (GenericSquare a → ℤ) where
  carrier := {f | HasSquareArrangement f}
  zero_mem' := ⟨∅,fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨S,hS⟩ ⟨T,hT⟩
    exact ⟨S∪T,fun p q h => congrArg₂ (·+·)
      (hS p q (fun l hl => h l (Finset.mem_union_left T hl)))
      (hT p q (fun l hl => h l (Finset.mem_union_right S hl)))⟩
  smul_mem' := by
    rintro c f ⟨S,hS⟩
    exact ⟨S,fun p q hpq => congrArg (c • ·) (hS p q hpq)⟩

noncomputable abbrev SquareStep (a : ℕ) := ↥(squareStepSubmodule a)

namespace SquareStep
variable {a : ℕ}

noncomputable def translate (u : CutRing × CutRing) : SquareStep a →ₗ[ℤ] SquareStep a where
  toFun f := ⟨fun p => f.val (SimpleAmenable.translate a (-u) p),
    squareArrangement_translate f.property (-u)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem translate_apply (u : CutRing × CutRing) (f : SquareStep a) (p : GenericSquare a) :
    (translate u f).val p = f.val (SimpleAmenable.translate a (-u) p) := rfl

@[simp] theorem translate_zero (f : SquareStep a) : translate 0 f=f := by
  apply Subtype.ext
  funext p
  simp

@[simp] theorem translate_add (u v : CutRing × CutRing) (f : SquareStep a) :
    translate (u+v) f=translate u (translate v f) := by
  apply Subtype.ext
  funext p
  simp only [translate_apply,neg_add_rev,SimpleAmenable.translate_add]

noncomputable def restrict : PlaneStep a →ₗ[ℤ] SquareStep a where
  toFun f := ⟨fun p => f.val ⟨p.val,p.property.2.2⟩,by
    obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
    exact ⟨S,fun p q hpq => hS ⟨p.val,p.property.2.2⟩ ⟨q.val,q.property.2.2⟩ hpq⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrict_apply (f : PlaneStep a) (p : GenericSquare a) :
    (restrict f).val p=f.val ⟨p.val,p.property.2.2⟩ := rfl

end SquareStep
end TorusStepFunctions

section SquareZeroExtension

open Classical
namespace SquareStep
variable {a : ℕ}

def InSquare (p : GenericPlane a) : Prop :=
  p.val.1 ∈ Set.Ico (0:ℝ) 1 ∧ p.val.2 ∈ Set.Ico (0:ℝ) 1

noncomputable def squareEdgeCuts : Finset PlaneCut := {(0,0),(0,1),(1,0),(1,1)}

theorem square_signs {p q : GenericPlane a}
    (h : ∀ l∈squareEdgeCuts, planeSign l p=planeSign l q) :
    InSquare p ↔ InSquare q := by
  have hx₀ : p.val.1 < 0 ↔ q.val.1 < 0 := by
    simpa [planeSign,cutForm] using decide_eq_decide.mp
      (h (0,0) (by simp [squareEdgeCuts]))
  have hx₁ : p.val.1 < 1 ↔ q.val.1 < 1 := by
    simpa [planeSign,cutForm] using decide_eq_decide.mp
      (h (0,1) (by simp [squareEdgeCuts]))
  have hy₀ : p.val.2 < 0 ↔ q.val.2 < 0 := by
    simpa [planeSign,cutForm] using decide_eq_decide.mp
      (h (1,0) (by simp [squareEdgeCuts]))
  have hy₁ : p.val.2 < 1 ↔ q.val.2 < 1 := by
    simpa [planeSign,cutForm] using decide_eq_decide.mp
      (h (1,1) (by simp [squareEdgeCuts]))
  have hx₀' := not_congr hx₀
  have hy₀' := not_congr hy₀
  simp only [not_lt] at hx₀' hy₀'
  exact and_congr (and_congr hx₀' hx₁) (and_congr hy₀' hy₁)

noncomputable def extendFun (f : SquareStep a) (p : GenericPlane a) : ℤ :=
  if h : InSquare p then f.val ⟨p.val,h.1,h.2,p.property⟩ else 0

theorem extend_arrangement (f : SquareStep a) : HasPlaneArrangement (extendFun f) := by
  obtain ⟨S,hS⟩ := f.property
  refine ⟨S∪squareEdgeCuts,fun p q hpq => ?_⟩
  have hiff := square_signs (fun l hl => hpq l (Finset.mem_union_right S hl))
  by_cases hp : InSquare p
  · have hq := hiff.mp hp
    simp only [extendFun,dite_eq_left hp,dite_eq_left hq]
    exact hS _ _ (fun l hl => hpq l (Finset.mem_union_left squareEdgeCuts hl))
  · have hq := mt hiff.mpr hp
    simp only [extendFun,dite_eq_right hp,dite_eq_right hq]

theorem extend_compact (f : SquareStep a) : PlaneCompactSupport (extendFun f) := by
  refine ⟨1,fun p hp => ?_⟩
  have hn : ¬ InSquare p := by
    rintro ⟨⟨hx,hx'⟩,⟨hy,hy'⟩⟩
    rw [abs_of_nonneg hx,abs_of_nonneg hy] at hp
    rcases hp with hp|hp <;> linarith
  exact dite_eq_right hn

noncomputable def extend : SquareStep a →ₗ[ℤ] PlaneStep a where
  toFun f := ⟨extendFun f,extend_arrangement f,extend_compact f⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    by_cases hp : InSquare p <;> simp [extendFun,hp]
    rfl
  map_smul' n f := by
    apply Subtype.ext
    funext p
    by_cases hp : InSquare p <;> simp [extendFun,hp]
    rfl

@[simp] theorem extend_apply (f : SquareStep a) (p : GenericPlane a) :
    (extend f).val p = extendFun f p := rfl

@[simp] theorem restrict_extend (f : SquareStep a) : restrict (extend f)=f := by
  apply Subtype.ext
  funext p
  exact dite_eq_left ⟨p.property.1,p.property.2.1⟩

noncomputable def intPair (n : ℤ × ℤ) : CutRing × CutRing := ((n.1:CutRing),(n.2:CutRing))

@[simp] theorem intPair_zero : intPair (0:ℤ×ℤ)=0 := by ext <;> simp [intPair]
@[simp] theorem intPair_add (n m : ℤ×ℤ) : intPair (n+m)=intPair n+intPair m := by
  ext <;> simp [intPair]
@[simp] theorem intPair_neg (n : ℤ×ℤ) : intPair (-n) = - intPair n := by
  ext <;> simp [intPair]

noncomputable def slice (n : ℤ×ℤ) : PlaneStep a →ₗ[ℤ] SquareStep a :=
  restrict.comp (PlaneStep.translate (-intPair n))

@[simp] theorem slice_apply (n : ℤ×ℤ) (f : PlaneStep a) (p : GenericSquare a) :
    (slice n f).val p=f.val (GenericPlane.shift (intPair n) ⟨p.val,p.property.2.2⟩) := by
  change f.val (GenericPlane.shift (- -intPair n) ⟨p.val,p.property.2.2⟩)=_
  rw [neg_neg]

@[simp] theorem slice_zero (f : PlaneStep a) : slice 0 f=restrict f := by
  apply Subtype.ext
  funext p
  rw [slice_apply]
  rw [intPair_zero]
  exact congrArg f.val (GenericPlane.shift_zero ⟨p.val,p.property.2.2⟩)

end SquareStep
end SquareZeroExtension

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagGerms
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
section FlagGerms
open Classical

def FlagDirections (a : ℕ) (v w : ℝ × ℝ) : Prop :=
  ∀ j : Fin 4, cutForm a j v ≠ 0 ∨ cutForm a j w ≠ 0

theorem flagDirections_sector {a : ℕ} {v w : ℝ×ℝ} (h : FlagDirections a v w) :
    ∃ d : ℝ×ℝ, TransverseDirection a d ∧ ∀ j,
      (cutForm a j d<0 ↔ if cutForm a j v=0 then cutForm a j w<0 else cutForm a j v<0) := by
  let σ : Fin 4 → Bool := fun j =>
    decide (if cutForm a j v=0 then cutForm a j w<0 else cutForm a j v<0)
  have ha (j : Fin 4) (hj : cutForm a j v=0) :
      if σ j then cutForm a j (v+w)<0 else 0 < cutForm a j (v+w) := by
    have hw : cutForm a j w≠0 := (h j).resolve_left (not_not.mpr hj)
    simp only [σ,hj,ite_eq_left,cutForm_add,zero_add]
    split_ifs with ht
    · exact of_decide_eq_true ht
    · exact lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false (Bool.eq_false_iff.mpr ht))) hw.symm
  have hi (j : Fin 4) (hj : cutForm a j v≠0) :
      if σ j then cutForm a j v<0 else 0 < cutForm a j v := by
    simp only [σ,ite_eq_right hj]
    split_ifs with ht
    · exact of_decide_eq_true ht
    · exact lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false (Bool.eq_false_iff.mpr ht))) hj.symm
  obtain ⟨d,_,hd,hg⟩ := finite_arrangement_germ a id (fun _ => 0) v (v+w) σ
    ha hi Set.univ isOpen_univ (Set.mem_univ _)
  refine ⟨d,fun j => ?_,fun j => ?_⟩
  · simpa using hg j 0
  · have hh := hd j
    by_cases ht : if cutForm a j v=0 then cutForm a j w<0 else cutForm a j v<0
    · simpa [σ,ht] using hh
    · have hh' : 0 < cutForm a j d := by simpa [σ,ht] using hh
      exact iff_of_false (not_lt_of_gt hh') ht

def SquareFlag (a : ℕ) (v : ℝ × ℝ) :=
  {z : ℝ × ℝ // TransverseDirection a v ∧ SquareBoundary v z}

theorem sector_enters_square {a : ℕ} {v z : ℝ × ℝ}
    (hz : SquareBoundary v z) {p : GenericPlane a}
    (hp : p.val ∈ arrangementNeighborhood a SquareStep.squareEdgeCuts z)
    (hv : p.val ∈ planeSector a z v) : SquareStep.InSquare p := by
  have h₀ (x d : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) (hd : x=0 → 0<d) :
      ¬(if x=0 then d<0 else x<0) := by
    split_ifs with he
    · exact not_lt_of_gt (hd he)
    · exact not_lt_of_ge hx.1
  have h₁ (x d : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) (hd : x=1 → d<0) :
      (if x=1 then d<0 else x<1) := by
    split_ifs with he
    · exact hd he
    · exact lt_of_le_of_ne hx.2 he
  have h l (hl : l∈SquareStep.squareEdgeCuts) := planeSign_neighborhood hp hv hl
  have hx₀ : ¬p.val.1<0 := by
    have hh := h (0,0) (by simp [SquareStep.squareEdgeCuts])
    have hh' := decide_eq_decide.mp hh
    simpa [planeSign,cutForm,h₀ z.1 v.1 hz.1 hz.2.2.1] using hh'
  have hx₁ : p.val.1<1 := by
    have hh := h (0,1) (by simp [SquareStep.squareEdgeCuts])
    have hh' := decide_eq_decide.mp hh
    simpa [planeSign,cutForm,h₁ z.1 v.1 hz.1 hz.2.2.2.1] using hh'
  have hy₀ : ¬p.val.2<0 := by
    have hh := h (1,0) (by simp [SquareStep.squareEdgeCuts])
    have hh' := decide_eq_decide.mp hh
    simpa [planeSign,cutForm,h₀ z.2 v.2 hz.2.1 hz.2.2.2.2.1] using hh'
  have hy₁ : p.val.2<1 := by
    have hh := h (1,1) (by simp [SquareStep.squareEdgeCuts])
    have hh' := decide_eq_decide.mp hh
    simpa [planeSign,cutForm,h₁ z.2 v.2 hz.2.1 hz.2.2.2.2.2] using hh'
  exact ⟨⟨le_of_not_gt hx₀,hx₁⟩,⟨le_of_not_gt hy₀,hy₁⟩⟩

theorem squareSector_generic {a : ℕ} {v : ℝ × ℝ} (z : SquareFlag a v)
    {N : Set (ℝ×ℝ)} (hN : IsOpen N) (hz : z.val∈N) :
    ∃ p : GenericSquare a, p.val∈N ∧ p.val∈planeSector a z.val v := by
  obtain ⟨p,hp,hpv⟩ := planeSector_generic z.property.1
    (hN.inter (arrangementNeighborhood_open a SquareStep.squareEdgeCuts z.val))
    ⟨hz,self_mem_arrangementNeighborhood a SquareStep.squareEdgeCuts z.val⟩
  have hps := sector_enters_square z.property.2 hp.2 hpv
  exact ⟨⟨p.val,hps.1,hps.2,p.property⟩,hp.1,hpv⟩

def IsSquareGerm {a : ℕ} {v : ℝ×ℝ} {K : Type*} (f : GenericSquare a → K)
    (z : SquareFlag a v) (c : K) : Prop :=
  ∃ N : Set (ℝ×ℝ), IsOpen N ∧ z.val∈N ∧
    ∀ p : GenericSquare a, p.val∈N → p.val∈planeSector a z.val v → f p=c

theorem exists_squareGerm {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (z : SquareFlag a v) :
    ∃ c, IsSquareGerm f z c := by
  obtain ⟨S,hS⟩ := hf
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z (arrangementNeighborhood_open a S z.val)
    (self_mem_arrangementNeighborhood a S z.val)
  refine ⟨f p,arrangementNeighborhood a S z.val,arrangementNeighborhood_open a S z.val,
    self_mem_arrangementNeighborhood a S z.val,fun q hq hqv => hS q p ?_⟩
  intro l hl
  exact (planeSign_neighborhood (p:=⟨q.val,q.property.2.2⟩) hq hqv hl).trans
    (planeSign_neighborhood (p:=⟨p.val,p.property.2.2⟩) hp hpv hl).symm

theorem IsSquareGerm.unique {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    {f : GenericSquare a → K} {z : SquareFlag a v} {c d : K}
    (hc : IsSquareGerm f z c) (hd : IsSquareGerm f z d) : c=d := by
  obtain ⟨N,hN,hz,hc⟩ := hc
  obtain ⟨M,hM,hz',hd⟩ := hd
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z (hN.inter hM) ⟨hz,hz'⟩
  exact (hc p hp.1 hpv).symm.trans (hd p hp.2 hpv)

noncomputable def flagValue {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (z : SquareFlag a v) : K :=
  Classical.choose (exists_squareGerm f hf z)

theorem flagValue_spec {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (z : SquareFlag a v) :
    IsSquareGerm f z (flagValue f hf z) := Classical.choose_spec (exists_squareGerm f hf z)

theorem flagValue_eq {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (z : SquareFlag a v)
    {c : K} (hc : IsSquareGerm f z c) : flagValue f hf z=c := (flagValue_spec f hf z).unique hc

theorem flagValue_finite {a : ℕ} {v : ℝ×ℝ} {ι K : Type*} [Finite ι]
    (f : ι → GenericSquare a → K) (hf : ∀ i, HasSquareArrangement (f i))
    (z : SquareFlag a v) {N : Set (ℝ×ℝ)} (hN : IsOpen N) (hz : z.val∈N) :
    ∃ p : GenericSquare a, p.val∈N ∧ p.val∈planeSector a z.val v ∧
      ∀ i, f i p=flagValue (f i) (hf i) z := by
  choose M hM hzM hfg using fun i => flagValue_spec (f i) (hf i) z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z
    (hN.inter (isOpen_iInter_of_finite hM)) ⟨hz,Set.mem_iInter.mpr hzM⟩
  exact ⟨p,hp.1,hpv,fun i => hfg i p (Set.mem_iInter.mp hp.2 i) hpv⟩

noncomputable def flagMem {a : ℕ} {v : ℝ×ℝ} (U : polygonAlgebra a)
    (z : SquareFlag a v) : Prop :=
  flagValue (fun p => decide (p∈U.val)) (polygon_hasSquareArrangement U.property) z=true

theorem flagMem_iff {a : ℕ} {v : ℝ×ℝ} (U : polygonAlgebra a) (z : SquareFlag a v) :
    ∃ N : Set (ℝ×ℝ), IsOpen N ∧ z.val∈N ∧
      ∀ p : GenericSquare a, p.val∈N → p.val∈planeSector a z.val v →
        (p∈U.val ↔ flagMem U z) := by
  obtain ⟨N,hN,hz,hf⟩ := flagValue_spec (fun p => decide (p∈U.val))
    (polygon_hasSquareArrangement U.property) z
  refine ⟨N,hN,hz,fun p hp hpv => ?_⟩
  unfold flagMem
  rw [← hf p hp hpv]
  simp

@[simp] theorem flagMem_bot {a : ℕ} {v : ℝ×ℝ} (z : SquareFlag a v) :
    ¬flagMem (⊥ : polygonAlgebra a) z := by
  have h := flagValue_eq (fun p : GenericSquare a => decide (p∈(⊥ : polygonAlgebra a).val))
    (polygon_hasSquareArrangement (⊥ : polygonAlgebra a).property) z
    (c:=false) ⟨Set.univ,isOpen_univ,Set.mem_univ _,fun _ _ _ => by simp⟩
  intro hm
  exact Bool.false_ne_true (h.symm.trans hm)

theorem flagMem_sup {a : ℕ} {v : ℝ×ℝ} (U V : polygonAlgebra a) (z : SquareFlag a v) :
    flagMem (U⊔V) z ↔ flagMem U z ∨ flagMem V z := by
  obtain ⟨N,hN,hz,h⟩ := flagMem_iff (U⊔V) z
  obtain ⟨M,hM,hz',h'⟩ := flagMem_iff U z
  obtain ⟨L,hL,hz'',h''⟩ := flagMem_iff V z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z ((hN.inter hM).inter hL) ⟨⟨hz,hz'⟩,hz''⟩
  rw [← h p hp.1.1 hpv,← h' p hp.1.2 hpv,← h'' p hp.2 hpv]
  rfl

theorem flagMem_compl {a : ℕ} {v : ℝ×ℝ} (U : polygonAlgebra a) (z : SquareFlag a v) :
    flagMem Uᶜ z ↔ ¬flagMem U z := by
  obtain ⟨N,hN,hz,h⟩ := flagMem_iff Uᶜ z
  obtain ⟨M,hM,hz',h'⟩ := flagMem_iff U z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z (hN.inter hM) ⟨hz,hz'⟩
  rw [← h p hp.1 hpv,← h' p hp.2 hpv]
  rfl

end FlagGerms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagTranslation
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
section FlagTranslation
open Classical

noncomputable def flagTranslate {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) : SquareFlag a v := by
  have hv₁ : v.1≠0 := by simpa [cutForm] using z.property.1 0
  have hv₂ : v.2≠0 := by simpa [cutForm] using z.property.1 1
  have hx := flagFract_boundary (z.val.1+ordinary u.1) v.1 hv₁
  have hy := flagFract_boundary (z.val.2+ordinary u.2) v.2 hv₂
  exact ⟨(flagFract (z.val.1+ordinary u.1) v.1,flagFract (z.val.2+ordinary u.2) v.2),
    z.property.1,hx.1,hy.1,hx.2.1,hx.2.2,hy.2.1,hy.2.2⟩

@[simp] theorem flagTranslate_val {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) : (flagTranslate u z).val=
      (flagFract (z.val.1+ordinary u.1) v.1,flagFract (z.val.2+ordinary u.2) v.2) := rfl

@[simp] theorem flagTranslate_zero {a : ℕ} {v : ℝ×ℝ} (z : SquareFlag a v) :
    flagTranslate 0 z=z := by
  apply Subtype.ext
  simp only [flagTranslate_val,Prod.fst_zero,Prod.snd_zero,map_zero,add_zero]
  exact Prod.ext (flagFract_self z.property.2.1 z.property.2.2.2.1 z.property.2.2.2.2.1)
    (flagFract_self z.property.2.2.1 z.property.2.2.2.2.2.1 z.property.2.2.2.2.2.2)

theorem flagTranslate_add {a : ℕ} {v : ℝ×ℝ} (u w : CutRing×CutRing)
    (z : SquareFlag a v) : flagTranslate (u+w) z=flagTranslate u (flagTranslate w z) := by
  apply Subtype.ext
  simp only [flagTranslate_val,Prod.fst_add,Prod.snd_add,map_add]
  rw [flagFract_flagFract_add,flagFract_flagFract_add]
  congr 1 <;> congr 1 <;> ring

theorem flagTranslate_period {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing) (k : ℤ×ℤ)
    (z : SquareFlag a v) : flagTranslate (u+SquareStep.intPair k) z=flagTranslate u z := by
  apply Subtype.ext
  simp only [flagTranslate_val,SquareStep.intPair,Prod.fst_add,Prod.snd_add,map_add,map_intCast]
  rw [← add_assoc,← add_assoc,flagFract_add_int,flagFract_add_int]

theorem flagTranslate_reduce {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) : flagTranslate u z=flagTranslate (orbitRepresentative u) z := by
  have hu : u=orbitRepresentative u+SquareStep.intPair (u.1.re,u.2.re) := by
    apply Prod.ext <;> apply QuadraticAlgebra.ext <;> simp [orbitRepresentative,SquareStep.intPair,cutTau]
  calc
    _ = flagTranslate (orbitRepresentative u+SquareStep.intPair (u.1.re,u.2.re)) z := congrArg (fun t => flagTranslate t z) hu
    _ = _ := flagTranslate_period _ _ _

theorem planeSector_add_iff {a : ℕ} (z v t p : ℝ×ℝ) :
    p+t∈planeSector a (z+t) v ↔ p∈planeSector a z v := by
  unfold planeSector
  simp only [Set.mem_ofPred_eq,cutForm_add]
  apply forall_congr'
  intro j
  split_ifs <;> simp

theorem flagTranslate_neighborhood {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) {N : Set (ℝ×ℝ)} (hN : IsOpen N)
    (hz : (flagTranslate u z).val∈N) :
    ∃ M : Set (ℝ×ℝ), IsOpen M ∧ z.val∈M ∧
      ∀ p : GenericSquare a, p.val∈M → p.val∈planeSector a z.val v →
        (translate a u p).val∈N ∧
          (translate a u p).val∈planeSector a (flagTranslate u z).val v := by
  let k : ℤ×ℤ := (flagFloor (z.val.1+ordinary u.1) v.1,
    flagFloor (z.val.2+ordinary u.2) v.2)
  let t : CutRing×CutRing := u-SquareStep.intPair k
  let b : ℝ×ℝ := (ordinary t.1,ordinary t.2)
  have hbase : (flagTranslate u z).val=z.val+b := by
    apply Prod.ext <;> simp only [flagTranslate_val,flagFract_eq,b,t,k,SquareStep.intPair,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,map_sub,map_intCast] <;> ring
  let L := N ∩ arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val
  let M : Set (ℝ×ℝ) := (fun p => p+b) ⁻¹' L
  have hL : IsOpen L := hN.inter (arrangementNeighborhood_open _ _ _)
  have hzL : (flagTranslate u z).val∈L := ⟨hz,self_mem_arrangementNeighborhood _ _ _⟩
  refine ⟨M,hL.preimage (continuous_id.add continuous_const),?_,fun p hp hpv => ?_⟩
  · change z.val+b∈L
    rw [← hbase]; exact hzL
  · let q : GenericPlane a := GenericPlane.shift t ⟨p.val,p.property.2.2⟩
    have hqv : q.val∈planeSector a (flagTranslate u z).val v := by
      rw [hbase]
      exact (planeSector_add_iff z.val v b p.val).mpr hpv
    have hqs : SquareStep.InSquare q := sector_enters_square (flagTranslate u z).property.2 hp.2 hqv
    have hqp : (translate a u p).val=q.val := by
      apply Prod.ext
      · change Int.fract (p.val.1+ordinary u.1)=p.val.1+ordinary t.1
        have he : p.val.1+ordinary t.1=p.val.1+ordinary u.1-(k.1:ℝ) := by
          simp only [t,SquareStep.intPair,Prod.fst_sub,map_sub,map_intCast]; ring
        rw [he]
        rw [← Int.fract_sub_intCast (p.val.1+ordinary u.1) k.1]
        exact Int.fract_eq_self.mpr (by simpa only [q,GenericPlane.shift,Prod.fst_add,he,Set.mem_Ico] using hqs.1)
      · change Int.fract (p.val.2+ordinary u.2)=p.val.2+ordinary t.2
        have he : p.val.2+ordinary t.2=p.val.2+ordinary u.2-(k.2:ℝ) := by
          simp only [t,SquareStep.intPair,Prod.snd_sub,map_sub,map_intCast]; ring
        rw [he]
        rw [← Int.fract_sub_intCast (p.val.2+ordinary u.2) k.2]
        exact Int.fract_eq_self.mpr (by simpa only [q,GenericPlane.shift,Prod.snd_add,he,Set.mem_Ico] using hqs.2)
    rw [hqp]
    exact ⟨hp.1,hqv⟩

theorem flagValue_translate {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (u : CutRing×CutRing)
    (z : SquareFlag a v) :
    flagValue (fun p => f (translate a u p)) (squareArrangement_translate hf u) z =
      flagValue f hf (flagTranslate u z) := by
  obtain ⟨N,hN,hz,hf'⟩ := flagValue_spec f hf (flagTranslate u z)
  obtain ⟨M,hM,hzM,hg⟩ := flagTranslate_neighborhood u z hN hz
  exact flagValue_eq _ _ _ ⟨M,hM,hzM,fun p hp hpv =>
    hf' (translate a u p) (hg p hp hpv).1 (hg p hp hpv).2⟩

theorem flagMem_preimage_translate {a : ℕ} {v : ℝ×ℝ} (U : polygonAlgebra a)
    (u : CutRing×CutRing) (z : SquareFlag a v) :
    flagMem ⟨translate a u ⁻¹' U.val,polygon_preimage_translate u U.property⟩ z ↔
      flagMem U (flagTranslate u z) := by
  change flagValue (fun p => decide (translate a u p∈U.val))
    (squareArrangement_translate (polygon_hasSquareArrangement U.property) u) z=true ↔ _
  rw [flagValue_translate (fun p => decide (p∈U.val)) (polygon_hasSquareArrangement U.property)]
  rfl

end FlagTranslation

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FlagExchangeAction
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
section FlagExchangeAction
open Classical

theorem flagMem_top {a : ℕ} {v : ℝ×ℝ} (z : SquareFlag a v) :
    flagMem (⊤ : polygonAlgebra a) z := by
  have h := flagMem_compl (⊥ : polygonAlgebra a) z
  simpa using h.mpr (flagMem_bot z)

theorem flagMem_inf {a : ℕ} {v : ℝ×ℝ} (U V : polygonAlgebra a) (z : SquareFlag a v) :
    flagMem (U⊓V) z ↔ flagMem U z ∧ flagMem V z := by
  have he : U⊓V=(Uᶜ⊔Vᶜ)ᶜ := by simp
  rw [he,flagMem_compl,flagMem_sup,flagMem_compl,flagMem_compl]
  tauto

theorem flagMem_nonempty {a : ℕ} {v : ℝ×ℝ} {U : polygonAlgebra a}
    {z : SquareFlag a v} (hz : flagMem U z) : U.val.Nonempty := by
  obtain ⟨N,hN,hzN,h⟩ := flagMem_iff U z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z hN hzN
  exact ⟨p,(h p hp hpv).mpr hz⟩

abbrev FlagTrackPoint (a m : ℕ) (v : ℝ×ℝ) := Fin m × SquareFlag a v

theorem flagChart_exists {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    ∃ c : TableChart a m, c.Holds g.val ∧ z.1=c.source ∧ flagMem c.domain z.2 := by
  obtain ⟨S,hS,hcover⟩ := g.property
  obtain ⟨p,_,_,hp⟩ := flagValue_finite
    (fun c : S => fun p : GenericSquare a => decide (p∈c.val.domain.val))
    (fun c => polygon_hasSquareArrangement c.val.domain.property)
    z.2 isOpen_univ (Set.mem_univ _)
  obtain ⟨c,hc,htrack,hcp⟩ := hcover (z.1,p)
  refine ⟨c,hS c hc,htrack,?_⟩
  exact (hp ⟨c,hc⟩).symm.trans (decide_eq_true hcp)

theorem flagChart_values_eq {a m : ℕ} {v : ℝ×ℝ} {f : TrackPoint a m → TrackPoint a m}
    {c d : TableChart a m} (hc : c.Holds f) (hd : d.Holds f)
    {z : FlagTrackPoint a m v} (hcs : z.1=c.source) (hds : z.1=d.source)
    (hcz : flagMem c.domain z.2) (hdz : flagMem d.domain z.2) :
    (c.target,flagTranslate c.shift z.2)=(d.target,flagTranslate d.shift z.2) := by
  obtain ⟨p,hp⟩ := flagMem_nonempty ((flagMem_inf c.domain d.domain z.2).mpr ⟨hcz,hdz⟩)
  have hev : (c.target,translate a c.shift p)=(d.target,translate a d.shift p) := by
    have hsource : c.source=d.source := hcs.symm.trans hds
    rw [← hc p hp.1,← hd p hp.2,hsource]
  have ht := congrArg Prod.fst hev
  have hu := orbitRepresentative_eq_of_translate_eq p (congrArg Prod.snd hev)
  refine Prod.ext (show c.target=d.target from ht) ?_
  rw [flagTranslate_reduce c.shift,flagTranslate_reduce d.shift,hu]

noncomputable def flagChart {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) : TableChart a m := Classical.choose (flagChart_exists g z)

theorem flagChart_spec {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    (flagChart g z).Holds g.val ∧ z.1=(flagChart g z).source ∧
      flagMem (flagChart g z).domain z.2 := Classical.choose_spec (flagChart_exists g z)

noncomputable def flagAction {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) : FlagTrackPoint a m v :=
  ((flagChart g z).target,flagTranslate (flagChart g z).shift z.2)

theorem flagAction_apply {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) (c : TableChart a m) (hc : c.Holds g.val)
    (hcs : z.1=c.source) (hcz : flagMem c.domain z.2) :
    flagAction g z=(c.target,flagTranslate c.shift z.2) := by
  exact flagChart_values_eq (flagChart_spec g z).1 hc (flagChart_spec g z).2.1 hcs
    (flagChart_spec g z).2.2 hcz

@[simp] theorem flagAction_one {a m : ℕ} {v : ℝ×ℝ} (z : FlagTrackPoint a m v) :
    flagAction (1 : polygonFullGroup a m) z=z := by
  let c : TableChart a m := ⟨z.1,z.1,0,⊤⟩
  have hc : c.Holds (1 : polygonFullGroup a m).val := by
    intro p _
    simp [c]
  have h := flagAction_apply 1 z c hc rfl (flagMem_top z.2)
  simpa only [c,flagTranslate_zero,Prod.eta] using h

theorem flagAction_mul {a m : ℕ} {v : ℝ×ℝ} (f g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) : flagAction (f*g) z=flagAction f (flagAction g z) := by
  let d := flagChart g z
  let c := flagChart f (flagAction g z)
  have hd : d.Holds g.val ∧ z.1=d.source ∧ flagMem d.domain z.2 := flagChart_spec g z
  have hc : c.Holds f.val ∧ (flagAction g z).1=c.source ∧
      flagMem c.domain (flagAction g z).2 := flagChart_spec f (flagAction g z)
  have hcd : c.source=d.target := hc.2.1.symm
  have hcomp : (c.comp d).Holds (f*g).val := by
    exact TableChart.comp_holds (f := f.val) (g := g.val) hc.1 hd.1 hcd
  have hcdom : flagMem (c.comp d).domain z.2 := by
    change flagMem (d.domain⊓⟨translate a d.shift ⁻¹' c.domain.val,
      polygon_preimage_translate d.shift c.domain.property⟩) z.2
    rw [flagMem_inf,flagMem_preimage_translate]
    exact ⟨hd.2.2,hc.2.2⟩
  calc
    flagAction (f*g) z = ((c.comp d).target,flagTranslate (c.comp d).shift z.2) :=
      flagAction_apply (f*g) z (c.comp d) hcomp hd.2.1 hcdom
    _ = flagAction f (flagAction g z) := by
      change (c.target,flagTranslate (c.shift+d.shift) z.2)=
        (c.target,flagTranslate c.shift (flagTranslate d.shift z.2))
      rw [flagTranslate_add]

end FlagExchangeAction

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

noncomputable def scaledOrdinary (D : ℕ) (u : CutRing×CutRing) : ℝ×ℝ :=
  (ordinary u.1/D,ordinary u.2/D)

noncomputable def scaledConjugate (D : ℕ) (u : CutRing×CutRing) : ℝ×ℝ :=
  (conjugate u.1/D,conjugate u.2/D)

def InFlagLattice (D : ℕ) (z : ℝ×ℝ) : Prop := ∃ u,scaledOrdinary D u=z

def FlagSite (a m D : ℕ) (v : ℝ×ℝ) :=
  {z : FlagTrackPoint a m v // InFlagLattice D z.2.val}

noncomputable def flagSiteNumerator {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) :
    CutRing×CutRing := z.property.choose

theorem flagSiteNumerator_spec {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) :
    scaledOrdinary D (flagSiteNumerator z)=z.val.2.val := z.property.choose_spec

noncomputable def flagShiftPeriod {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) : ℤ×ℤ :=
  (flagFloor (z.val.1+ordinary u.1) v.1,flagFloor (z.val.2+ordinary u.2) v.2)

noncomputable def flagShiftNumerator (D : ℕ) (n u : CutRing×CutRing) (k : ℤ×ℤ) :
    CutRing×CutRing :=
  (n.1+(D:CutRing)*u.1-(D:CutRing)*(k.1:CutRing),
   n.2+(D:CutRing)*u.2-(D:CutRing)*(k.2:CutRing))

theorem scaledOrdinary_shift {D : ℕ} (hD : 0<D) (n u : CutRing×CutRing) (k : ℤ×ℤ) :
    scaledOrdinary D (flagShiftNumerator D n u k)=
      scaledOrdinary D n+(ordinary u.1,ordinary u.2)-((k.1:ℝ),(k.2:ℝ)) := by
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  apply Prod.ext <;>
    simp only [scaledOrdinary,flagShiftNumerator,Prod.fst_sub,Prod.snd_sub,
      Prod.fst_add,Prod.snd_add,map_sub,map_add,map_mul,map_natCast,map_intCast] <;>
    field_simp

theorem flagTranslate_lattice {a D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (u : CutRing×CutRing) (z : SquareFlag a v) (hz : InFlagLattice D z.val) :
    InFlagLattice D (flagTranslate u z).val := by
  obtain ⟨n,hn⟩ := hz
  refine ⟨flagShiftNumerator D n u (flagShiftPeriod u z),?_⟩
  rw [scaledOrdinary_shift hD,hn]
  simp only [flagTranslate_val,flagFract_eq,flagShiftPeriod]
  rfl

theorem flagAction_lattice {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagTrackPoint a m v) (hz : InFlagLattice D z.2.val) :
    InFlagLattice D (flagAction g z).2.val :=
  flagTranslate_lattice hD _ _ hz

noncomputable def flagSiteAction {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) : FlagSite a m D v :=
  ⟨flagAction g z.val,flagAction_lattice hD g z.val z.property⟩

@[simp] theorem flagSiteAction_one {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (z : FlagSite a m D v) : flagSiteAction hD 1 z=z :=
  Subtype.ext (flagAction_one z.val)

theorem flagSiteAction_mul {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (f g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteAction hD (f*g) z=flagSiteAction hD f (flagSiteAction hD g z) :=
  Subtype.ext (flagAction_mul f g z.val)

noncomputable def flagSitePermutation {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) : Equiv.Perm (FlagSite a m D v) where
  toFun := flagSiteAction hD g
  invFun := flagSiteAction hD g⁻¹
  left_inv z := by rw [← flagSiteAction_mul,inv_mul_cancel,flagSiteAction_one]
  right_inv z := by rw [← flagSiteAction_mul,mul_inv_cancel,flagSiteAction_one]

noncomputable def flagSiteConjugate {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) :
    ℝ×ℝ := scaledConjugate D (flagSiteNumerator z)

end FlagSites

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierLineGeometry
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
section BarrierLineGeometry
open Classical Set

noncomputable def barrierLinePoint (a : ℕ) (j : Fin 4) (c : CutRing) (t : ℝ) : ℝ×ℝ :=
  ![(ordinary c,t),(t,ordinary c),(t,ordinary c+Real.goldenRatio^a*t),
    (ordinary c+Real.goldenRatio^a*t,t)] j

noncomputable def barrierLineLower (a : ℕ) (j : Fin 4) (c : CutRing) : ℝ :=
  ![0,0,max 0 (-ordinary c/Real.goldenRatio^a),max 0 (-ordinary c/Real.goldenRatio^a)] j

noncomputable def barrierLineUpper (a : ℕ) (j : Fin 4) (c : CutRing) : ℝ :=
  ![1,1,min 1 ((1-ordinary c)/Real.goldenRatio^a),min 1 ((1-ordinary c)/Real.goldenRatio^a)] j

theorem cutForm_barrierLinePoint (a : ℕ) (j : Fin 4) (c : CutRing) (t : ℝ) :
    cutForm a j (barrierLinePoint a j c t)=ordinary c := by
  fin_cases j <;> simp [cutForm,barrierLinePoint]

theorem barrierLinePoint_parameter {a : ℕ} {j : Fin 4} {c : CutRing} {p : ℝ×ℝ}
    (hp : cutForm a j p=ordinary c) : barrierLinePoint a j c (barrierLineParameter j p)=p := by
  fin_cases j <;> simp [cutForm] at hp <;>
    apply Prod.ext <;> simp [barrierLinePoint,barrierLineParameter] <;> linarith

noncomputable def barrierCandidate (a : ℕ) (j : Fin 4) (N : ℝ) : Set CutRing :=
  {c | |conjugate c|≤4*N ∧ ∃p∈squareInterior,cutForm a j p=ordinary c}

theorem squareInterior_cutForm_bound {a : ℕ} {p : ℝ×ℝ} (hp : p∈squareInterior) (j : Fin 4) :
    |cutForm a j p|≤1+Real.goldenRatio^a := by
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  rcases hp with ⟨⟨hx₀,hx₁⟩,⟨hy₀,hy₁⟩⟩
  apply abs_le.mpr
  fin_cases j <;> simp [cutForm] <;> constructor <;> nlinarith

theorem barrierCandidate_finite (a : ℕ) (j : Fin 4) {N : ℝ} (hN : 0<N) :
    (barrierCandidate a j N).Finite := by
  apply (cutRectangle_finite (-(1+Real.goldenRatio^a)) (-4*N)
    (2*(1+Real.goldenRatio^a)) (8*N) (by positivity)).subset
  rintro c ⟨hc,p,hp,hpc⟩
  have hbound := squareInterior_cutForm_bound (a:=a) hp j
  rw [hpc] at hbound
  have ho := abs_le.mp hbound
  have hb := abs_le.mp hc
  exact ⟨⟨ho.1,by linarith [ho.2]⟩,⟨by linarith [hb.1],by linarith [hb.2]⟩⟩

theorem barrierCandidate_coordinate {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) (hj : j=0 ∨ j=1) : ordinary c∈Ioo (0:ℝ) 1 := by
  obtain ⟨p,hp,hpc⟩ := hc.2
  rcases hj with rfl | rfl
  · have he : p.1=ordinary c := by simpa [cutForm] using hpc
    exact he ▸ hp.1
  · have he : p.2=ordinary c := by simpa [cutForm] using hpc
    exact he ▸ hp.2

theorem barrierLinePoint_interior_iff {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) (t : ℝ) :
    barrierLinePoint a j c t∈squareInterior ↔
      t∈Ioo (barrierLineLower a j c) (barrierLineUpper a j c) := by
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  fin_cases j <;> simp [barrierLinePoint,barrierLineLower,barrierLineUpper,
    squareInterior,Set.mem_prod,Set.mem_Ioo]
  · have hz := barrierCandidate_coordinate hc (Or.inl rfl)
    exact fun _ _ => hz
  · have hz := barrierCandidate_coordinate hc (Or.inr rfl)
    exact fun _ _ => hz
  · rw [div_lt_iff₀ ht,lt_div_iff₀ ht]
    constructor <;> intro h <;> constructor <;> constructor <;> linarith [h.1.1,h.1.2,h.2.1,h.2.2]
  · rw [div_lt_iff₀ ht,lt_div_iff₀ ht]
    constructor <;> intro h <;> constructor <;> constructor <;> linarith [h.1.1,h.1.2,h.2.1,h.2.2]

end BarrierLineGeometry

section BarrierFlags
open Classical

theorem positiveDiagonal_transverse {a : ℕ} (ha : 0<a) : TransverseDirection a (1,1) := by
  have ht : 1<Real.goldenRatio^a := one_lt_pow₀ Real.one_lt_goldenRatio (by omega)
  intro j
  fin_cases j <;> simp [cutForm] <;> linarith

theorem exists_barrierFlagDirection {a : ℕ} (ha : 0<a) (j : Fin 4) :
    ∃d : ℝ×ℝ,TransverseDirection a d ∧ 0<d.1 ∧ 0<d.2 ∧ ∀k,
      (cutForm a k d<0 ↔ if cutForm a k (barrierTangent a j)=0 then
        cutForm a k (1,1)<0 else cutForm a k (barrierTangent a j)<0) := by
  obtain ⟨d,hd,he⟩ := flagDirections_sector
    (show FlagDirections a (barrierTangent a j) (1,1) from
      fun k => Or.inr (positiveDiagonal_transverse ha k))
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  have hpos₁ : 0<d.1 := by
    have hn : d.1≠0 := by simpa [cutForm] using hd 0
    have hh := he 0
    have hnot : ¬d.1<0 := by
      fin_cases j <;> norm_num [cutForm,barrierTangent,ne_of_gt ht,not_lt_of_gt ht] at hh ⊢ <;> exact hh
    exact lt_of_le_of_ne (le_of_not_gt hnot) hn.symm
  have hpos₂ : 0<d.2 := by
    have hn : d.2≠0 := by simpa [cutForm] using hd 1
    have hh := he 1
    have hnot : ¬d.2<0 := by
      fin_cases j <;> norm_num [cutForm,barrierTangent,ne_of_gt ht,not_lt_of_gt ht] at hh ⊢ <;> exact hh
    exact lt_of_le_of_ne (le_of_not_gt hnot) hn.symm
  exact ⟨d,hd,hpos₁,hpos₂,he⟩

noncomputable def barrierFlagDirection {a : ℕ} (ha : 0<a) (j : Fin 4) : ℝ×ℝ :=
  (exists_barrierFlagDirection ha j).choose

theorem barrierFlagDirection_spec {a : ℕ} (ha : 0<a) (j : Fin 4) :
    TransverseDirection a (barrierFlagDirection ha j) ∧
      0<(barrierFlagDirection ha j).1 ∧ 0<(barrierFlagDirection ha j).2 ∧ ∀k,
      (cutForm a k (barrierFlagDirection ha j)<0 ↔
      if cutForm a k (barrierTangent a j)=0 then cutForm a k (1,1)<0
      else cutForm a k (barrierTangent a j)<0) :=
  (exists_barrierFlagDirection ha j).choose_spec

end BarrierFlags

section BarrierEndpoints
open Classical Set

noncomputable def barrierIncoming (a : ℕ) (j : Fin 4) (c : CutRing) : ℝ×ℝ :=
  barrierLinePoint a j c (barrierLineLower a j c)

theorem barrierLineLower_lt_upper {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) : barrierLineLower a j c<barrierLineUpper a j c := by
  obtain ⟨p,hp,hpc⟩ := hc.2
  have hh : barrierLinePoint a j c (barrierLineParameter j p)∈squareInterior := by
    rwa [barrierLinePoint_parameter hpc]
  exact lt_trans ((barrierLinePoint_interior_iff hc _).mp hh).1
    ((barrierLinePoint_interior_iff hc _).mp hh).2

theorem barrierIncoming_bounds {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) :
    (barrierIncoming a j c).1∈Ico (0:ℝ) 1 ∧ (barrierIncoming a j c).2∈Ico (0:ℝ) 1 ∧
    ((barrierIncoming a j c).1=0 ∨ (barrierIncoming a j c).2=0) := by
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  have hgap := barrierLineLower_lt_upper hc
  fin_cases j
  · have hz := barrierCandidate_coordinate hc (Or.inl rfl)
    simpa [barrierIncoming,barrierLinePoint,barrierLineLower] using
      (show (0≤ordinary c ∧ ordinary c<1) from ⟨le_of_lt hz.1,hz.2⟩)
  · have hz := barrierCandidate_coordinate hc (Or.inr rfl)
    simpa [barrierIncoming,barrierLinePoint,barrierLineLower] using
      (show (0≤ordinary c ∧ ordinary c<1) from ⟨le_of_lt hz.1,hz.2⟩)
  · by_cases h : 0≤ordinary c
    · have hm : max 0 (-ordinary c/Real.goldenRatio^a)=0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) ht.le)
      simp [barrierLineLower,barrierLineUpper,hm] at hgap
      have hb : ordinary c<1 := by
        have := (div_pos_iff_of_pos_right ht).mp hgap
        linarith
      simp [barrierIncoming,barrierLinePoint,barrierLineLower,hm,h,hb]
    · have hneg : ordinary c<0 := lt_of_not_ge h
      have hm : max 0 (-ordinary c/Real.goldenRatio^a)= -ordinary c/Real.goldenRatio^a :=
        max_eq_right (div_nonneg (neg_nonneg.mpr hneg.le) ht.le)
      simp [barrierLineLower,barrierLineUpper,hm] at hgap
      have he : ordinary c+Real.goldenRatio^a*(-ordinary c/Real.goldenRatio^a)=0 := by
        field_simp; ring
      simp [barrierIncoming,barrierLinePoint,barrierLineLower,he,
        div_nonneg (neg_nonneg.mpr hneg.le) ht.le,hgap.1]
  · by_cases h : 0≤ordinary c
    · have hm : max 0 (-ordinary c/Real.goldenRatio^a)=0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) ht.le)
      simp [barrierLineLower,barrierLineUpper,hm] at hgap
      have hb : ordinary c<1 := by
        have := (div_pos_iff_of_pos_right ht).mp hgap
        linarith
      simp [barrierIncoming,barrierLinePoint,barrierLineLower,hm,h,hb]
    · have hneg : ordinary c<0 := lt_of_not_ge h
      have hm : max 0 (-ordinary c/Real.goldenRatio^a)= -ordinary c/Real.goldenRatio^a :=
        max_eq_right (div_nonneg (neg_nonneg.mpr hneg.le) ht.le)
      simp [barrierLineLower,barrierLineUpper,hm] at hgap
      have he : ordinary c+Real.goldenRatio^a*(-ordinary c/Real.goldenRatio^a)=0 := by
        field_simp; ring
      simp [barrierIncoming,barrierLinePoint,barrierLineLower,he,
        div_nonneg (neg_nonneg.mpr hneg.le) ht.le,hgap.1]

theorem barrierIncoming_boundary {a : ℕ} (ha : 0<a) {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) :
    SquareBoundary (barrierFlagDirection ha j) (barrierIncoming a j c) := by
  obtain ⟨hx,hy,_⟩ := barrierIncoming_bounds hc
  have hd := barrierFlagDirection_spec ha j
  exact ⟨⟨hx.1,hx.2.le⟩,⟨hy.1,hy.2.le⟩,fun _ => hd.2.1,
    fun h => False.elim ((ne_of_lt hx.2) h),fun _ => hd.2.2.1,
    fun h => False.elim ((ne_of_lt hy.2) h)⟩

theorem barrierIncoming_edge {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) : ∃k : Fin 4,k≠j ∧
    cutForm a k (barrierIncoming a j c)=ordinary (0:CutRing) := by
  obtain ⟨hx,hy,hzero⟩ := barrierIncoming_bounds hc
  have hj := cutForm_barrierLinePoint a j c (barrierLineLower a j c)
  change cutForm a j (barrierIncoming a j c)=ordinary c at hj
  by_cases hj₀ : j=0
  · subst j
    refine ⟨1,by decide,?_⟩
    have hcpos := (barrierCandidate_coordinate hc (Or.inl rfl)).1
    have hxne : (barrierIncoming a 0 c).1≠0 := by
      simp [cutForm] at hj
      rw [hj]; exact ne_of_gt hcpos
    simpa [cutForm] using hzero.resolve_left hxne
  · rcases hzero with hzero | hzero
    · exact ⟨0,Ne.symm hj₀,by simpa [cutForm] using hzero⟩
    · refine ⟨1,?_,by simpa [cutForm] using hzero⟩
      intro he
      subst j
      have hcpos := (barrierCandidate_coordinate hc (Or.inr rfl)).1
      simp [cutForm] at hj
      linarith

theorem barrierIncoming_lattice {a : ℕ} (ha : 0<a) {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) :
    InFlagLattice (commonVertexDenominator a) (barrierIncoming a j c) := by
  obtain ⟨k,hkj,hk⟩ := barrierIncoming_edge hc
  obtain ⟨u,v,hu,hv⟩ := all_intersections_common_denominator ha j k hkj.symm c 0
    (barrierIncoming a j c) (cutForm_barrierLinePoint a j c _) hk
  refine ⟨(u,v),Prod.ext ?_ ?_⟩ <;> simp only [scaledOrdinary]
  · rw [hu,mul_div_cancel_left₀ _ (by exact_mod_cast Nat.ne_of_gt (commonVertexDenominator_pos ha))]
  · rw [hv,mul_div_cancel_left₀ _ (by exact_mod_cast Nat.ne_of_gt (commonVertexDenominator_pos ha))]

noncomputable def barrierIncomingSite {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} {c : CutRing} (hc : c∈barrierCandidate a j N) :
    FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) :=
  ⟨(i,⟨barrierIncoming a j c,(barrierFlagDirection_spec ha j).1,barrierIncoming_boundary ha hc⟩),
    barrierIncoming_lattice ha hc⟩

end BarrierEndpoints

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierAlgorithm
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
section BarrierAlgorithm
open Classical Set

noncomputable def barrierSitePoint {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) : ℝ×ℝ :=
  z.val.2.val

def BarrierLineIndex (a : ℕ) (N : ℝ) := Σj : Fin 4,{c : CutRing // c∈barrierCandidate a j N}

@[instance_reducible] noncomputable def barrierLineIndexFintype (a : ℕ) {N : ℝ} (hN : 0<N) :
    Fintype (BarrierLineIndex a N) := by
  letI (j : Fin 4) : Fintype {c : CutRing // c∈barrierCandidate a j N} :=
    (barrierCandidate_finite a j hN).fintype
  exact inferInstanceAs (Fintype (Σj : Fin 4,{c : CutRing // c∈barrierCandidate a j N}))

end BarrierAlgorithm

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_QuadraticTiles
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
section QuadraticTiles
open Classical Module MeasureTheory
open scoped QuadraticAlgebra

theorem cutUnit_abs_norm {u : CutRing} (hu : IsUnit u) :
    |ordinary u*conjugate u|=1 := by
  rw [cut_norm_identity,← Int.cast_abs]
  have h := (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu)
  rcases Int.isUnit_iff.mp h with h|h <;> simp [h]

noncomputable def quadraticScaledMatrix (u : CutRing) (d s t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ordinary u/(d*s),ordinary u*Real.goldenRatio/(d*s);
     conjugate u/(d*t),conjugate u*Real.goldenConj/(d*t)]

theorem quadraticScaledMatrix_det (u : CutRing) (d s t : ℝ) :
    (quadraticScaledMatrix u d s t).det=
      ordinary u*conjugate u*(Real.goldenConj-Real.goldenRatio)/(d^2*s*t) := by
  simp only [quadraticScaledMatrix,Matrix.det_fin_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

theorem quadraticScaledMatrix_det_ne {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    (quadraticScaledMatrix u d s t).det≠0 := by
  rw [quadraticScaledMatrix_det]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact (abs_ne_zero.mp (by rw [cutUnit_abs_norm hu]; norm_num))
    · linarith [Real.goldenRatio_pos,Real.goldenConj_neg]
  · positivity

noncomputable def quadraticScaledBasis {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) : Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
  (Pi.basisFun ℝ (Fin 2)).map ((quadraticScaledMatrix u d s t).toLinearEquiv
    (Pi.basisFun ℝ (Fin 2)) (isUnit_iff_ne_zero.mpr (quadraticScaledMatrix_det_ne hu hd hs ht)))

theorem quadraticScaledBasis_apply {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) (i j : Fin 2) :
    quadraticScaledBasis hu hd hs ht i j=quadraticScaledMatrix u d s t j i := by
  simp only [quadraticScaledBasis,Basis.map_apply,Matrix.toLinearEquiv_apply,
    Matrix.toLin_self]
  fin_cases j <;> simp [Pi.basisFun_apply,Fin.sum_univ_two]

noncomputable def quadraticScaledEmbedding (d s t : ℝ) : CutRing →ₗ[ℤ] (Fin 2 → ℝ) where
  toFun z := ![ordinary z/(d*s),conjugate z/(d*t)]
  map_add' z w := by ext i; fin_cases i <;> simp [add_div]
  map_smul' n z := by ext i; fin_cases i <;> simp [mul_div_assoc]

theorem quadraticScaledEmbedding_injective {d s t : ℝ}
    (hd : 0<d) (hs : 0 < s) : Function.Injective (quadraticScaledEmbedding d s t) := by
  intro z w hh
  apply ordinary_injective
  have h := congrFun hh 0
  exact (div_left_inj' (mul_pos hd hs).ne').mp h

theorem quadraticScaledBasis_zero {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    quadraticScaledBasis hu hd hs ht 0=quadraticScaledEmbedding d s t u := by
  ext i
  rw [quadraticScaledBasis_apply]
  fin_cases i <;> rfl

theorem quadraticScaledBasis_one {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    quadraticScaledBasis hu hd hs ht 1=quadraticScaledEmbedding d s t (u*cutTau) := by
  ext i
  rw [quadraticScaledBasis_apply]
  fin_cases i <;> simp [quadraticScaledMatrix,quadraticScaledEmbedding]

theorem quadraticScaledBasis_span {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    Submodule.span ℤ (Set.range (quadraticScaledBasis hu hd hs ht))=
      (quadraticScaledEmbedding d s t).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change quadraticScaledBasis hu hd hs ht 0∈_
      rw [quadraticScaledBasis_zero]; exact LinearMap.mem_range_self _ _
    · change quadraticScaledBasis hu hd hs ht 1∈_
      rw [quadraticScaledBasis_one]; exact LinearMap.mem_range_self _ _
  · rintro _ ⟨z,rfl⟩
    have huu := hu
    obtain ⟨U,hU⟩ := huu
    let w : CutRing := (↑(U⁻¹):CutRing)*z
    have hz : u*w=z := by simp [w,← hU,← mul_assoc]
    have hw' : w=(w.re:CutRing)+(w.im:CutRing)*cutTau := by
      ext <;> simp [cutTau]
    have he : quadraticScaledEmbedding d s t z=
        w.re • quadraticScaledBasis hu hd hs ht 0+
        w.im • quadraticScaledBasis hu hd hs ht 1 := by
      rw [quadraticScaledBasis_zero,quadraticScaledBasis_one,← LinearMap.map_smul,
        ← LinearMap.map_smul,← map_add]
      congr 1
      rw [← hz,zsmul_eq_mul,zsmul_eq_mul]
      conv_lhs => rhs; rw [hw']
      ring
    rw [he]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩))

end QuadraticTiles

end SimpleAmenable
end
end

end OAI
end

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

section PairedQuadraticTiles
open Classical Module MeasureTheory

noncomputable def pairedQuadraticBasis {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    Basis (Fin 2 ⊕ Fin 2) ℝ ((Fin 2 → ℝ)×(Fin 2 → ℝ)) :=
  (quadraticScaledBasis hu hd hs ht).prod (quadraticScaledBasis hu hd hs ht)

end PairedQuadraticTiles

section PairedLatticeRiemann
open Classical Module MeasureTheory

noncomputable def pairedQuadraticEmbedding (d s t : ℝ) :
    (CutRing×CutRing) →ₗ[ℤ] ((Fin 2 → ℝ)×(Fin 2 → ℝ)) :=
  (quadraticScaledEmbedding d s t).prodMap (quadraticScaledEmbedding d s t)

theorem pairedQuadraticEmbedding_injective {d s t : ℝ} (hd : 0<d) (hs : 0 < s) :
    Function.Injective (pairedQuadraticEmbedding d s t) := by
  intro z w hh
  exact Prod.ext (quadraticScaledEmbedding_injective hd hs (congrArg Prod.fst hh))
    (quadraticScaledEmbedding_injective hd hs (congrArg Prod.snd hh))

theorem pairedQuadratic_span {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    Submodule.span ℤ (Set.range (pairedQuadraticBasis hu hd hs ht))=
      (pairedQuadraticEmbedding d s t).range := by
  rw [pairedQuadraticEmbedding,LinearMap.range_prodMap,← quadraticScaledBasis_span hu hd hs ht]
  ext x
  simp only [Submodule.mem_prod,Basis.mem_span_iff_repr_mem,pairedQuadraticBasis,
    Sum.forall,Basis.prod_repr_inl,Basis.prod_repr_inr]

noncomputable def pairedLatticeEquiv {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    (CutRing×CutRing) ≃ₗ[ℤ] Submodule.span ℤ (Set.range (pairedQuadraticBasis hu hd hs ht)) :=
  (LinearEquiv.ofInjective (pairedQuadraticEmbedding d s t)
    (pairedQuadraticEmbedding_injective hd hs)).trans
    (LinearEquiv.ofEq _ _ (pairedQuadratic_span hu hd hs ht).symm)

@[simp] theorem pairedLatticeEquiv_coe {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) (z : CutRing×CutRing) :
    (pairedLatticeEquiv hu hd hs ht z : ((Fin 2 → ℝ)×(Fin 2 → ℝ)))=
      pairedQuadraticEmbedding d s t z := rfl

end PairedLatticeRiemann

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
section FlagSiteCounts
open Classical

theorem flagSite_key_injective {a m D : ℕ} {v : ℝ×ℝ} :
    Function.Injective (fun z : FlagSite a m D v => (z.val.1,flagSiteNumerator z)) := by
  intro z w h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p : Fin m × (CutRing×CutRing) => p.1) h
  · apply Subtype.ext
    rw [← flagSiteNumerator_spec z,← flagSiteNumerator_spec w]
    exact congrArg (scaledOrdinary D) (congrArg (fun p : Fin m × (CutRing×CutRing) => p.2) h)

noncomputable def flagSiteBox {a m D : ℕ} {v : ℝ×ℝ} (R : ℝ) : Set (FlagSite a m D v) :=
  {z | |(flagSiteConjugate z).1|≤R ∧ |(flagSiteConjugate z).2|≤R}

theorem flagSiteNumerator_box {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {R : ℝ} (z : FlagSite a m D v) (hz : z∈flagSiteBox R) :
    (flagSiteNumerator z).1∈cutRectangle 0 (-(D:ℝ)*R) D (2*D*R) ∧
    (flagSiteNumerator z).2∈cutRectangle 0 (-(D:ℝ)*R) D (2*D*R) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have he₁ : ordinary (flagSiteNumerator z).1/(D:ℝ)=z.val.2.val.1 :=
    congrArg Prod.fst (flagSiteNumerator_spec z)
  have he₂ : ordinary (flagSiteNumerator z).2/(D:ℝ)=z.val.2.val.2 :=
    congrArg Prod.snd (flagSiteNumerator_spec z)
  have ho₁ := z.val.2.property.2.1
  have ho₂ := z.val.2.property.2.2.1
  have hc₁ := abs_le.mp hz.1
  have hc₂ := abs_le.mp hz.2
  change -R ≤ conjugate (flagSiteNumerator z).1/(D:ℝ) ∧
    conjugate (flagSiteNumerator z).1/(D:ℝ)≤R at hc₁
  change -R ≤ conjugate (flagSiteNumerator z).2/(D:ℝ) ∧
    conjugate (flagSiteNumerator z).2/(D:ℝ)≤R at hc₂
  rw [le_div_iff₀ hd,div_le_iff₀ hd] at hc₁ hc₂
  have he₁' := (div_eq_iff hd.ne').mp he₁
  have he₂' := (div_eq_iff hd.ne').mp he₂
  constructor <;> constructor <;> constructor <;>
    simp only [Set.mem_Icc] at * <;> nlinarith

theorem flagSiteBox_finite {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {R : ℝ} (hR : 0<R) : (flagSiteBox (a:=a) (m:=m) (D:=D) (v:=v) R).Finite := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have hf := cutRectangle_finite 0 (-(D:ℝ)*R) D (2*D*R) (by positivity)
  have hi : ((fun z : FlagSite a m D v => (z.val.1,flagSiteNumerator z)) '' flagSiteBox R).Finite := by
    refine ((Set.finite_univ : (Set.univ : Set (Fin m)).Finite).prod (hf.prod hf)).subset ?_
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨Set.mem_univ _,flagSiteNumerator_box hD z hz⟩
  exact hi.of_finite_image flagSite_key_injective.injOn

end FlagSiteCounts

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

noncomputable def cutCoordinates (a : ℕ) (j : Fin 4) : (CutRing×CutRing) ≃ (CutRing×CutRing) where
  toFun p := ![p,(p.2,p.1),(p.2-cutTau^a*p.1,p.1),(p.1-cutTau^a*p.2,p.2)] j
  invFun q := ![q,(q.2,q.1),(q.2,q.1+cutTau^a*q.2),(q.1+cutTau^a*q.2,q.2)] j
  left_inv p := by fin_cases j <;> simp
  right_inv p := by fin_cases j <;> simp

@[simp] theorem cutCoordinates_fst (a : ℕ) (j : Fin 4) (p : CutRing×CutRing) :
    (cutCoordinates a j p).1=integralCutForm a j p := by
  fin_cases j <;> simp [cutCoordinates,integralCutForm]

end DirectionStripCounts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagArrangementControl
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

section SquareAffineCharts
open Classical

theorem floor_add_unit {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (y : ℝ) :
    ⌊x+y⌋ = ⌊y⌋ + if x < 1-Int.fract y then 0 else 1 := by
  have hy₀ := Int.floor_le y
  have hy₁ := Int.lt_floor_add_one y
  by_cases h : x < 1-Int.fract y
  · rw [ite_eq_left h,add_zero]
    simp only [Int.fract] at h
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  · rw [ite_eq_right h]
    simp only [Int.fract] at h
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith

noncomputable def squareTranslationPeriod {a : ℕ} (u : CutRing×CutRing)
    (p : GenericSquare a) : ℤ×ℤ :=
  (⌊p.val.1+ordinary u.1⌋,⌊p.val.2+ordinary u.2⌋)

theorem squareTranslationPeriod_arrangement {a : ℕ} (u : CutRing×CutRing) :
    HasSquareArrangement (squareTranslationPeriod (a:=a) u) := by
  let c₁ : CutRing := (⌊ordinary u.1⌋:CutRing)+1-u.1
  let c₂ : CutRing := (⌊ordinary u.2⌋:CutRing)+1-u.2
  have hc₁ : ordinary c₁=1-Int.fract (ordinary u.1) := by simp only [c₁,map_sub,map_add,map_intCast,map_one,Int.fract]; ring
  have hc₂ : ordinary c₂=1-Int.fract (ordinary u.2) := by simp only [c₂,map_sub,map_add,map_intCast,map_one,Int.fract]; ring
  refine ⟨{(0,c₁),(1,c₂)},fun p q h => ?_⟩
  have h₁ := decide_eq_decide.mp (h (0,c₁) (by simp))
  have h₂ := decide_eq_decide.mp (h (1,c₂) (by simp))
  change (p.val.1<ordinary c₁ ↔ q.val.1<ordinary c₁) at h₁
  change (p.val.2<ordinary c₂ ↔ q.val.2<ordinary c₂) at h₂
  rw [hc₁] at h₁
  rw [hc₂] at h₂
  apply Prod.ext
  · change ⌊p.val.1+ordinary u.1⌋=⌊q.val.1+ordinary u.1⌋
    rw [floor_add_unit p.property.1.1 p.property.1.2,floor_add_unit q.property.1.1 q.property.1.2]
    simp only [h₁]
  · change ⌊p.val.2+ordinary u.2⌋=⌊q.val.2+ordinary u.2⌋
    rw [floor_add_unit p.property.2.1.1 p.property.2.1.2,floor_add_unit q.property.2.1.1 q.property.2.1.2]
    simp only [h₂]

theorem squareArrangement_pair {a : ℕ} {K J : Type*} {f : GenericSquare a → K} {g : GenericSquare a → J}
    (hf : HasSquareArrangement f) (hg : HasSquareArrangement g) :
    HasSquareArrangement (fun p => (f p,g p)) := by
  obtain ⟨S,hS⟩ := hf
  obtain ⟨T,hT⟩ := hg
  refine ⟨S∪T,fun p q h => Prod.ext (hS p q (fun l hl => h l (Finset.mem_union_left _ hl)))
    (hT p q (fun l hl => h l (Finset.mem_union_right _ hl)))⟩

theorem squareArrangement_finite_family {a : ℕ} {ι K : Type*} [Finite ι]
    (f : ι → GenericSquare a → K) (hf : ∀i,HasSquareArrangement (f i)) :
    HasSquareArrangement (fun p i => f i p) := by
  let := Fintype.ofFinite ι
  choose S hS using hf
  refine ⟨Finset.univ.biUnion S,fun p q h => funext (fun i => hS i p q (fun l hl => ?_))⟩
  exact h l (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hl⟩)

end SquareAffineCharts

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

theorem fullGroupSquareShift_exists {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) :
    ∃u : CutRing×CutRing,(g.val (i,p)).2.val=p.val+(ordinary u.1,ordinary u.2) := by
  obtain ⟨S,hS,hcover⟩ := g.property
  obtain ⟨c,hc,hi,hp⟩ := hcover (i,p)
  change i=c.source at hi
  refine ⟨c.shift-SquareStep.intPair (squareTranslationPeriod c.shift p),?_⟩
  rw [hi,hS c hc p hp]
  apply Prod.ext <;>
    simp only [translate,Int.fract,squareTranslationPeriod,SquareStep.intPair,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,map_sub,map_intCast] <;> ring

noncomputable def fullGroupSquareShift {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) : CutRing×CutRing :=
  (fullGroupSquareShift_exists g i p).choose

theorem fullGroupSquareShift_spec {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) :
    (g.val (i,p)).2.val=p.val+(ordinary (fullGroupSquareShift g i p).1,
      ordinary (fullGroupSquareShift g i p).2) := (fullGroupSquareShift_exists g i p).choose_spec

noncomputable def fullGroupAffineData {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) : Fin m × (CutRing×CutRing) :=
  ((g.val (i,p)).1,fullGroupSquareShift g i p)

theorem fullGroupAffineData_chart {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) (c : TableChart a m) (hc : c.Holds g.val)
    (hi : i=c.source) (hp : p∈c.domain.val) :
    fullGroupAffineData g i p=(c.target,c.shift-SquareStep.intPair (squareTranslationPeriod c.shift p)) := by
  have he : g.val (i,p)=(c.target,translate a c.shift p) := by rw [hi,hc p hp]
  unfold fullGroupAffineData
  apply Prod.ext
  · change (g.val (i,p)).1=c.target
    exact congrArg Prod.fst he
  · have hv := fullGroupSquareShift_spec g i p
    rw [he] at hv
    apply Prod.ext
    · apply ordinary_injective
      have hx := congrArg Prod.fst hv
      simpa only [translate,Int.fract,squareTranslationPeriod,SquareStep.intPair,
        Prod.fst_sub,Prod.fst_add,map_sub,map_intCast,add_sub_assoc,add_right_inj] using hx.symm
    · apply ordinary_injective
      have hx := congrArg Prod.snd hv
      simpa only [translate,Int.fract,squareTranslationPeriod,SquareStep.intPair,
        Prod.snd_sub,Prod.snd_add,map_sub,map_intCast,add_sub_assoc,add_right_inj] using hx.symm

theorem fullGroupAffineData_arrangement {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) : HasSquareArrangement (fullGroupAffineData g i) := by
  obtain ⟨S,hS,hcover⟩ := g.property
  let f (c : S) (p : GenericSquare a) := (decide (p∈c.val.domain.val),squareTranslationPeriod c.val.shift p)
  have hf (c : S) : HasSquareArrangement (f c) :=
    squareArrangement_pair (polygon_hasSquareArrangement c.val.domain.property)
      (squareTranslationPeriod_arrangement c.val.shift)
  obtain ⟨T,hT⟩ := squareArrangement_finite_family f hf
  refine ⟨T,fun p q h => ?_⟩
  obtain ⟨c,hc,hi,hp⟩ := hcover (i,p)
  have he := congrFun (hT p q h) ⟨c,hc⟩
  have hq : q∈c.domain.val := (decide_eq_decide.mp (congrArg Prod.fst he)).mp hp
  rw [fullGroupAffineData_chart g i p c (hS c hc) hi hp,
    fullGroupAffineData_chart g i q c (hS c hc) hi hq]
  exact congrArg (fun k => (c.target,c.shift-SquareStep.intPair k)) (congrArg Prod.snd he)

end FullGroupAffineData

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

section SignalActiveBox
open Classical

noncomputable def flagBoxFinset {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D) {R : ℝ} (hR : 0<R) :
    Finset (FlagSite a m D v) := (flagSiteBox_finite (v:=v) hD hR).toFinset

@[simp] theorem mem_flagBoxFinset {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D) {R : ℝ} (hR : 0<R)
    (z : FlagSite a m D v) : z∈flagBoxFinset hD hR ↔ z∈flagSiteBox R :=
  Set.Finite.mem_toFinset _

end SignalActiveBox

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FieldHS
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

section SourceFieldLaw
open Classical Matrix MeasureTheory Filter
open scoped Topology

noncomputable def sourceCommonSites {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) {L : ℝ} (hL : 0<L) (n : ℕ) : Finset (FlagSite a m D v) :=
  let J := flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL)
  J ∪ J.image (flagSitePermutation hD g)

end SourceFieldLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierSignals
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
section BarrierSignals
open Classical Set
open scoped ContDiff

noncomputable def conjugateLineForm (a : ℕ) (j : Fin 4) : (ℝ×ℝ) →L[ℝ] ℝ :=
  conjugate (lineNormal a j).1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    conjugate (lineNormal a j).2 • ContinuousLinearMap.snd ℝ ℝ ℝ

end BarrierSignals

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

section BarrierSignalGeometry
open Classical Set

noncomputable def finiteFirstMarks {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {N R : ℝ} (hN : 0<N) (hR : 0<R) (b : FlagSite a m D v → Bool) :
    Finset (FlagSite a m D v) := (flagBoxFinset hD (mul_pos hN hR)).filter (fun z => b z=true)

end BarrierSignalGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierSignalSystem
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
section BarrierSignalSystem
open Classical Set

structure BarrierSignalSystem (a : ℕ) (ha : 0 < a) (Q B : ℝ) where
  R₀ : ℝ
  R₁ : ℝ
  R₀_pos : 0 < R₀
  gap : R₀+1 < R₁
  first : FieldSignalData
  second : Fin 4 → FieldSignalData
  first_q : first.q=-3
  second_q : ∀j,(second j).q=-3
  first_pos : ∀x,‖x‖ ≤ R₀ → first.signal x=3
  first_neg : ∀x,R₁ ≤ ‖x‖ → first.signal x=-3
  second_pos : ∀j x,‖x‖ ≤ R₁ → |conjugateLineForm a j x| ≤ 1 → (second j).signal x=3
  second_neg : ∀j x,3  ≤  |conjugateLineForm a j x| → (second j).signal x=-3
  intersection_core : ∀N : ℝ,1 ≤ N → ∀i j : Fin 4,i ≠ j → ∀c d : CutRing,
    |conjugate c| ≤ 4*N+Q → |conjugate d| ≤ B → ∀p : ℝ×ℝ,
    conjugateLineForm a i p=conjugate c → conjugateLineForm a j p=conjugate d → ‖p‖ ≤ R₀*N
  incoming_core : ∀m : ℕ,∀i : Fin m,∀N : ℝ,1 ≤ N → ∀j : Fin 4,∀c : CutRing,
    ∀hc : c ∈ barrierCandidate a j N,‖flagSiteConjugate (barrierIncomingSite ha i hc)‖ ≤ R₀*N

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem R₁_pos : 0 < S.R₁ := by linarith [S.R₀_pos,S.gap]

noncomputable def marks {m : ℕ} {N : ℝ} (hN : 0 < N) (j : Fin 4)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :=
  finiteFirstMarks (commonVertexDenominator_pos ha) hN S.R₁_pos b

end BarrierSignalSystem
end BarrierSignalSystem

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ChartBoundaryEndpoints
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
section ChartBoundaryEndpoints
open Classical Set

def squareBoundaryCuts : Finset PlaneCut := {(0,0),(0,1),(1,0),(1,1)}

end ChartBoundaryEndpoints

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
section BarrierFiniteMenu
open Classical Set

noncomputable def barrierChartCuts {a m : ℕ} (g : polygonFullGroup a m) (i : Fin m) : Finset PlaneCut :=
  (fullGroupAffineData_arrangement g i).choose

structure BarrierMenu (a m : ℕ) (ha : 0 < a) (F : Finset (polygonFullGroup a m)) where
  Q : ℝ
  B : ℝ
  Q_nonneg : 0 ≤ Q
  B_nonneg : 0 ≤ B
  signals : BarrierSignalSystem a ha Q B
  shift_bound : ∀g ∈ F,∀i (p : GenericSquare a),∀j,
    |conjugate (integralCutForm a j (fullGroupAffineData g i p).2)| ≤ Q
  chart_bound : ∀g ∈ F,∀i (p : GenericSquare a),∀l ∈ barrierChartCuts g i ∪ squareBoundaryCuts,
    |conjugate l.2| ≤ B ∧ |conjugate (l.2+integralCutForm a l.1 (fullGroupAffineData g i p).2)| ≤ B

end BarrierFiniteMenu

section EightBarrierFields
open Classical MeasureTheory Filter Set
open scoped Topology

noncomputable def barrierEightDirections {a : ℕ} (ha : 0 < a) : Fin (4+4) → ℝ×ℝ :=
  Fin.addCases (barrierFlagDirection ha) (barrierFlagDirection ha)

noncomputable def BarrierSignalSystem.eight {a : ℕ} {ha : 0 < a} {Q B : ℝ}
    (S : BarrierSignalSystem a ha Q B) : Fin (4+4) → FieldSignalData :=
  Fin.addCases (fun _ => S.first) S.second

abbrev BarrierBits (a m : ℕ) (ha : 0 < a) :=
  ∀j : Fin (4+4),FlagSite a m (commonVertexDenominator a) (barrierEightDirections ha j) → Bool

def castFlagBits {a m D : ℕ} {v w : ℝ×ℝ} (e : v=w)
    (b : FlagSite a m D v → Bool) : FlagSite a m D w → Bool := fun z => b (e.symm ▸ z)

noncomputable def barrierFirstBits {a m : ℕ} {ha : 0 < a} (b : BarrierBits a m ha)
    (j : Fin 4) : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool :=
  castFlagBits (Fin.addCases_left j) (b (j.castAdd 4))

noncomputable def barrierSecondBits {a m : ℕ} {ha : 0 < a} (b : BarrierBits a m ha)
    (j : Fin 4) : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool :=
  castFlagBits (Fin.addCases_right j) (b (j.natAdd 4))

end EightBarrierFields

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_PartitionArrows
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
section PartitionArrows
open Classical Set

abbrev TrackPolygonPartition (a m : ℕ) := Fin m → FinitePolygonPartition a
end PartitionArrows

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FinitePowerGeneral
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def outerFunctor : Diagram C (Fin 3) ⥤ (Fin 2 → Diagram C (Fin 2)) :=
  Functor.pi' (fun i => reindex (outerOrder i))
noncomputable instance instBraidedFinOfNatNatForallOuterFunctor : (outerFunctor (C:=C)).Braided :=
  inferInstanceAs ((Functor.pi' (fun i : Fin 2 => reindex (C:=C) (outerOrder i))).Braided)
noncomputable instance instFaithfulFinOfNatNatForallOuterFunctor : (outerFunctor (C:=C)).Faithful where
  map_injective {X Y} f g h := by
    apply (eval (C:=C) 2).map_injective
    funext i
    fin_cases i
    · exact congrArg (fun h => ((eval (C:=C) 1).map (h (1:Fin 2))) 0) h
    · exact congrArg (fun h => ((eval (C:=C) 1).map (h (0:Fin 2))) 0) h
noncomputable instance instFullFinOfNatNatForallOuterFunctor : (outerFunctor (C:=C)).Full where
  map_surjective {X Y} f := by
    let g : (eval 2).obj X ⟶ (eval 2).obj Y := fun i =>
      if h:i=0 then by subst i; exact ((eval 1).map (f 1)) 0
      else by
        have hi:i=1 := by omega
        subst i
        exact ((eval 1).map (f 0)) 0
    refine ⟨(eval 2).preimage g,?_⟩
    funext i
    apply (eval (C:=C) 1).map_injective
    funext j
    have hj:j=0 := Subsingleton.elim _ _
    subst j
    fin_cases i
    · change ((eval 2).map ((eval 2).preimage g)) 1 = ((eval 1).map (f 0)) 0
      rw [Functor.map_preimage]
      simp only [g,dite_eq_right (show (1:Fin 2)≠0 by decide)]
      rfl
    · have h := congrArg (fun h=>h (0:Fin 2)) ((eval 2).map_preimage g)
      exact h
noncomputable instance instEssSurjFinOfNatNatForallOuterFunctor : (outerFunctor (C:=C)).EssSurj where
  mem_essImage Y := by
    let U : Fin 2 → C := fun i => if i=0 then ((eval 1).obj (Y 1)) 0 else ((eval 1).obj (Y 0)) 0
    let X := (eval (C:=C) 2).objPreimage U
    let e := (eval (C:=C) 2).objObjPreimageIso U
    refine ⟨X,⟨?_⟩⟩
    refine { hom := fun i=> ?_,inv := fun i=>?_,hom_inv_id := ?_,inv_hom_id := ?_ }
    · apply (eval 1).preimage
      intro j
      have hj:j=0 := Subsingleton.elim _ _
      subst j
      cases i using Fin.cases with
      | zero => exact e.hom 1
      | succ i =>
        have hi:i=0 := Subsingleton.elim _ _
        subst i
        exact e.hom 0
    · apply (eval 1).preimage
      intro j
      have hj:j=0 := Subsingleton.elim _ _
      subst j
      cases i using Fin.cases with
      | zero => exact e.inv 1
      | succ i =>
        have hi:i=0 := Subsingleton.elim _ _
        subst i
        exact e.inv 0
    · funext i
      apply (eval (C:=C) 1).map_injective
      change (eval 1).map (_ ≫ _) = (eval 1).map (𝟙 _)
      simp only [Functor.map_comp,Functor.map_preimage]
      funext j
      have hj:j=0 := Subsingleton.elim _ _
      subst j
      fin_cases i
      · change e.hom 1 ≫ e.inv 1 = 𝟙 _
        exact congrArg (fun f=>f (1:Fin 2)) e.hom_inv_id
      · change e.hom 0 ≫ e.inv 0 = 𝟙 _
        exact congrArg (fun f=>f (0:Fin 2)) e.hom_inv_id
    · funext i
      apply (eval (C:=C) 1).map_injective
      change (eval 1).map (_ ≫ _) = (eval 1).map (𝟙 _)
      simp only [Functor.map_comp,Functor.map_preimage]
      funext j
      have hj:j=0 := Subsingleton.elim _ _
      subst j
      fin_cases i
      · change e.inv 1 ≫ e.hom 1 = 𝟙 _
        exact congrArg (fun f=>f (1:Fin 2)) e.inv_hom_id
      · change e.inv 0 ≫ e.hom 0 = 𝟙 _
        exact congrArg (fun f=>f (0:Fin 2)) e.inv_hom_id
noncomputable instance instIsEquivalenceFinOfNatNatForallOuterFunctor : (outerFunctor (C:=C)).IsEquivalence where
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedNerve
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.reindexBraided _root_.OAI.RestrictedNerve.reindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_groupoid _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_isIso _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C) [W.IsMultiplicative]
noncomputable def diagonalIso : SimplicialDiagonal.nerveDiagonal.obj (horizontal W) ≅
    SimplicialDiagonal.nerveDiagonal.obj (vertical W) :=
  NatIso.ofComponents (fun p => Equiv.toIso {
    toFun := transpose W
    invFun := untranspose W
    left_inv := untranspose_transpose W
    right_inv := transpose_untranspose W }) (by
      intro p q f
      ext t
      refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      intro source target arrow
      erw [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply ObjectProperty.hom_ext
      ext index
      rfl)
noncomputable def constantDiagonalIso :
    SimplicialDiagonal.nerveDiagonal.obj ((Functor.const SimplexCategoryᵒᵖ).obj (Cat.of C)) ≅ nerve C :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_ResolutionAugmentation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory SimplicialObject Simplicial Opposite

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C) [W.IsMultiplicative]

def verticalAugmentation : SimplicialDiagonal.nerveDiagonal.obj (vertical W) ⟶ nerve C where
  app _ := ↾(verticalDiagonalFunctor W)
  naturality _ _ _ := by
    ext F
    refine CategoryTheory.Functor.ext (fun _=>rfl) ?_
    intro i j g
    erw [Category.id_comp, Category.comp_id]
    rfl

noncomputable def resolutionAugmentation :
    SimplicialDiagonal.nerveDiagonal.obj (horizontal W) ⟶ nerve C :=
  (diagonalIso W).hom ≫ verticalAugmentation W
variable {D:Type} [Groupoid.{0} D] (V:MorphismProperty D) [V.IsMultiplicative]
  (F:C⥤D) (hF:∀{X Y:C} (f:X⟶Y),W f→V (F.map f))
omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma verticalAugmentation_natural :
    SimplicialDiagonal.nerveDiagonal.map (verticalMapNat W V F hF) ≫ verticalAugmentation V =
      verticalAugmentation W ≫ nerveMap F := by
  ext n A
  refine CategoryTheory.Functor.ext (fun _=>rfl) ?_
  intro i j f
  erw [Category.id_comp, Category.comp_id]
  change F.map ((A.map f).hom.app i) ≫ F.map ((A.obj j).obj.map f) = F.map (_ ≫ _)
  rw [F.map_comp]
end

end RestrictedNerve

end OAI
end



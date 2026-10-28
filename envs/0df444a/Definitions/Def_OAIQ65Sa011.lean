-- Prove2me | Definitions.Def_OAIQ65Sa011
-- name    : OAIQ65Sa011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T03:20:27.889087+00:00
-- url     : https://prove2.me/theorems/a5038acf-e6df-455b-bea4-14994d24b8c1
-- title:
--   Definitions bundle OAIQ65Sa011 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 39 definitions, 3 inductive types or structures and 52 theorems. The definitions and types are `OAI.SimpleAmenable.FieldSignalData.bitLaw`, `OAI.SimpleAmenable.FieldSignalData.realLaw`, `OAI.SimpleAmenable.FlagSeparates`, `OAI.SimpleAmenable.FormalStarTable`, `OAI.SimpleAmenable.FormalStarTable.sector`, `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported`, `OAI.SimpleAmenable.InitialCoverSystem.AllPrimitiveLaws`, `OAI.SimpleAmenable.InitialCoverSystem.SlotRouting`, `OAI.SimpleAmenable.InitialCoverSystem.SlotRouting.star`, `OAI.SimpleAmenable.InitialCoverSystem.TangentChartLaws`, `OAI.SimpleAmenable.InitialCoverSystem.constantReindexedFrame`, `OAI.SimpleAmenable.InitialCoverSystem.distinctSlotStar`, `OAI.SimpleAmenable.InitialCoverSystem.frameStar`, `OAI.SimpleAmenable.InitialCoverSystem.geometricFrameGroup`, `OAI.SimpleAmenable.InitialCoverSystem.polygonStar`, `OAI.SimpleAmenable.InitialCoverSystem.privateRoutingFactor`, `OAI.SimpleAmenable.InitialCoverSystem.privateRoutingWord`, `OAI.SimpleAmenable.InitialCoverSystem.tangentSign`, `OAI.SimpleAmenable.OffsetFrame`, `OAI.SimpleAmenable.OffsetFrame.restrict`, `OAI.SimpleAmenable.OffsetFrame.zero`, `OAI.SimpleAmenable.SmallSupported`, `OAI.SimpleAmenable.balancedOffsetFrame`, `OAI.SimpleAmenable.clippingOverlapLower`, `OAI.SimpleAmenable.clippingOverlapUpper`, `OAI.SimpleAmenable.flagAveragingMatrix`, `OAI.SimpleAmenable.flagChamber`, `OAI.SimpleAmenable.flagMeanSignal`, `OAI.SimpleAmenable.flagSiteOrdinary`, `OAI.SimpleAmenable.frameDomain`, `OAI.SimpleAmenable.genericBox`, `OAI.SimpleAmenable.orderedTrackHom`, `OAI.SimpleAmenable.privateCycleStar`, `OAI.SimpleAmenable.scaledSiteConjugate`, `OAI.SimpleAmenable.separatorMatrix`, `OAI.SimpleAmenable.signedShortSteps`, `OAI.SimpleAmenable.sourceBitFieldLaw`, `OAI.SimpleAmenable.sourceFlagMatrix`, `OAI.SimpleAmenable.sourceSmoothFieldLaw`, `OAI.SimpleAmenable.tangentChartTemplate` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_CentralCovers_BooleanCoordinateGeneration`, `SimpleAmenable_CentralCovers_CommonFrameTransport`, `SimpleAmenable_CentralCovers_ControlCalculus`, `SimpleAmenable_CentralCovers_FormalStarTables`, `SimpleAmenable_CentralCovers_FrameActions`, `SimpleAmenable_CentralCovers_GeometricSectors`, `SimpleAmenable_CentralCovers_PrimitiveCentralLaws`, `SimpleAmenable_CentralCovers_PrimitiveCopies`, `SimpleAmenable_CentralCovers_PrimitiveGeometricGeneration`, `SimpleAmenable_CentralCovers_PrimitiveTable`, `SimpleAmenable_Configurations_DistinctSlotStars`, `SimpleAmenable_Configurations_RepeatedTrackRouting`, `SimpleAmenable_Homology_FinitePrimitiveResolution`, `SimpleAmenable_PolygonGeometry_ClosedChartOverlap`, `SimpleAmenable_PolygonGeometry_CommonTranslatedCopies`, `SimpleAmenable_PolygonGeometry_FlagSeparatingLevels`, `SimpleAmenable_PolygonGeometry_FrameDisjointness`, `SimpleAmenable_PolygonGeometry_OffsetFrames`, `SimpleAmenable_PolygonGeometry_PrivateBankWord`, `SimpleAmenable_PolygonGeometry_RoutingIndependence`, `SimpleAmenable_PolygonGeometry_SmallControlCalculus`, `SimpleAmenable_PolygonGeometry_SpatialChartGeometry`, `SimpleAmenable_PolygonGeometry_TangentChartTemplates`, `SimpleAmenable_PolygonGeometry_TentMatrixPositivity`, `SimpleAmenable_RandomFields_CovarianceLimit`, `SimpleAmenable_RandomFields_FieldHS`, `SimpleAmenable_RandomFields_FieldSignalData`, `SimpleAmenable_RandomFields_FlagAveragingMatrices`, `SimpleAmenable_RandomFields_FlagSignalEnergy`, `SimpleAmenable_RandomFields_PrimitiveCovariance`, `SimpleAmenable_RandomFields_RecoveredConstantCovariance`, `SimpleAmenable_RandomFields_ThresholdField`, `SimpleAmenable_Simplicial_SmallEvenRouting`.
--
--   **Imports.** It imports the bundle `OAIQ65Sa008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa013` and `OAIQ65Sa014`; the statements `OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport`, `OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_inactive_clipped_model_action_neighborhood`, `OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_primitive_table_with_coordinates`, `OAI.SimpleAmenable.InitialCoverSystem.actual_template_actual_word_controls`, `OAI.SimpleAmenable.InitialCoverSystem.actual_template_word_controls`, `OAI.SimpleAmenable.InitialCoverSystem.all_rectangle_control_to_sign`, `OAI.SimpleAmenable.InitialCoverSystem.all_rectangle_control_to_template`, `OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations`, `OAI.SimpleAmenable.InitialCoverSystem.chart_action_transfer`, `OAI.SimpleAmenable.InitialCoverSystem.control_trans`, `OAI.SimpleAmenable.InitialCoverSystem.coverMap_kernel_central`, `OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law`, `OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform`, `OAI.SimpleAmenable.InitialCoverSystem.tangentSign_step_action_closed`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_interval_action`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_transport_uniform_cover_uniform`, `OAI.SimpleAmenable.finiteSignalFields_transport`, `OAI.SimpleAmenable.formal_pairs_assemble` and `OAI.SimpleAmenable.tangentChartTables_eventually`; the proofs of `OAI.SimpleAmenable.AxisAnchorFamily.atoms_commute`, `OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport`, `OAI.SimpleAmenable.ClippedGerm.model_restrict_gate`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons_assignment_realized`, `OAI.SimpleAmenable.CoordinateGerm.model_formula`, `OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_inactive_clipped_model_action_neighborhood`, `OAI.SimpleAmenable.InitialCoverSystem.actual_template_actual_word_controls`, `OAI.SimpleAmenable.InitialCoverSystem.actual_template_word_controls`, `OAI.SimpleAmenable.InitialCoverSystem.all_rectangle_control_to_sign`, `OAI.SimpleAmenable.InitialCoverSystem.all_rectangle_control_to_template`, `OAI.SimpleAmenable.InitialCoverSystem.chart_action_transfer`, `OAI.SimpleAmenable.InitialCoverSystem.control_trans`, `OAI.SimpleAmenable.InitialCoverSystem.gridInputs_normalize`, `OAI.SimpleAmenable.InitialCoverSystem.grid_formal_patching_templates`, `OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law`, `OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform`, `OAI.SimpleAmenable.InitialCoverSystem.pair_formal_quotient`, `OAI.SimpleAmenable.InitialCoverSystem.tangentSign_step_action_closed`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_interval_action`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_transport_uniform_cover_uniform` and `OAI.SimpleAmenable.initialCoverSystem_eventually`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa008

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_BooleanCoordinateGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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

theorem coordinate_cuts_generated {a : ℕ} (B : BooleanSubalgebra (Set (GenericSquare a)))
    (j : Fin 2) (htrans : ∀ u U, U ∈ B → translate a u ⁻¹' U ∈ B)
    (hprimitive : (coordinatePrimitive a j).val ∈ B) (z : CutRing) :
    halfPlane a (Fin.castLE (by omega) j) z ∈ B := by
  classical
  have hsymm {U V : Set (GenericSquare a)} (hU : U ∈ B) (hV : V ∈ B) :
      symmDiff U V ∈ B := by
    rw [Set.symmDiff_def]
    exact BooleanSubalgebra.sup_mem (BooleanSubalgebra.sdiff_mem hU hV)
      (BooleanSubalgebra.sdiff_mem hV hU)
  let H : AddSubgroup CutRing := {
    carrier := {u | coordinateArc a j u ∈ B}
    zero_mem' := by
      change coordinateArc a j 0 ∈ B
      rw [coordinateArc_zero_of_fract j 0 (by simp)]
      exact BooleanSubalgebra.bot_mem
    add_mem' := by
      intro u v hu hv
      change coordinateArc a j (u+v) ∈ B
      rw [coordinateArc_add]
      split_ifs
      · exact hsymm hu (htrans _ _ hv)
      · exact BooleanSubalgebra.compl_mem (hsymm hu (htrans _ _ hv))
    neg_mem' := by
      intro u hu
      change coordinateArc a j (-u) ∈ B
      by_cases hzero : Int.fract (ordinary u) = 0
      · have hh : Int.fract (ordinary (-u)) = 0 := by
          rw [map_neg,Int.fract_neg_eq_zero.mpr hzero]
        rw [coordinateArc_zero_of_fract j (-u) hh]
        exact BooleanSubalgebra.bot_mem
      · rw [coordinateArc_neg j u hzero]
        exact BooleanSubalgebra.compl_mem (htrans _ _ hu) }
  have hτ : cutTau ∈ H := by
    have hfloor : ⌊Real.goldenRatio⌋ = (1 : ℤ) :=
      Int.floor_eq_iff.mpr ⟨by norm_num; exact Real.one_lt_goldenRatio.le,by norm_num; exact Real.goldenRatio_lt_two⟩
    have he : coordinateArc a j cutTau = (coordinatePrimitive a j).val := by
      ext p
      have hp := (coordinate_bounds j p).1
      fin_cases j <;>
        simp [coordinateArc,coordinate,coordinatePrimitive,halfPlane,cutForm,
          Int.fract,hfloor,ordinary_cutTau] <;> intro _ <;> exact hp
    change coordinateArc a j cutTau ∈ B
    rw [he]
    exact hprimitive
  have hint (n : ℤ) : (n : CutRing) ∈ H := by
    change coordinateArc a j (n : CutRing) ∈ B
    rw [coordinateArc_zero_of_fract j _ (by simp)]
    exact BooleanSubalgebra.bot_mem
  have hall (u : CutRing) : coordinateArc a j u ∈ B := by
    have he : u = (u.re : CutRing) + u.im • cutTau := by
      apply QuadraticAlgebra.ext <;> simp [cutTau]
    change u ∈ H
    rw [he]
    exact H.add_mem (hint _) (H.zsmul_mem hτ _)
  have hcoord : ∀ p : GenericSquare a,
      cutForm a (Fin.castLE (by omega) j) p.val = coordinate j p := by
    intro p
    fin_cases j <;> rfl
  by_cases hz0 : ordinary z ≤ 0
  · have he : halfPlane a (Fin.castLE (by omega) j) z = ∅ := by
      ext p
      simp only [halfPlane,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_lt,hcoord]
      exact hz0.trans (coordinate_bounds j p).1
    rw [he]
    exact BooleanSubalgebra.bot_mem
  by_cases hz1 : 1 ≤ ordinary z
  · have he : halfPlane a (Fin.castLE (by omega) j) z = Set.univ := by
      ext p
      simp only [halfPlane,Set.mem_ofPred_eq,Set.mem_univ,iff_true,hcoord]
      exact (coordinate_bounds j p).2.trans_le hz1
    rw [he]
    exact BooleanSubalgebra.top_mem
  have he : halfPlane a (Fin.castLE (by omega) j) z = coordinateArc a j z := by
    ext p
    simp only [halfPlane,coordinateArc,Set.mem_ofPred_eq,hcoord,
      Int.fract_eq_self.mpr (show 0 ≤ ordinary z ∧ ordinary z < 1 by constructor <;> linarith)]
  rw [he]
  exact hall z

end BooleanCoordinateGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveGeometricGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

theorem mem_clippedSlope_lift {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (p : GenericSquare a) (t : ℝ × ℝ)
    (ht : (-ordinary r < t.1 ∧ t.1 < ordinary r) ∧
      (-ordinary r < t.2 ∧ t.2 < ordinary r))
    (hp : p.val = (Int.fract t.1,Int.fract t.2)) :
    p ∈ (clippedSlopePrimitive a r j).val ↔ 0 ≤ cutForm a j t := by
  classical
  have hform (k : Fin 2 × Fin 2)
      (hk : (p.val.1-k.1.val,p.val.2-k.2.val) = t) :
      cutForm a j p.val - ordinary (integralCutForm a j (k.1.val,k.2.val)) =
        cutForm a j t := by
    rw [← cutForm_ordinary,← cutForm_sub]
    simpa only [map_natCast,Prod.sub_def] using congrArg (cutForm a j) hk
  constructor
  · intro h
    obtain ⟨k,hk,hside⟩ := Set.mem_iUnion.mp h
    have hb := (mem_circularBoxPiece r k p).mp hk
    have he : (p.val.1-k.1.val,p.val.2-k.2.val) = t := by
      apply Prod.ext
      · simpa only [hp] using fract_small_lift_unique hr ht.1 k.1 (by simpa only [hp] using hb.1)
      · simpa only [hp] using fract_small_lift_unique hr ht.2 k.2 (by simpa only [hp] using hb.2)
    have hs : ordinary (integralCutForm a j (k.1.val,k.2.val)) ≤ cutForm a j p.val := not_lt.mp hside
    linarith [hform k he]
  · intro h
    obtain ⟨kx,hx⟩ := fract_small_lift hr ht.1
    obtain ⟨ky,hy⟩ := fract_small_lift hr ht.2
    let k : Fin 2 × Fin 2 := (kx,ky)
    have he : (p.val.1-k.1.val,p.val.2-k.2.val) = t := by
      simp [hp,k,hx,hy]
    apply Set.mem_iUnion.mpr
    refine ⟨k,(mem_circularBoxPiece r k p).mpr ?_,?_⟩
    · have h1 : p.val.1-k.1.val = t.1 := congrArg Prod.fst he
      have h2 : p.val.2-k.2.val = t.2 := congrArg Prod.snd he
      constructor <;> constructor <;> linarith [ht.1.1,ht.1.2,ht.2.1,ht.2.2]
    · change ¬cutForm a j p.val < ordinary (integralCutForm a j (k.1.val,k.2.val))
      linarith [hform k he]

theorem translated_clippedSlope_local {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (u : CutRing × CutRing)
    (p : GenericSquare a)
    (hp : (-ordinary r < p.val.1-ordinary u.1 ∧ p.val.1-ordinary u.1 < ordinary r) ∧
      (-ordinary r < p.val.2-ordinary u.2 ∧ p.val.2-ordinary u.2 < ordinary r)) :
    translate a (-u) p ∈ (clippedSlopePrimitive a r j).val ↔
      ordinary (integralCutForm a j u) ≤ cutForm a j p.val := by
  rw [mem_clippedSlope_lift r j hr (translate a (-u) p)
    (p.val - (ordinary u.1,ordinary u.2)) hp (by simp [sub_eq_add_neg])]
  rw [cutForm_sub,cutForm_ordinary]
  exact sub_nonneg

theorem exists_cut_parameter (f : ℝ → ℝ × ℝ) (hf : Continuous f)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : CutRing, dist (f (ordinary u)) (f x) < ε := by
  exact ordinary_denseRange.exists_mem_open (hf.isOpen_preimage _ Metric.isOpen_ball)
    ⟨x,by simpa using hε⟩

theorem slope_line_anchor (a : ℕ) (j : Fin 4) (hj : j = 2 ∨ j = 3)
    (z : CutRing) (p : ℝ × ℝ) (hp : cutForm a j p = ordinary z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : CutRing × CutRing, integralCutForm a j u = z ∧
      dist (ordinary u.1,ordinary u.2) p < ε := by
  rcases hj with rfl | rfl
  · let f : ℝ → ℝ × ℝ := fun x => (x,ordinary z + Real.goldenRatio^a*x)
    have hf : Continuous f := continuous_id.prodMk (continuous_const.add (continuous_const.mul continuous_id))
    obtain ⟨u,hu⟩ := exists_cut_parameter f hf p.1 hε
    have he : f p.1 = p := by
      apply Prod.ext
      · rfl
      · change ordinary z + Real.goldenRatio^a*p.1 = p.2
        simp [cutForm] at hp
        linarith
    refine ⟨(u,z+cutTau^a*u),?_,?_⟩
    · simp [integralCutForm]
    · simpa only [f,map_add,map_mul,map_pow,ordinary_cutTau,he] using hu
  · let f : ℝ → ℝ × ℝ := fun y => (ordinary z + Real.goldenRatio^a*y,y)
    have hf : Continuous f := (continuous_const.add (continuous_const.mul continuous_id)).prodMk continuous_id
    obtain ⟨u,hu⟩ := exists_cut_parameter f hf p.2 hε
    have he : f p.2 = p := by
      apply Prod.ext
      · change ordinary z + Real.goldenRatio^a*p.2 = p.1
        simp [cutForm] at hp
        linarith
      · rfl
    refine ⟨(z+cutTau^a*u,u),?_,?_⟩
    · simp [integralCutForm]
    · simpa only [f,map_add,map_mul,map_pow,ordinary_cutTau,he] using hu

noncomputable def genericBox (a : ℕ) (l h : CutRing × CutRing) : Set (GenericSquare a) :=
  Subtype.val ⁻¹' ordinaryBox l h

theorem genericBox_eq {a : ℕ} (l h : CutRing × CutRing) : genericBox a l h =
    ((halfPlane a 0 l.1)ᶜ ∩ halfPlane a 0 h.1) ∩
      ((halfPlane a 1 l.2)ᶜ ∩ halfPlane a 1 h.2) := by
  ext p
  have hx : p.val.1 ≠ ordinary l.1 := p.property.2.2 0 l.1
  have hy : p.val.2 ≠ ordinary l.2 := p.property.2.2 1 l.2
  simp only [genericBox,ordinaryBox,
    Set.mem_inter_iff,Set.mem_compl_iff,halfPlane,Set.mem_ofPred_eq,cutForm,
    Matrix.cons_val_zero,Matrix.cons_val_one,not_lt]
  exact and_congr (and_congr (lt_iff_le_and_ne.trans (and_iff_left hx.symm)) Iff.rfl)
    (and_congr (lt_iff_le_and_ne.trans (and_iff_left hy.symm)) Iff.rfl)

theorem genericBox_mem {a : ℕ} (B : BooleanSubalgebra (Set (GenericSquare a)))
    (hcoord : ∀ (j : Fin 2) z, halfPlane a (Fin.castLE (by omega) j) z ∈ B)
    (l h : CutRing × CutRing) : genericBox a l h ∈ B := by
  rw [genericBox_eq]
  exact BooleanSubalgebra.inf_mem
    (BooleanSubalgebra.inf_mem (BooleanSubalgebra.compl_mem (hcoord 0 l.1)) (hcoord 0 h.1))
    (BooleanSubalgebra.inf_mem (BooleanSubalgebra.compl_mem (hcoord 1 l.2)) (hcoord 1 h.2))

theorem halfPlane_locally_generated {a : ℕ} (r : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (B : BooleanSubalgebra (Set (GenericSquare a)))
    (htrans : ∀ u U, U ∈ B → translate a u ⁻¹' U ∈ B)
    (j : Fin 4) (hj : j = 2 ∨ j = 3)
    (hprimitive : (clippedSlopePrimitive a r j).val ∈ B)
    (z : CutRing) (p : ℝ × ℝ) :
    ∃ l h : CutRing × CutRing, ∃ D : Set (GenericSquare a),
      p ∈ ordinaryBox l h ∧ D ∈ B ∧
      ∀ q : GenericSquare a, q.val ∈ ordinaryBox l h →
        (q ∈ halfPlane a j z ↔ q ∈ D) := by
  rcases lt_trichotomy (cutForm a j p) (ordinary z) with hp | hp | hp
  · obtain ⟨l,h,hl,hsub⟩ := exists_box_in_open
      (isOpen_lt (cutForm_continuous a j) continuous_const) p hp
    refine ⟨l,h,Set.univ,hl,BooleanSubalgebra.top_mem,?_⟩
    intro q hq
    exact iff_true_intro (hsub hq)
  · obtain ⟨u,hu,hup⟩ := slope_line_anchor a j hj z p hp hr.1
    have hpU : p ∈ {q : ℝ × ℝ |
        (-ordinary r < q.1-ordinary u.1 ∧ q.1-ordinary u.1 < ordinary r) ∧
        (-ordinary r < q.2-ordinary u.2 ∧ q.2-ordinary u.2 < ordinary r)} := by
      change max (dist (ordinary u.1) p.1) (dist (ordinary u.2) p.2) < ordinary r at hup
      rw [max_lt_iff,Real.dist_eq,Real.dist_eq,abs_lt,abs_lt] at hup
      exact ⟨⟨by linarith [hup.1.2],by linarith [hup.1.1]⟩,
        ⟨by linarith [hup.2.2],by linarith [hup.2.1]⟩⟩
    have hU : IsOpen {q : ℝ × ℝ |
        (-ordinary r < q.1-ordinary u.1 ∧ q.1-ordinary u.1 < ordinary r) ∧
        (-ordinary r < q.2-ordinary u.2 ∧ q.2-ordinary u.2 < ordinary r)} :=
      ((isOpen_lt continuous_const (continuous_fst.sub continuous_const)).inter
        (isOpen_lt (continuous_fst.sub continuous_const) continuous_const)).inter
      ((isOpen_lt continuous_const (continuous_snd.sub continuous_const)).inter
        (isOpen_lt (continuous_snd.sub continuous_const) continuous_const))
    obtain ⟨l,h,hl,hsub⟩ := exists_box_in_open hU p hpU
    refine ⟨l,h,(translate a (-u) ⁻¹' (clippedSlopePrimitive a r j).val)ᶜ,hl,
      BooleanSubalgebra.compl_mem (htrans _ _ hprimitive),?_⟩
    intro q hq
    change cutForm a j q.val < ordinary z ↔ ¬translate a (-u) q ∈ (clippedSlopePrimitive a r j).val
    rw [translated_clippedSlope_local r j hr u q (hsub hq),hu,not_le]
  · obtain ⟨l,h,hl,hsub⟩ := exists_box_in_open
      (isOpen_lt continuous_const (cutForm_continuous a j)) p hp
    refine ⟨l,h,∅,hl,BooleanSubalgebra.bot_mem,?_⟩
    intro q hq
    change cutForm a j q.val < ordinary z ↔ False
    exact iff_false_intro (not_lt.mpr (le_of_lt (hsub hq)))

theorem slope_cuts_generated {a : ℕ} (r : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (B : BooleanSubalgebra (Set (GenericSquare a)))
    (htrans : ∀ u U, U ∈ B → translate a u ⁻¹' U ∈ B)
    (hcoord : ∀ (j : Fin 2) z, halfPlane a (Fin.castLE (by omega) j) z ∈ B)
    (j : Fin 4) (hj : j = 2 ∨ j = 3)
    (hprimitive : (clippedSlopePrimitive a r j).val ∈ B) (z : CutRing) :
    halfPlane a j z ∈ B := by
  classical
  choose l h D hp hD he using halfPlane_locally_generated r hr B htrans j hj hprimitive z
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun p => ordinaryBox (l p) (h p))
    (fun _ => isOpen_Ioo.prod isOpen_Ioo) (by intro p _; exact Set.mem_iUnion.mpr ⟨p,hp p⟩)
  have heq : halfPlane a j z = ⋃ p ∈ s, genericBox a (l p) (h p) ∩ D p := by
    ext q
    constructor
    · intro hq
      have hqK : q.val ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
        ⟨⟨q.property.1.1,q.property.1.2.le⟩,⟨q.property.2.1.1,q.property.2.1.2.le⟩⟩
      obtain ⟨p,hps,hqp⟩ := Set.mem_iUnion₂.mp (hs hqK)
      exact Set.mem_iUnion₂.mpr ⟨p,hps,hqp,(he p q hqp).mp hq⟩
    · intro hq
      obtain ⟨p,_,hqp,hqD⟩ := Set.mem_iUnion₂.mp hq
      exact (he p q hqp).mpr hqD
  rw [heq]
  exact BooleanSubalgebra.biSup_mem s.finite_toSet (fun p _ =>
    BooleanSubalgebra.inf_mem (genericBox_mem B hcoord _ _) (hD p))

end PrimitiveGeometricGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveCopies
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
section PrimitiveCopies

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem initialAlphabet_aligned (I : Finset (Fin (m+1))) (j : Fin 5)
    (s : alternatingGroup I) :
    B.initialAlphabet I j s ∈ sourceAlignedGroup a r m hm M B.t I := by
  have hle : Subgroup.closure {g : alternatingGroup I | Equiv.Perm.IsThreeCycle g.val} ≤
      (sourceAlignedGroup a r m hm M B.t I).comap (B.initialAlphabet I j) := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change B.initialConditional j (subtypeAlternatingHom I g) ∈
      sourceAlignedGroup a r m hm M B.t I
    have hc : (subtypeAlternatingHom I g).val.support.card ≤ 5 := by
      change (Equiv.Perm.ofSubtype g.val).support.card ≤ 5
      have hI : (Subtype.fintype (fun x : Fin (m+1) => x ∈ I)) =
          (inferInstance : Fintype I) := Subsingleton.elim _ _
      rw [Equiv.Perm.support_ofSubtype, Finset.card_map, hI, hg.card_support]
      decide
    rw [B.initialConditional_input j _ hc]
    exact alignedGroup_input _ _ _
      ((j,⟨(subtypeAlternatingHom I g).val,(subtypeAlternatingHom I g).property,hc⟩) :
        SmallConditional m)
      (Equiv.Perm.mem_range_ofSubtype_iff.mp ⟨g.val,rfl⟩)
  rw [alternatingGroup.closure_isThreeCycles_eq_top] at hle
  exact hle (Subgroup.mem_top s)

theorem translatedAlphabet_aligned (I : Finset (Fin (m+1))) (j : Fin 5)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) (s : alternatingGroup I) :
    B.translatedAlphabet I j k s ∈ sourceAlignedGroup a r m hm M B.t I :=
  alignedGroup_conjugate _ _ _ k (B.initialAlphabet_aligned I j s)

end InitialCoverSystem
end PrimitiveCopies

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CommonTranslatedCopies
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
section CommonTranslatedCopies

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem primitiveCopy_aligned (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (p : Fin 5 × (CutRing × CutRing)) (s : alternatingGroup I) :
    B.primitiveCopy I b hb p s ∈ sourceAlignedGroup a r m hm M B.t I :=
  B.translatedAlphabet_aligned I p.1 _ s

end InitialCoverSystem
end CommonTranslatedCopies

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PrimitiveCovariance
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
section PrimitiveCovariance

theorem spatialTranslate_add {a : ℕ} (u v : CutRing × CutRing) (U : polygonAlgebra a) :
    spatialTranslate (u+v) U = spatialTranslate u (spatialTranslate v U) := by
  apply Subtype.ext
  ext x
  change translate a (-(u+v)) x ∈ U.val ↔ translate a (-v) (translate a (-u) x) ∈ U.val
  rw [← translate_add,neg_add,add_comm]

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem primitiveCopy_translate_eq (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (j : Fin 5) (u v : CutRing × CutRing)
    (huv : spatialTranslate u (initialTest a r j) = spatialTranslate v (initialTest a r j)) :
    B.primitiveCopy I b hb (j,u) = B.primitiveCopy I b hb (j,v) :=
  B.commonTranslatedAlphabet_independent (commonFrame a r m hm I b hb u)
    (commonFrame a r m hm I b hb v) j huv

theorem translatedAlphabet_mul (I : Finset (Fin (m+1))) (j : Fin 5)
    (k l : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    B.translatedAlphabet I j (k*l) =
      (MulAut.conj (B.t k)).toMonoidHom.comp (B.translatedAlphabet I j l) := by
  ext s
  change B.t (k*l) * B.initialAlphabet I j s * (B.t (k*l))⁻¹ =
    B.t k * (B.t l * B.initialAlphabet I j s * (B.t l)⁻¹) * (B.t k)⁻¹
  rw [map_mul]
  group

theorem primitiveCopy_zero (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (j : Fin 5) :
    B.primitiveCopy I b hb (j,0) = B.initialAlphabet I j := by
  let F : CommonFrame a r m hm I 0 := {
    k := 1
    d := 0
    projection := by simp
    common := by simp }
  rw [B.primitiveCopy_frame I b hb _ F]
  ext s
  change B.t 1 * B.initialAlphabet I j s * (B.t 1)⁻¹ = B.initialAlphabet I j s
  simp

end InitialCoverSystem
end PrimitiveCovariance

section FamilyCovariance

variable {ι E H Q : Type*} [Group E] [Group H] [Group Q]

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem PrimitiveFamilyLaw.congr_offsets (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P Q : ι → Fin 5 × (CutRing × CutRing))
    (hj : ∀ i, (P i).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P i).2 (initialTest a r (P i).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1))
    (h : B.PrimitiveFamilyLaw I b hb P) : B.PrimitiveFamilyLaw I b hb Q := by
  have he : B.primitiveFamily I b hb P = B.primitiveFamily I b hb Q := by
    funext i
    cases i with
    | none => rfl
    | some i =>
      change B.primitiveCopy I b hb (P i) = B.primitiveCopy I b hb (Q i)
      have he : P i = ((Q i).1,(P i).2) := Prod.ext (hj i) rfl
      rw [he]
      exact B.primitiveCopy_translate_eq I b hb (Q i).1 (P i).2 (Q i).2
        (by simpa only [hj i] using hp i)
  unfold PrimitiveFamilyLaw at h ⊢
  rwa [← he]

end InitialCoverSystem
end FamilyCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveTable
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
section ActualPrimitiveTable

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {ι : Type*} [Finite ι]

namespace InitialCoverSystem

variable (B : InitialCoverSystem a r m hm M)

omit [Finite ι] in
theorem primitiveFamily_aligned (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) :
    (copyFamilyEval (B.primitiveFamily I b hb P)).range ≤
      sourceAlignedGroup a r m hm M B.t I := by
  rw [copyFamilyEval_range]
  apply iSup_le
  intro i s hs
  obtain ⟨t,rfl⟩ := hs
  cases i with
  | none => exact B.initialAlphabet_aligned I 0 t
  | some j => exact B.primitiveCopy_aligned I b hb (P j) t

end InitialCoverSystem
end ActualPrimitiveTable

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GeometricSectors
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
section GeometricSectors

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {ι : Type*} [Finite ι]

namespace InitialCoverSystem

variable (B : InitialCoverSystem a r m hm M)

theorem geometricSector_aligned (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup I)) :
    B.geometricSector I b hb P h V s ∈ sourceAlignedGroup a r m hm M B.t I :=
  B.primitiveFamily_aligned I b hb P (B.geometricSector_mem I b hb P h V s)

end InitialCoverSystem
end GeometricSectors

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

def SmallSupported (L : Finset α → Subgroup H) (f : TrackStar α →* H) : Prop :=
  ∀ I : ControlAlphabet α, (f.comp (universalMap (subtypeAlternatingHom I.val))).range ≤ L I.val

end SmallControlCalculus

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ControlCalculus
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
section SourceControlCalculus
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

abbrev AlignedSmallSupported (f : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)) : Prop :=
  SmallSupported (sourceAlignedGroup a r m hm M B.t) f

end InitialCoverSystem
end SourceControlCalculus

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SpatialChartGeometry
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

section ChartTransforms

theorem spatialTranslate_resolved {a : ℕ} {ι : Type*}
    (U : ι → polygonAlgebra a) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (U i).val) V.val) (z : CutRing × CutRing) :
    ResolvedBy (fun i => (spatialTranslate z (U i)).val) (spatialTranslate z V).val := by
  intro x y he
  exact hV (translate a (-z) x) (translate a (-z) y) he

end ChartTransforms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TangentChartTemplates
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
section TangentChartTemplates

noncomputable def tangentChartTemplate (a k : ℕ) (p : Fin 2 → ℤ) (d : Fin 2) (e : CutRing) :
    Fin 2 ⊕ (Fin 2 × Fin (k-1)) → Fin 5 × (CutRing × CutRing)
  | Sum.inl i => (slopeTestIndex d,if i=0 then 0 else tangentOffset a d e)
  | Sum.inr i => coordinateWindowPrimitives k p i

noncomputable def translatedTemplate {ι : Type*}
    (P : ι → Fin 5 × (CutRing × CutRing)) (z : CutRing × CutRing) :
    ι → Fin 5 × (CutRing × CutRing) := fun i => ((P i).1,z+(P i).2)

noncomputable def signedShortSteps (u : CutRing) : Fin 5 → CutRing := ![0,u,-u,cutTau*u,-(cutTau*u)]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

def TangentChartLaws (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) : Prop :=
  ∀ d e z I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)

noncomputable def tangentSign (hlarge : 15 < m+1) (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing)
    (h : B.TangentChartLaws k p u) (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u 0)) z)
    (h d 0 z) (if positive then spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d))
      else (spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d)))ᶜ)

end InitialCoverSystem
end TangentChartTemplates

section TangentChartAction

theorem translatedTemplate_resolved {a : ℕ} {r : CutRing} {ι : Type*}
    (P : ι → Fin 5 × (CutRing × CutRing)) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r) P i).val) V.val)
    (z : CutRing × CutRing) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (translatedTemplate P z) i).val) (spatialTranslate z V).val := by
  simpa only [InitialCoverSystem.primitiveTests,primitiveFamilyTests,translatedTemplate,
    ← spatialTranslate_add] using spatialTranslate_resolved
      (InitialCoverSystem.primitiveTests (a := a) (r := r) P) V hV z

end TangentChartAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalStarTables
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
section FormalStarTables
variable {α ι H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

structure FormalStarTable (F : Option ι → TrackStar α →* H) where
  carrier : Subgroup H
  carrier_eq : carrier=(copyFamilyEval F).range
  input : Option ι → TrackStar α →* carrier
  inclusion : ∀ i, carrier.subtype.comp (input i)=F i
  model : ((ι → Bool) → alternatingGroup α) →* carrier ⧸ Subgroup.center carrier
  onto : Function.Surjective model
  spec : ∀ i, model.comp ((maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i).comp
      (universalProjection (alternatingGroup α))) =
    (QuotientGroup.mk' _).comp (input i)

namespace FormalStarTable
variable {F : Option ι → TrackStar α →* H} (T : FormalStarTable F)
noncomputable def sector (U : Set (ι → Bool)) : TrackStar α →* H :=
  T.carrier.subtype.comp (centralSector T.model U)

end FormalStarTable
end FormalStarTables

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClosedChartOverlap
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

section FullTangentOverlap

noncomputable def clippingOverlapLower (r : CutRing) (t : CutRing × CutRing) (j : Fin 2) : CutRing :=
  orderedCutMax (-r) (pointCoordinate t j-r)
noncomputable def clippingOverlapUpper (r : CutRing) (t : CutRing × CutRing) (j : Fin 2) : CutRing :=
  orderedCutMin r (pointCoordinate t j+r)

end FullTangentOverlap

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FinitePrimitiveResolution
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
section FinitePrimitiveResolution
variable {X ι : Type*}

noncomputable def translatedPrimitiveAlgebra (a : ℕ) (r : CutRing) :
    BooleanSubalgebra (Set (GenericSquare a)) :=
  BooleanSubalgebra.closure (Set.range fun p : Fin 5 × (CutRing × CutRing) =>
    (spatialTranslate p.2 (initialTest a r p.1)).val)

theorem translatedPrimitiveAlgebra_test (a : ℕ) (r : CutRing)
    (p : Fin 5 × (CutRing × CutRing)) :
    (spatialTranslate p.2 (initialTest a r p.1)).val ∈ translatedPrimitiveAlgebra a r :=
  BooleanSubalgebra.subset_closure ⟨p,rfl⟩

theorem translatedPrimitiveAlgebra_translate (a : ℕ) (r : CutRing)
    (u : CutRing × CutRing) {V : Set (GenericSquare a)}
    (hV : V ∈ translatedPrimitiveAlgebra a r) :
    translate a u ⁻¹' V ∈ translatedPrimitiveAlgebra a r := by
  induction hV using BooleanSubalgebra.closure_bot_sup_induction with
  | mem V h =>
    obtain ⟨p,rfl⟩ := h
    have he : translate a u ⁻¹' (spatialTranslate p.2 (initialTest a r p.1)).val =
        (spatialTranslate (p.2-u) (initialTest a r p.1)).val := by
      ext x
      simp only [spatialTranslate,Set.mem_preimage,← translate_add]
      abel_nf
    rw [he]
    exact translatedPrimitiveAlgebra_test a r (p.1,p.2-u)
  | bot => exact BooleanSubalgebra.bot_mem
  | sup V W _ _ ihV ihW => exact BooleanSubalgebra.sup_mem ihV ihW
  | compl V _ ih => exact BooleanSubalgebra.compl_mem ih

theorem translatedPrimitiveAlgebra_initial (a : ℕ) (r : CutRing) (j : Fin 5) :
    (initialTest a r j).val ∈ translatedPrimitiveAlgebra a r := by
  have h := translatedPrimitiveAlgebra_test a r (j,0)
  have he : (spatialTranslate (0:CutRing × CutRing) (initialTest a r j)).val =
      (initialTest a r j).val := by
    ext p
    simp [spatialTranslate,translate_zero]
  rwa [he] at h

theorem polygon_finite_primitive_resolution {a : ℕ} (r : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (V : polygonAlgebra a) :
    ∃ S : Finset (Fin 5 × (CutRing × CutRing)),
      ResolvedBy (fun p : S => (spatialTranslate p.val.2 (initialTest a r p.val.1)).val) V.val := by
  apply finite_resolving_subfamily (fun p : Fin 5 × (CutRing × CutRing) =>
    (spatialTranslate p.2 (initialTest a r p.1)).val)
  let B := translatedPrimitiveAlgebra a r
  have ht := fun u U hU => translatedPrimitiveAlgebra_translate a r u (V := U) hU
  have hcoord (j : Fin 2) (z : CutRing) :
      halfPlane a (Fin.castLE (by omega) j) z ∈ B := by
    apply coordinate_cuts_generated B j ht
    fin_cases j
    · exact translatedPrimitiveAlgebra_initial a r 1
    · exact translatedPrimitiveAlgebra_initial a r 2
  apply polygon_induction (P := fun U => U ∈ B) ?_ BooleanSubalgebra.bot_mem
    (fun _ _ hU hV => BooleanSubalgebra.sup_mem hU hV)
    (fun _ hU => BooleanSubalgebra.compl_mem hU) V.property
  intro j z
  fin_cases j
  · exact hcoord 0 z
  · exact hcoord 1 z
  · exact slope_cuts_generated r hr B ht hcoord 2 (Or.inl rfl)
      (translatedPrimitiveAlgebra_initial a r 3) z
  · exact slope_cuts_generated r hr B ht hcoord 3 (Or.inr rfl)
      (translatedPrimitiveAlgebra_initial a r 4) z

end FinitePrimitiveResolution

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveCentralLaws
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

theorem polygon_family_primitive_resolution {a : ℕ} {ι : Type} [Finite ι]
    (r : CutRing) (hr : 0<ordinary r ∧ ordinary r<1/2) (V : ι → polygonAlgebra a) :
    ∃ S : Finset (Fin 5 × (CutRing × CutRing)), ∀ i,
      ResolvedBy (fun p : S => (spatialTranslate p.val.2 (initialTest a r p.val.1)).val) (V i).val := by
  classical
  let _ := Fintype.ofFinite ι
  choose S hS using fun i => polygon_finite_primitive_resolution r hr (V i)
  refine ⟨Finset.univ.biUnion S,fun i x y he => hS i x y ?_⟩
  intro p
  exact he ⟨p.val,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,p.property⟩⟩

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

def AllPrimitiveLaws : Prop :=
  ∀ (ι : Type) [Finite ι] (P : ι → Fin 5 × (CutRing × CutRing))
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I), B.PrimitiveFamilyLaw I b hb P

variable (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws)

theorem fullGeometricSector_independent {ι κ : Type} [Finite ι] [Finite κ]
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val) :
    B.fullGeometricSector hlarge P (fun I _ b hb => h ι P I b hb) V =
      B.fullGeometricSector hlarge Q (fun I _ b hb => h κ Q I b hb) V := by
  let R : ι ⊕ κ → Fin 5 × (CutRing × CutRing) := Sum.elim P Q
  rw [B.fullGeometricSector_subfamily hlarge R P Sum.inl rfl
      (fun I _ b hb => h _ R I b hb) _ V hV,
    B.fullGeometricSector_subfamily hlarge R Q Sum.inr rfl
      (fun I _ b hb => h _ R I b hb) _ V hV']

noncomputable def polygonStar (hr : 0<ordinary r ∧ ordinary r<1/2)
    (V : polygonAlgebra a) : TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  let S := (polygon_finite_primitive_resolution r hr V).choose
  B.fullGeometricSector hlarge (fun p : S => p.val) (fun I _ b hb => h S (fun p => p.val) I b hb) V

theorem polygonStar_eq (hr : 0<ordinary r ∧ ordinary r<1/2)
    {ι : Type} [Finite ι] (P : ι → Fin 5 × (CutRing × CutRing)) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    B.polygonStar hlarge h hr V = B.fullGeometricSector hlarge P (fun I _ b hb => h ι P I b hb) V := by
  apply B.fullGeometricSector_independent hlarge h _ P V _ hV
  exact (polygon_finite_primitive_resolution r hr V).choose_spec

theorem polygonStar_projection (hr : 0<ordinary r ∧ ordinary r<1/2) (V : polygonAlgebra a) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.polygonStar hlarge h hr V) =
      (conditionalAlternatingHom V).comp (universalProjection (alternatingGroup (Fin (m+1)))) := by
  unfold polygonStar
  exact B.fullGeometricSector_projection hlarge _ _ V
    (polygon_finite_primitive_resolution r hr V).choose_spec

theorem polygonStar_whole (hr : 0<ordinary r ∧ ordinary r<1/2) :
    B.polygonStar hlarge h hr (wholePolygon a) =
      B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))) := by
  unfold polygonStar
  exact B.fullGeometricSector_whole hlarge _ _

theorem polygonStars_finite_central (hr : 0<ordinary r ∧ ordinary r<1/2)
    {ι : Type} [Finite ι] (V : ι → polygonAlgebra a) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (⨆ i, (B.polygonStar hlarge h hr (V i)).range) := by
  obtain ⟨S,hS⟩ := polygon_family_primitive_resolution r hr V
  apply (B.fullPrimitiveFamily_central hlarge (fun p : S => p.val)
    (fun I _ b hb => h S (fun p => p.val) I b hb)).mono
  apply iSup_le
  intro i
  rw [B.polygonStar_eq hlarge h hr (fun p : S => p.val) (V i) (hS i)]
  rintro x ⟨s,rfl⟩
  exact B.fullGeometricSector_mem hlarge _ _ (V i) s

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_OffsetFrames
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

structure OffsetFrame (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (u : Fin (m+1) → CutRing × CutRing) where
  k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))
  d : Fin (m+1) → CutRing × CutRing
  projection : sourceLatticeFullMap a r m hm k = trackTranslation d
  prescribed : ∀ i ∈ I, d i = u i

noncomputable def balancedOffsetFrame (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I)
    (u : Fin (m+1) → CutRing × CutRing) : OffsetFrame a r m hm I u := by
  let h := sourceLatticeFullMap_prescribed a r m hm I b hb u
  exact ⟨h.choose,h.choose_spec.choose,h.choose_spec.choose_spec.1,h.choose_spec.choose_spec.2⟩

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

noncomputable def frameStar (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup I) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (MulAut.conj (B.t F.k)).toMonoidHom.comp
    ((B.polygonStar hlarge h hr V).comp (universalMap (subtypeAlternatingHom I)))

theorem frameStar_projection (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I)) :
    coverMap M (alternatingGenerator a r m hm) (B.frameStar hlarge h hr I u F V s) =
      sourceLatticeMap a r m hm F.k *
        conditionalAlternatingHom V (subtypeAlternatingHom I (universalProjection _ s)) *
        (sourceLatticeMap a r m hm F.k)⁻¹ := by
  change coverMap M (alternatingGenerator a r m hm)
    (B.t F.k * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) * (B.t F.k)⁻¹) = _
  rw [map_mul,map_mul,map_inv,
    show coverMap M (alternatingGenerator a r m hm) (B.t F.k) = sourceLatticeMap a r m hm F.k from DFunLike.congr_fun B.t_projection F.k]
  have he := DFunLike.congr_fun (B.polygonStar_projection hlarge h hr V)
    (universalMap (subtypeAlternatingHom I) s)
  rw [show coverMap M (alternatingGenerator a r m hm)
    (B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s)) =
      conditionalAlternatingHom V (universalProjection _ (universalMap (subtypeAlternatingHom I) s)) from he]
  rw [show universalProjection _ (universalMap (subtypeAlternatingHom I) s) =
    subtypeAlternatingHom I (universalProjection _ s) from DFunLike.congr_fun (universalMap_spec _) s]

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FrameActions
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
section FrameActions

variable {P H Q : Type*} [Group P] [Group H] [Group Q]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem frameStar_apply (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I))
    (i : I) (x : V.val) :
    (coverMap M (alternatingGenerator a r m hm) (B.frameStar hlarge h hr I u F V s)).val.val
      (i.val,translate a (u i.val) x.val) =
      (((universalProjection _ s).val i).val,
        translate a (u ((universalProjection _ s).val i).val) x.val) := by
  classical
  have hp := congrArg Subtype.val (B.frameStar_projection hlarge h hr I u F V s)
  change (coverMap M (alternatingGenerator a r m hm) (B.frameStar hlarge h hr I u F V s)).val =
    sourceLatticeFullMap a r m hm F.k * conditionalHom V (subtypeAlternatingHom I (universalProjection _ s)).val *
      (sourceLatticeFullMap a r m hm F.k)⁻¹ at hp
  rw [F.projection] at hp
  rw [hp]
  have hin : (trackTranslation (a := a) F.d).val (i.val,x.val) =
      (i.val,translate a (u i.val) x.val) := by
    change (i.val,translate a (F.d i.val) x.val) = _
    rw [F.prescribed i.val i.property]
  change (trackTranslation F.d).val
    (conditionalPerm V (subtypeAlternatingHom I (universalProjection _ s)).val
      ((trackTranslation F.d).val.symm (i.val,translate a (u i.val) x.val))) = _
  rw [← hin,Equiv.symm_apply_apply]
  have hcond : conditionalPerm V (subtypeAlternatingHom I (universalProjection _ s)).val
      (i.val,x.val) = (((universalProjection _ s).val i).val,x.val) := by
    change (if x.val ∈ V.val then Equiv.Perm.ofSubtype (universalProjection _ s).val i.val else i.val,x.val) = _
    rw [ite_eq_left x.property,Equiv.Perm.ofSubtype_apply_of_mem _ i.property]
  rw [hcond]
  change (_,translate a (F.d ((universalProjection _ s).val i).val) x.val)=_
  rw [F.prescribed _ ((universalProjection _ s).val i).property]

end InitialCoverSystem
end FrameActions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FrameDisjointness
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section FrameDisjointness

namespace OffsetFrame
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {I J : Finset (Fin (m+1))} {u : Fin (m+1) → CutRing × CutRing}

def restrict (F : OffsetFrame a r m hm J u) (hIJ : I ⊆ J) : OffsetFrame a r m hm I u where
  k := F.k
  d := F.d
  projection := F.projection
  prescribed := fun i hi => F.prescribed i (hIJ hi)

end OffsetFrame

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem polygonStar_alphabet_aligned (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card)
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I)) :
    B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) ∈
      sourceAlignedGroup a r m hm M B.t I := by
  obtain ⟨S,hS⟩ := polygon_finite_primitive_resolution r hr V
  let P : S → Fin 5 × (CutRing × CutRing) := fun p => p.val
  have hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val := hS
  rw [B.polygonStar_eq hlarge h hr P V hV]
  have he := DFunLike.congr_fun (B.fullGeometricSector_inclusion hlarge P (fun J _ d hd => h S P J d hd) I hI b hb
    (h S P I b hb) V hV) s
  change B.fullGeometricSector hlarge P (fun J _ d hd => h S P J d hd) V (universalMap (subtypeAlternatingHom I) s) = _ at he
  rw [he]
  exact B.geometricSector_aligned I b hb P _ V s

end InitialCoverSystem
end FrameDisjointness

theorem conditional_alphabet_supported {a m : ℕ} (I : Finset (Fin m))
    (V : polygonAlgebra a) (s : alternatingGroup I) :
    SupportedIn (conditionalHom V (subtypeAlternatingHom I s).val).val
      {p : TrackPoint a m | p.1 ∈ I ∧ p.2 ∈ V.val} := by
  classical
  rintro ⟨i,x⟩ hp
  change (if x∈V.val then (subtypeAlternatingHom I s).val i else i,x) = (i,x)
  by_cases hx : x ∈ V.val
  · have hi : i ∉ I := fun hi => hp ⟨hi,hx⟩
    have he : (subtypeAlternatingHom I s).val i = i := by
      change Equiv.Perm.ofSubtype s.val i = i
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hi
    rw [ite_eq_left hx,he]
  · rw [ite_eq_right hx]

def frameDomain {a m : ℕ} (I : Finset (Fin m)) (u : Fin m → CutRing × CutRing)
    (V : polygonAlgebra a) : Set (TrackPoint a m) :=
  {p | ∃ i ∈ I, ∃ x ∈ V.val, p = (i,translate a (u i) x)}

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem frameStar_supported (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)] (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm I u) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup I)) :
    SupportedIn (coverMap M (alternatingGenerator a r m hm)
      (B.frameStar hlarge h hr I u F V s)).val.val (frameDomain I u V) := by
  have hp := congrArg Subtype.val (B.frameStar_projection hlarge h hr I u F V s)
  change (coverMap M (alternatingGenerator a r m hm) (B.frameStar hlarge h hr I u F V s)).val =
    sourceLatticeFullMap a r m hm F.k * conditionalHom V (subtypeAlternatingHom I (universalProjection _ s)).val *
      (sourceLatticeFullMap a r m hm F.k)⁻¹ at hp
  rw [F.projection] at hp
  rw [hp]
  apply (supported_conjugate (trackTranslation F.d).val
    (conditional_alphabet_supported I V (universalProjection _ s))).mono
  rintro p ⟨⟨i,x⟩,⟨hi,hx⟩,rfl⟩
  refine ⟨i,hi,x,hx,?_⟩
  change (i,translate a (F.d i) x)=(i,translate a (u i) x)
  rw [F.prescribed i hi]

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_DistinctSlotStars
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
section DistinctSlotStars

noncomputable def orderedTrackHom {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    alternatingGroup (Fin 5) →* alternatingGroup (orderedTrackAlphabet ι) :=
  (MonoidHom.ofInjective (subtypeAlternatingHom_injective (orderedTrackAlphabet ι))).symm.toMonoidHom.comp
    ((fiveAlternatingHom ι).codRestrict (subtypeAlternatingHom (orderedTrackAlphabet ι)).range
      (fun s => (subtypeAlternatingHom_mem_range _ _).mpr (alphabet_support_subset ι s)))

@[simp] theorem orderedTrackHom_comp {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    (subtypeAlternatingHom (orderedTrackAlphabet ι)).comp (orderedTrackHom ι) =
      fiveAlternatingHom ι := by
  ext s : 1
  exact MonoidHom.apply_ofInjective_symm (subtypeAlternatingHom_injective _) _

@[simp] theorem orderedTrackAlphabet_mem {m : ℕ} (ι : Fin 5 ↪ Fin m) (j : Fin 5) :
    ι j ∈ orderedTrackAlphabet ι := Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩

theorem orderedTrackHom_apply {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (s : alternatingGroup (Fin 5)) (j : Fin 5) :
    ((orderedTrackHom ι s).val ⟨ι j,orderedTrackAlphabet_mem ι j⟩).val = ι (s.val j) := by
  have he := congrArg (fun t : alternatingGroup (Fin m) => t.val (ι j))
    (DFunLike.congr_fun (orderedTrackHom_comp ι) s)
  change Equiv.Perm.ofSubtype (orderedTrackHom ι s).val (ι j) =
    Equiv.Perm.viaEmbedding s.val ι (ι j) at he
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ (orderedTrackAlphabet_mem ι j),
    Equiv.Perm.viaEmbedding_apply] at he
  exact he

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

noncomputable def distinctSlotStar (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup (Fin 5)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.frameStar hlarge h hr (orderedTrackAlphabet ι) u F V).comp (universalMap (orderedTrackHom ι))

theorem distinctSlotStar_apply (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup (Fin 5))) (j : Fin 5) (x : V.val) :
    (coverMap M (alternatingGenerator a r m hm) (B.distinctSlotStar hlarge h hr ι u F V s)).val.val
      (ι j,translate a (u (ι j)) x.val) =
      (ι ((universalProjection _ s).val j),translate a (u (ι ((universalProjection _ s).val j))) x.val) := by
  have he := B.frameStar_apply hlarge h hr (orderedTrackAlphabet ι) u F V
    (universalMap (orderedTrackHom ι) s) ⟨ι j,orderedTrackAlphabet_mem ι j⟩ x
  rw [show universalProjection _ (universalMap (orderedTrackHom ι) s) =
    orderedTrackHom ι (universalProjection _ s) from
    DFunLike.congr_fun (universalMap_spec (orderedTrackHom ι)) s,orderedTrackHom_apply] at he
  exact he

end InitialCoverSystem
end DistinctSlotStars

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CommonFrameTransport
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

noncomputable def geometricFrameGroup
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  (⨆ V : polygonAlgebra a, (B.polygonStar hlarge h hr V).range).map (MulAut.conj (B.t k)).toMonoidHom

theorem frameStar_mem_geometricFrameGroup (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)] (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm I u) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup I)) :
    B.frameStar hlarge h hr I u F V s ∈ B.geometricFrameGroup hlarge h hr F.k := by
  refine ⟨_,?_,rfl⟩
  exact (le_iSup (fun W : polygonAlgebra a => (B.polygonStar hlarge h hr W).range) V)
    ⟨universalMap (subtypeAlternatingHom I) s,rfl⟩

theorem distinctSlotStar_mem_geometricFrameGroup (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    B.distinctSlotStar hlarge h hr ι u F V s ∈ B.geometricFrameGroup hlarge h hr F.k :=
  B.frameStar_mem_geometricFrameGroup hlarge h hr _ u F V (universalMap (orderedTrackHom ι) s)

theorem frameStar_alphabet_mem (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card)
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I)) :
    B.frameStar hlarge h hr I u F V s ∈ sourceAlignedGroup a r m hm M B.t I :=
  alignedGroup_conjugate B.t _ _ F.k (B.polygonStar_alphabet_aligned hlarge h hr I hI b hb V s)

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PrivateBankWord
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
section PrivateBankWord

theorem bankRow_subset {m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m) (j : Fin 5) :
    orderedTrackAlphabet (bankRow e j) ⊆ bankAlphabet e := by
  intro i hi
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_map.mpr ⟨(j,k),Finset.mem_univ _,rfl⟩

noncomputable def privateCycleStar : UniversalExtension (alternatingGroup (Fin 5)) :=
  (universalProjection_surjective _ privateCycle).choose

@[simp] theorem privateCycleStar_projection : universalProjection _ privateCycleStar=privateCycle :=
  (universalProjection_surjective _ privateCycle).choose_spec

end PrivateBankWord

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_RepeatedTrackRouting
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace PrivateRoutingBank
variable {m : ℕ} {i : Fin 5 → Fin m} (P : PrivateRoutingBank i)

theorem row_subset (j : Fin 5) : orderedTrackAlphabet (P.row j) ⊆ P.alphabet := by
  classical
  intro t ht
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp ht
  exact Finset.mem_image.mpr ⟨(j,k),Finset.mem_univ _,rfl⟩

theorem source_mem (j : Fin 5) : i j ∈ P.alphabet := by
  rw [← P.source j]
  exact P.row_subset j (orderedTrackAlphabet_mem _ _)

theorem target_other_notmem (j l : Fin 5) (hjl : j≠l) :
    P.target l ∉ orderedTrackAlphabet (P.row j) := by
  intro ht
  obtain ⟨k,_,he⟩ := Finset.mem_map.mp ht
  by_cases hk : k=0
  · subst k
    rw [P.source j] at he
    exact P.fresh l 1 (by decide) j he.symm
  · exact hjl (P.separate j k l 1 hk (by decide) he).1

theorem source_other_frame_notmem {a : ℕ} (V : polygonAlgebra a)
    (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a m V (fun j => (i j,u j))))
    (j l : Fin 5) (hjl : j≠l) (x : V.val) :
    (i l,translate a (u l) x.val) ∉
      frameDomain (orderedTrackAlphabet (P.row j)) (fun _ => u j) V := by
  rintro ⟨t,ht,y,hy,he⟩
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp ht
  have ht := congrArg Prod.fst he
  by_cases hk : k=0
  · subst k
    rw [P.source j] at he
    have hh : SlotMap a m V (fun j => (i j,u j)) (j,⟨y,hy⟩) =
        SlotMap a m V (fun j => (i j,u j)) (l,x) := he.symm
    exact hjl (congrArg Prod.fst (hinj hh))
  · exact P.fresh j k hk l ht.symm

end PrivateRoutingBank

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

noncomputable def privateRoutingFactor (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet) (V : polygonAlgebra a) (j : Fin 5) :
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.distinctSlotStar hlarge h hr (P.row j) (fun _ => u j)
    (balancedOffsetFrame a r m hm (orderedTrackAlphabet (P.row j)) b
      (fun ht => hb (P.row_subset j ht)) (fun _ => u j)) V privateCycleStar

noncomputable def privateRoutingWord (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet) (V : polygonAlgebra a) :
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  ((List.finRange 5).map (B.privateRoutingFactor hlarge h hr i u P b hb V)).prod

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSeparatingLevels
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section FlagSeparatingLevels
open Classical

def FlagSeparates {a : ℕ} {v : ℝ×ℝ} (j : Fin 4) (c : CutRing)
    (z w : SquareFlag a v) : Prop :=
  ¬ (flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ z ↔
     flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ w)

end FlagSeparatingLevels

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_RecoveredConstantCovariance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace OffsetFrame
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}

def zero (I : Finset (Fin (m+1))) : OffsetFrame a r m hm I (fun _ => 0) where
  k := 1
  d := 0
  projection := by rw [map_one,trackTranslation_zero]
  prescribed := by intros; rfl

end OffsetFrame

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem constant_mem_polygonStars (s : alternatingGroup (Fin (m+1))) :
    B.c s ∈ ⨆ V : polygonAlgebra a, (B.polygonStar hlarge h hr V).range := by
  obtain ⟨x,hx⟩ := universalProjection_surjective (E := alternatingGroup (Fin (m+1))) s
  apply (le_iSup (fun V : polygonAlgebra a => (B.polygonStar hlarge h hr V).range) (wholePolygon a))
  refine ⟨x,?_⟩
  rw [B.polygonStar_whole hlarge h hr]
  exact congrArg B.c hx

theorem distinctSlotStar_offset_formula (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a) :
    B.distinctSlotStar hlarge h hr ι u F V =
      (MulAut.conj (B.t F.k)).toMonoidHom.comp
        (B.distinctSlotStar hlarge h hr ι (fun _ => 0) (OffsetFrame.zero _) V) := by
  ext s : 1
  simp [distinctSlotStar,frameStar,OffsetFrame.zero]

def constantReindexedFrame
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (ι κ : Fin 5 ↪ Fin (m+1)) (c : alternatingGroup (Fin (m+1)))
    (hc : ∀ j, c.val (ι j) = κ j)
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) :
    OffsetFrame a r m hm (orderedTrackAlphabet κ) (fun i => u (c.val.symm i)) where
  k := R c F.k
  d := fun i => F.d (c.val.symm i)
  projection := by
    have he := congrArg (coverMap M (alternatingGenerator a r m hm)) (hR c F.k)
    simp only [map_mul,map_inv] at he
    rw [show coverMap M (alternatingGenerator a r m hm) (B.c c) =
      conditionalAlternatingHom (wholePolygon a) c from DFunLike.congr_fun B.c_projection c,
      show coverMap M (alternatingGenerator a r m hm) (B.t F.k) =
      sourceLatticeMap a r m hm F.k from DFunLike.congr_fun B.t_projection F.k,
      show coverMap M (alternatingGenerator a r m hm) (B.t (R c F.k)) =
      sourceLatticeMap a r m hm (R c F.k) from DFunLike.congr_fun B.t_projection (R c F.k)] at he
    have hf := congrArg Subtype.val he
    change conditionalHom (wholePolygon a) c.val * sourceLatticeFullMap a r m hm F.k *
      (conditionalHom (wholePolygon a) c.val)⁻¹ = sourceLatticeFullMap a r m hm (R c F.k) at hf
    rw [F.projection,constant_conjugate_translation] at hf
    exact hf.symm
  prescribed := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
    have he : c.val.symm (κ j) = ι j := by rw [← hc j]; exact c.val.symm_apply_apply _
    rw [he]
    exact F.prescribed (ι j) (orderedTrackAlphabet_mem ι j)

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_SmallEvenRouting
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
section SmallEvenRouting

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem constant_mem_sourceAligned (c : alternatingGroup (Fin (m+1)))
    (J : Finset (Fin (m+1))) (hc : c.val.support ⊆ J) :
    B.c c ∈ sourceAlignedGroup a r m hm M B.t J := by
  obtain ⟨s,rfl⟩ := (subtypeAlternatingHom_mem_range J c).mpr hc
  have hh := B.initialAlphabet_aligned J 0 s
  rwa [B.initialAlphabet_zero] at hh

end InitialCoverSystem
end SmallEvenRouting

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_RoutingIndependence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

structure SlotRouting (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) where
  alphabet : Finset (Fin (m+1))
  card_le : alphabet.card ≤ 25
  source_mem : ∀ j, i j ∈ alphabet
  target : Fin 5 ↪ Fin (m+1)
  target_mem : ∀ j, target j ∈ alphabet
  offsets : Fin (m+1) → CutRing × CutRing
  offsets_spec : ∀ j, offsets (target j)=u j
  frame : OffsetFrame a r m hm (orderedTrackAlphabet target) offsets
  word : BoundedRelationCover M (alternatingGenerator a r m hm)
  aligned : word ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range
  supported : word ∈ sourceAlignedGroup a r m hm M B.t alphabet
  transport : ∀ (j : Fin 5) (x : V.val),
    (coverMap M (alternatingGenerator a r m hm) word).val.val (i j,translate a (u j) x.val) =
      (target j,translate a (u j) x.val)

namespace SlotRouting
variable {B hlarge h hr}

noncomputable def star {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr V i u) :
    UniversalExtension (alternatingGroup (Fin 5)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (MulAut.conj ρ.word⁻¹).toMonoidHom.comp
    (B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V)

end SlotRouting
end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TentMatrixPositivity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

section FlagSeparatorMatrices
open Classical MeasureTheory

noncomputable def flagChamber {a : ℕ} {v : ℝ×ℝ} (t : Fin 4 → ℝ)
    (z : SquareFlag a v) : (Fin 4 × CutRing) → Bool := fun l =>
  if |conjugate l.2|≤t l.1 then
    decide (flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ z) else false

noncomputable def separatorMatrix {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) (z w : SquareFlag a v) : ℝ :=
  ∫t,if flagChamber t z=flagChamber t w then 1 else 0 ∂μ

end FlagSeparatorMatrices

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FlagAveragingMatrices
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
section FlagAveragingMatrices
open Classical MeasureTheory

noncomputable def flagSiteOrdinary {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) : ℝ×ℝ :=
  z.val.2.val

noncomputable def scaledSiteConjugate {a m D : ℕ} {v : ℝ×ℝ}
    (N : ℝ) (z : FlagSite a m D v) : ℝ×ℝ :=
  ((flagSiteConjugate z).1/N,(flagSiteConjugate z).2/N)

noncomputable def flagAveragingMatrix {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) : Matrix (FlagSite a m D v) (FlagSite a m D v) ℝ := fun z w =>
  if z.val.1=w.val.1 then
    (χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w)/(ρ*(r*η)^2)) *
    planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w) *
    planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w) *
    separatorMatrix (thresholdLaw (r/N) κ) z.val.2 w.val.2
  else 0

end FlagAveragingMatrices

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
section SourceCovarianceLimit
open Classical Filter
open scoped Topology

noncomputable def sourceFlagMatrix {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ η κ : ℝ) (n : ℕ)
    (z y : FlagSite a m D v) : ℝ :=
  sourceDyadicWeight n*∑i∈sourceDyadicIndices n,
    flagAveragingMatrix χ ρ (sourceDyadicN n) ((2:ℝ)^i) η κ z y

end SourceCovarianceLimit

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

noncomputable def flagMeanSignal {a m D : ℕ} {v : ℝ×ℝ}
    (θ : (ℝ×ℝ) → ℝ) (N : ℝ) (z : FlagSite a m D v) : ℝ :=
  θ (scaledSiteConjugate N z)

end FlagSignalEnergy

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

noncomputable def sourceSmoothFieldLaw {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    Measure (FlagSite a m D v → ℝ) :=
  (independentSmoothNoiseLaw (FlagSite a m D v)).map
    (finiteCoefficientField (flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL))
      (flagMeanSignal θ (sourceDyadicN n)) (Matrix.of (sourceFlagMatrix χ ρ η κ n)))

end SourceFieldLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_ThresholdField
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

section SourceBitField
open Classical MeasureTheory Filter Set
open scoped Topology

noncomputable def sourceBitFieldLaw {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    Measure (FlagSite a m D v → Bool) :=
  (sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n).map thresholdField

end SourceBitField

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FieldSignalData
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
section FieldSignalData
open Classical Set
open scoped ContDiff

namespace FieldSignalData

noncomputable def realLaw (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.Measure (FlagSite a m D v → ℝ) :=
  sourceSmoothFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n

noncomputable def bitLaw (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.Measure (FlagSite a m D v → Bool) :=
  sourceBitFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n

end FieldSignalData
end FieldSignalData

end SimpleAmenable
end
end

end OAI
end



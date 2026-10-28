-- Prove2me | Definitions.Def_OAIQ65Sa010
-- name    : OAIQ65Sa010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T03:25:12.570194+00:00
-- url     : https://prove2.me/theorems/8e09f9b8-1085-44ef-be47-bf80886c3950
-- title:
--   Definitions bundle OAIQ65Sa010 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 142 declarations of OpenAI's Lean: 70 definitions, 4 inductive types or structures, 11 instances and 57 theorems. The definitions and types are `OAI.RestrictedNerve.diagramEquivalence`, `OAI.RestrictedNerve.homologyIso`, `OAI.RestrictedNerve.innerNerveRows`, `OAI.RestrictedNerve.innerNerveRowsMiddle`, `OAI.RestrictedNerve.innerNerveRowsOuter`, `OAI.RestrictedNerve.middleNerveRows`, `OAI.RestrictedNerve.middleNerveRowsOuter`, `OAI.RestrictedNerve.nestedPosReindex`, `OAI.RestrictedNerve.outerNerveRows`, `OAI.RestrictedNerve.pos₃`, `OAI.RestrictedNerve.property₂`, `OAI.RestrictedNerve.property₃`, `OAI.RestrictedNerve.stringEvaluation`, `OAI.RestrictedNerve.totalNerveBarIso`, `OAI.RestrictedNerve.transposeReindexLeft`, `OAI.RestrictedNerve.transposeReindexRight`, `OAI.RestrictedNerve.triplePosHomologyIso`, `OAI.RestrictedNerve.triplePosInclusion`, `OAI.RestrictedNerve.tripleRestrictedHomologyIso`, `OAI.RestrictedNerve.tripleTranspose`, `OAI.RestrictedNerve.untransposeDiagram`, `OAI.RestrictedNerve.untransposeDiagramHom`, `OAI.RestrictedNerve.untransposeDiagramObj`, `OAI.SimpleAmenable.BarrierSignalSystem.sampledPartition`, `OAI.SimpleAmenable.ClippedGerm`, `OAI.SimpleAmenable.ClippedGerm.BoxValid`, `OAI.SimpleAmenable.ClippedGerm.axialCut`, `OAI.SimpleAmenable.ClippedGerm.offset`, `OAI.SimpleAmenable.CommonFrame.mul`, `OAI.SimpleAmenable.ConcurrentGeometry`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.offset`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.vertex`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChartAnchor`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChartBound`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChartBoundaryAnchor`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChartBoundaryBound`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChartNeighborhood`, `OAI.SimpleAmenable.ConcurrentGeometry.coordinateGate` and 34 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Amenability_BarrierAlgorithm`, `SimpleAmenable_Amenability_BarrierCells`, `SimpleAmenable_Amenability_FinitePartitionArrows`, `SimpleAmenable_Amenability_PartitionArrows`, `SimpleAmenable_Amenability_UniformShapeMatchings`, `SimpleAmenable_CentralCovers_FiniteSlotRefinement`, `SimpleAmenable_CentralCovers_FrameCentrality`, `SimpleAmenable_CentralCovers_GlobalAlignedCentrality`, `SimpleAmenable_CentralCovers_LocalArrangementAssignments`, `SimpleAmenable_Configurations_SymmetricCharts`, `SimpleAmenable_Homology_UniformConcurrentMesh`, `SimpleAmenable_PolygonGeometry_ClippedGerms`, `SimpleAmenable_PolygonGeometry_ConcurrentGeometry`, `SimpleAmenable_PolygonGeometry_ConcurrentInwardModel`, `SimpleAmenable_PolygonGeometry_CoordinateModels`, `SimpleAmenable_PolygonGeometry_FinePatchAtlas`, `SimpleAmenable_PolygonGeometry_InactiveNeighborhoodActions`, `SimpleAmenable_PolygonGeometry_IntersectionControl`, `SimpleAmenable_PolygonGeometry_InwardPlanarGerms`, `SimpleAmenable_PolygonGeometry_LocalClippedBoxFormula`, `SimpleAmenable_PolygonGeometry_TranslationRoutingHelpers`, `SimpleAmenable_PolygonGeometry_VertexMargins`, `SimpleAmenable_RandomFields_PrimitiveCovariance`, `SimpleAmenable_Simplicial_MonoidalCongruence`, `SimpleAmenable_Simplicial_NestedPosReindex`, `SimpleAmenable_Simplicial_PositionalInclusionMonoidal`, `SimpleAmenable_Simplicial_RestrictedFunctorial`, `SimpleAmenable_Simplicial_RestrictedMonoidal`, `SimpleAmenable_Simplicial_RestrictedMonoidalTranspose`, `SimpleAmenable_Simplicial_RestrictedNerve`, `SimpleAmenable_Simplicial_RestrictedTripleDegree`, `SimpleAmenable_Simplicial_RestrictedTripleMaps`, `SimpleAmenable_Simplicial_StringEvaluation`, `SimpleAmenable_Simplicial_Supplemental`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa004`, `OAIQ65Sa005` and `OAIQ65Sa006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa013` and `OAIQ65Sa014`; the statements `OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport`, `OAI.SimpleAmenable.ClippedGerm.model_restrict_gate`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons_assignment_realized`, `OAI.SimpleAmenable.CoordinateGerm.model_formula`, `OAI.SimpleAmenable.InitialCoverSystem.all_rectangle_control_to_sign`, `OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations`, `OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law`, `OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform`, `OAI.SimpleAmenable.InitialCoverSystem.tangentSign_step_action_closed`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_interval_action` and `OAI.SimpleAmenable.InitialCoverSystem.tangent_transport_uniform_cover_uniform`; the proofs of `OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport`, `OAI.SimpleAmenable.ClippedGerm.model_restrict_gate`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons_assignment_realized`, `OAI.SimpleAmenable.CoordinateGerm.model_formula`, `OAI.SimpleAmenable.InitialCoverSystem.all_rectangle_control_to_sign`, `OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law`, `OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform`, `OAI.SimpleAmenable.InitialCoverSystem.tangentSign_step_action_closed`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_interval_action`, `OAI.SimpleAmenable.InitialCoverSystem.tangent_transport_uniform_cover_uniform` and `OAI.SimpleAmenable.polygon_infinite_simple_folner`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa004
import Definitions.Def_OAIQ65Sa005
import Definitions.Def_OAIQ65Sa006

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

namespace CommonFrame

variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {I : Finset (Fin (m+1))} {u v : CutRing × CutRing}

noncomputable def mul (F : CommonFrame a r m hm I u) (G : CommonFrame a r m hm I v) :
    CommonFrame a r m hm I (u+v) where
  k := F.k * G.k
  d := F.d + G.d
  projection := by rw [map_mul,F.projection,G.projection,trackTranslation_add]
  common i hi := by simp only [Pi.add_apply,F.common i hi,G.common i hi]

end CommonFrame

end PrimitiveCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_IntersectionControl
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

section ActualRectangleBridge

noncomputable def coordinateRectangle (a : ℕ) (u v : Fin 2 → CutRing) : polygonAlgebra a :=
  coordinateInterval a 0 (u 0) (v 0) ⊓ coordinateInterval a 1 (u 1) (v 1)

end ActualRectangleBridge

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

def symmetricWindowLength (s : CutRing) : ℕ := 2*(endpointLabel s).natAbs+2

end SymmetricCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_UniformConcurrentMesh
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
section UniformConcurrentMesh

noncomputable def lineIntersectionCoefficient (a : ℕ) (i j : Fin 4) : ℝ :=
  ((|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|+
      |ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)/
      |ordinary (lineDet a i j)|)*
    max (|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|)
      (|ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)

noncomputable def lineIntersectionConstant (a : ℕ) : ℝ :=
  1+∑ i : Fin 4, ∑ j : Fin 4, lineIntersectionCoefficient a i j

theorem lineIntersectionCoefficient_nonneg (a : ℕ) (i j : Fin 4) :
    0≤lineIntersectionCoefficient a i j := by
  unfold lineIntersectionCoefficient
  positivity

theorem lineIntersectionConstant_ge_one (a : ℕ) : 1≤lineIntersectionConstant a := by
  unfold lineIntersectionConstant
  have h : 0≤∑ i : Fin 4, ∑ j : Fin 4, lineIntersectionCoefficient a i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => lineIntersectionCoefficient_nonneg a i j))
  linarith

end UniformConcurrentMesh

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_VertexMargins
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
section VertexMargins

structure VertexMargin (z : ℝ × ℝ) (ε : ℝ) where
  lower : Fin 2 → CutRing
  upper : Fin 2 → CutRing
  lower_outer : ∀ j, realCoordinate z j-2*ε < ordinary (lower j)
  lower_inner : ∀ j, ordinary (lower j) < realCoordinate z j-ε
  upper_inner : ∀ j, realCoordinate z j+ε < ordinary (upper j)
  upper_outer : ∀ j, ordinary (upper j) < realCoordinate z j+2*ε

end VertexMargins

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

structure ConcurrentGeometryData (a D : ℕ) (r : CutRing) where
  epsilon : ℝ
  positive : 0<epsilon
  radius : 100*epsilon ≤ ordinary r
  first_gap : 100*epsilon ≤ Real.goldenRatio-1
  second_gap : 100*epsilon ≤ 2-Real.goldenRatio
  anchors : VertexType D → Fin 4 → CutRing × CutRing
  anchors_spec : ∀ t j, AllowableVertexLine a (vertexRepresentative D t) j →
    cutForm a j (vertexRepresentative D t)=
      ordinary (integralCutForm a j (anchors t j)) ∧
    dist (ordinary (anchors t j).1,ordinary (anchors t j).2)
      (vertexRepresentative D t)<epsilon
  margins : ∀ t : VertexType D,
    VertexMargin (vertexRepresentative D t) epsilon
  mesh : ℕ
  mesh_large : 201 ≤ mesh
  clipping : symmetricWindowLength r ≤ mesh
  mesh_fine : lineIntersectionConstant a*(200/(mesh:ℝ))<epsilon
  window : ℕ
  start : Fin 2 → ℤ
  labels : ∀ t j,
    (start j ≤ endpointLabel ((margins t).lower j) ∧
      endpointLabel ((margins t).lower j) < start j+window) ∧
    (start j ≤ endpointLabel ((margins t).upper j) ∧
      endpointLabel ((margins t).upper j) < start j+window)

abbrev ConcurrentGeometry (a : ℕ) (r : CutRing) :=
  ConcurrentGeometryData a (commonVertexDenominator a) r

end ConcurrentGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_LocalArrangementAssignments
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
section LocalArrangementAssignments
variable {a : ℕ} {ι : Type*}

noncomputable def cutPolygon (a : ℕ) (j : Fin 4) (c : CutRing) : polygonAlgebra a :=
  ⟨halfPlane a j c,halfPlane_mem a j c⟩

end LocalArrangementAssignments

section LocalBooleanAssignments
variable {a : ℕ} {ι κ : Type*}

noncomputable def polygonBooleanPullback [Finite κ] (U : κ → polygonAlgebra a)
    (S : Set (κ → Bool)) : polygonAlgebra a := by
  refine ⟨{p | polygonAssignment U p ∈ S},?_⟩
  have he : {p | polygonAssignment U p ∈ S}=
      ⋃ σ : S, {p | polygonAssignment U p=σ.val} := by
    ext p
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h; exact ⟨⟨_,h⟩,rfl⟩
    · rintro ⟨σ,hσ⟩; exact hσ ▸ σ.property
  rw [he]
  exact BooleanSubalgebra.iSup_mem fun σ => polygonAssignment_fiber_mem U σ.val

noncomputable def polygonFormalMask (U : κ → polygonAlgebra a)
    (V : polygonAlgebra a) : Set (κ → Bool) :=
  {σ | ∃ p, polygonAssignment U p=σ ∧ p ∈ V.val}

end LocalBooleanAssignments

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FinePatchAtlas
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
section FinePatchAtlas

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

noncomputable def refineMesh (n : ℕ) (hn : C.mesh  ≤  n) : ConcurrentGeometry a r :=
  { C with
    mesh := n
    mesh_large := C.mesh_large.trans hn
    clipping := C.clipping.trans hn
    mesh_fine := by
      have hpos : (0:ℝ) < C.mesh := by exact_mod_cast (show 0 < C.mesh by have := C.mesh_large; omega)
      have hle : (C.mesh:ℝ) ≤ n := by exact_mod_cast hn
      have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 200) hpos hle
      exact (mul_le_mul_of_nonneg_left h (by linarith [lineIntersectionConstant_ge_one a])).trans_lt C.mesh_fine }

end ConcurrentGeometry

end FinePatchAtlas

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InwardPlanarGerms
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

section ConcurrentPositiveDecisions
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

noncomputable def positiveDecision (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (j : Fin 4) : polygonAlgebra a :=
  spatialTranslate (u+C.anchors t j) (initialTest a r ⟨j.val+1,by omega⟩)

noncomputable def marginPolygon (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) : polygonAlgebra a :=
  spatialTranslate u (coordinateRectangle a (C.margins t).lower (C.margins t).upper)

end ConcurrentGeometry
end ConcurrentPositiveDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentInwardModel
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
section ConcurrentInwardModel
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

noncomputable def inwardGate (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (k : Fin 2) : polygonAlgebra a :=
  if realCoordinate z k=0 then C.positiveDecision t u (axisDirection k)
  else if realCoordinate z k=1 then (C.positiveDecision t u (axisDirection k))ᶜ
  else wholePolygon a

noncomputable def inwardMargin (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) : polygonAlgebra a :=
  C.marginPolygon t u ⊓ C.inwardGate t u z 0 ⊓ C.inwardGate t u z 1

noncomputable def localDecision (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (j : Fin 4) (c : CutRing) : polygonAlgebra a :=
  if cutForm a j z=ordinary c then (C.positiveDecision t u j)ᶜ
  else if cutForm a j z<ordinary c then ⊤ else ⊥

end ConcurrentGeometry
end ConcurrentInwardModel

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InactiveNeighborhoodActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r) {ι : Type*}

def InwardChartNeighborhood (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (z : ℝ × ℝ) : Prop :=
  ∀ y : ℝ × ℝ, dist y z<C.epsilon/2 → ∀ k,
    ordinary ((C.margins t).lower k+pointCoordinate u k) < realCoordinate y k ∧
    realCoordinate y k<ordinary ((C.margins t).upper k+pointCoordinate u k)

def InwardChartAnchor (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) : Prop :=
  ∀ i, cutForm a (j i) z=ordinary (c i) →
    integralCutForm a (j i) (u+C.anchors t (j i))=c i

def InwardChartBound (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) : Prop :=
  ∀ i, cutForm a (j i) z=ordinary (c i) → ∀ y : ℝ × ℝ,
    (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
      realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
    ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (j i)) k)|<3*C.epsilon

def InwardChartBoundaryAnchor (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (z : ℝ × ℝ) : Prop :=
  ∀ k, realCoordinate z k=0 ∨ realCoordinate z k=1 →
    ordinary (pointCoordinate (u+C.anchors t (axisDirection k)) k)=realCoordinate z k

def InwardChartBoundaryBound (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (z : ℝ × ℝ) : Prop :=
  ∀ d, realCoordinate z d=0 ∨ realCoordinate z d=1 → ∀ y : ℝ × ℝ,
    (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
      realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
    ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (axisDirection d)) k)|<3*C.epsilon

def InwardChart (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) :=
  {p : VertexType (commonVertexDenominator a) × (CutRing × CutRing) //
    C.InwardChartNeighborhood p.1 p.2 z ∧ C.InwardChartAnchor p.1 p.2 j c z ∧
    C.InwardChartBound p.1 p.2 j c z ∧ C.InwardChartBoundaryAnchor p.1 p.2 z ∧
    C.InwardChartBoundaryBound p.1 p.2 z}

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)
def vertex : VertexType (commonVertexDenominator a) := T.val.1
def offset : CutRing × CutRing := T.val.2
end InwardChart

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

noncomputable def polygons [Finite ι] {κ : Type*} (R : κ → polygonAlgebra a) (i : κ) : polygonAlgebra a :=
  polygonBooleanPullback (fun i => C.localDecision T.vertex T.offset z (j i) (c i))
    (polygonFormalMask (fun i => cutPolygon a (j i) (c i)) (R i))

end InwardChart
end ConcurrentGeometry

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClippedGerms
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section ClippedGerms

structure ClippedGerm (a : ℕ) (r : CutRing) (j : Fin 4)
    (u : CutRing × CutRing) (z : ℝ × ℝ) where
  period : Fin 2 → ℤ
  radius : ℝ
  radius_pos : 0 < radius
  valid : let v := u+((period 0:CutRing),(period 1:CutRing))
    ∀ p : GenericSquare a, dist p.val z < radius →
      (p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ↔
        (∀ d, ordinary (pointCoordinate v d-r) ≤ realCoordinate p.val d ∧
          realCoordinate p.val d<ordinary (pointCoordinate v d+r)) ∧
        ordinary (integralCutForm a j v) ≤ cutForm a j p.val)

namespace ClippedGerm
variable {a : ℕ} {r : CutRing} {slope : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r slope u z)

def offset : CutRing × CutRing := u+((G.period 0:CutRing),(G.period 1:CutRing))

end ClippedGerm
end ClippedGerms

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r) {κ : Type*} [Finite κ]

noncomputable def coordinateGate (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (j : κ → Fin 2) (c : κ → CutRing) (σ : κ → Bool) : polygonAlgebra a :=
  C.inwardMargin t u z ⊓ polygonBooleanPullback
    (fun i => C.localDecision t u z (axisDirection (j i)) (c i)) {σ}

end ConcurrentGeometry

namespace ClippedGerm
variable {a : ℕ} {r : CutRing} {slope : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r slope u z)

noncomputable def axialCut (i : Fin 2 × Bool) : CutRing :=
  if i.2 then pointCoordinate G.offset i.1+r else pointCoordinate G.offset i.1-r

end ClippedGerm

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CoordinateModels
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section CoordinateModels

structure CoordinateGerm (a : ℕ) (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ) where
  period : ℤ
  radius : ℝ
  radius_pos : 0 < radius
  valid : ∀ p : GenericSquare a, dist p.val z < radius →
    (p ∈ (spatialTranslate u (coordinatePrimitive a d)).val ↔
      ordinary (pointCoordinate u d+(period:CutRing)) ≤ realCoordinate p.val d ∧
      realCoordinate p.val d<ordinary (pointCoordinate u d+(period:CutRing)+(cutTau-1)))

namespace CoordinateGerm
variable {a : ℕ} {d : Fin 2} {u : CutRing × CutRing} {z : ℝ × ℝ} (G : CoordinateGerm a d u z)
noncomputable def lower : CutRing := pointCoordinate u d+(G.period:CutRing)
noncomputable def upper : CutRing := G.lower+(cutTau-1)

end CoordinateGerm

end CoordinateModels

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LocalClippedBoxFormula
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section LocalClippedBoxFormula

namespace ClippedGerm

def BoxValid {a : ℕ} {r : CutRing} {j : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r j u z) : Prop :=
  ∀ p : GenericSquare a, dist p.val z<G.radius →
    (p ∈ (spatialTranslate u (coordinateRectangle a (fun _ => -r) (fun _ => r))).val ↔
      ∀ d, ordinary (pointCoordinate G.offset d-r) ≤ realCoordinate p.val d ∧
        realCoordinate p.val d<ordinary (pointCoordinate G.offset d+r))
end ClippedGerm

end LocalClippedBoxFormula

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GlobalAlignedCentrality
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
section GlobalAlignedCentrality

variable {H Q ι : Type*} [Group H] [Group Q]

theorem CentralOn.iSup_directed (q : H →* Q) (S : ι → Subgroup H) [Nonempty ι]
    (hd : Directed (· ≤ ·) S) (h : ∀ i, CentralOn q (S i)) : CentralOn q (⨆ i, S i) := by
  rw [centralOn_iff]
  intro x hx hqx y hy
  obtain ⟨i,hi⟩ := (Subgroup.mem_iSup_of_directed hd).mp hx
  obtain ⟨j,hj⟩ := (Subgroup.mem_iSup_of_directed hd).mp hy
  obtain ⟨k,hik,hjk⟩ := hd i j
  exact (centralOn_iff q (S k)).mp (h k) x (hik hi) hqx y (hjk hj)

end GlobalAlignedCentrality

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FrameCentrality
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
section FrameCentrality

variable {H Q : Type*} [Group H] [Group Q]

theorem CentralOn.conjugate {q : H →* Q} {S : Subgroup H} (h : CentralOn q S) (z : H) :
    CentralOn q (S.map (MulAut.conj z).toMonoidHom) := by
  rw [centralOn_iff] at h ⊢
  rintro _ ⟨x,hx,rfl⟩ he _ ⟨y,hy,rfl⟩
  change q (z*x*z⁻¹) = 1 at he
  have hqx : q x = 1 := by
    have hh := congrArg (fun t => (q z)⁻¹*t*q z) he
    simpa [mul_assoc] using hh
  exact (h x hx hqx y hy).map (MulAut.conj z).toMonoidHom

end FrameCentrality

end SimpleAmenable
end
end

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

theorem polygon_mem_finset_inf {a : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → polygonAlgebra a) (x : GenericSquare a) :
    x∈(s.inf f).val ↔ ∀ j∈s, x∈(f j).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.inf_empty,Finset.notMem_empty,IsEmpty.forall_iff,implies_true]
             exact iff_true_intro (Set.mem_univ x)
  | @insert j s hjs ih =>
    rw [Finset.inf_insert]
    change x∈(f j).val ∧ x∈(s.inf f).val ↔ _
    rw [ih]
    simp only [Finset.mem_insert,forall_eq_or_imp]

end FiniteSlotRefinement

end SimpleAmenable
end
end

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

theorem mem_arrangementAtom {ι : Type*} [Fintype ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → CutRing) (σ : ι → Bool) (p : GenericSquare a) :
    p∈(arrangementAtom a j c σ).val ↔ p.val∈strictLineCell a j (ordinary ∘ c) σ := by
  rw [arrangementAtom,polygon_mem_finset_inf]
  simp only [Finset.mem_univ,true_implies,strictLineCell,Set.mem_ofPred_eq,Function.comp_apply]
  apply forall_congr'
  intro i
  cases σ i
  · change (¬cutForm a (j i) p.val<ordinary (c i)) ↔ ordinary (c i) < cutForm a (j i) p.val
    exact ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) (p.property.2.2 (j i) (c i)).symm,
      fun h => not_lt.mpr h.le⟩
  · rfl

theorem mem_arrangementPattern {ι : Type*} [Fintype ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → CutRing) (p : GenericSquare a) :
    p∈(arrangementAtom a j c (arrangementPattern a j c p)).val := by
  rw [mem_arrangementAtom]
  intro i
  by_cases h : cutForm a (j i) p.val<ordinary (c i)
  · simp [arrangementPattern,h]
  · simpa [arrangementPattern,h] using
      lt_of_le_of_ne (le_of_not_gt h) (p.property.2.2 (j i) (c i)).symm

theorem strictLineCell_convex {ι : Type*} (a : ℕ)
    (j : ι → Fin 4) (c : ι → ℝ) (σ : ι → Bool) :
    Convex ℝ (strictLineCell a j c σ) := by
  have hlin (i : ι) : IsLinearMap ℝ (cutForm a (j i)) :=
    ⟨cutForm_add a (j i),fun t p => cutForm_smul a (j i) t p⟩
  simp only [strictLineCell,Set.ofPred_forall]
  apply convex_iInter
  intro i
  cases σ i
  · exact convex_halfSpace_gt (hlin i) (c i)
  · exact convex_halfSpace_lt (hlin i) (c i)

theorem generic_mem_barrierRegion {ι : Type*} {a : ℕ} {j : ι → Fin 4}
    {c : ι → CutRing} {B : Set (ℝ×ℝ)} (hB : SupportedBarriers a j c B)
    (p : GenericSquare a) : p.val∈barrierRegion B := by
  refine ⟨generic_mem_squareInterior p,?_⟩
  intro hp
  obtain ⟨i,hi⟩ := hB p.val hp
  exact p.property.2.2 (j i) (c i) hi

theorem arrangementAtom_same_component {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) (σ : ι → Bool) (p q : GenericSquare a)
    (hp : p∈(arrangementAtom a j c σ).val) (hq : q∈(arrangementAtom a j c σ).val) :
    q.val∈connectedComponentIn (barrierRegion B) p.val := by
  let C := squareInterior ∩ strictLineCell a j (ordinary ∘ c) σ
  have hC : Convex ℝ C := ((convex_Ioo (0:ℝ) 1).prod (convex_Ioo (0:ℝ) 1)).inter
    (strictLineCell_convex a j (ordinary ∘ c) σ)
  have hpC : p.val∈C := ⟨generic_mem_squareInterior p,(mem_arrangementAtom _ _ _ _ _).mp hp⟩
  have hqC : q.val∈C := ⟨generic_mem_squareInterior q,(mem_arrangementAtom _ _ _ _ _).mp hq⟩
  have hCB : C⊆barrierRegion B := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hxB
    obtain ⟨i,hi⟩ := hB x hxB
    have hc := hx.2 i
    cases hσ : σ i <;> simp only [hσ,Bool.false_eq_true,ite_false,ite_true,Function.comp_apply] at hc
    · exact (ne_of_gt hc) hi
    · exact (ne_of_lt hc) hi
  exact hC.isPreconnected.subset_connectedComponentIn hpC hCB hqC

theorem barrierComponentCell_polygon {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) (x : ℝ×ℝ) :
    barrierComponentCell (a:=a) B x∈polygonAlgebra a := by
  let T := (Finset.univ : Finset (ι → Bool)).filter (fun σ => ∃p : GenericSquare a,
    p∈(arrangementAtom a j c σ).val ∧ p∈barrierComponentCell B x)
  let P : polygonAlgebra a := T.sup (arrangementAtom a j c)
  have hmem (p : GenericSquare a) : p∈P.val ↔ ∃σ∈T,p∈(arrangementAtom a j c σ).val := by
    dsimp [P]
    induction T using Finset.induction_on with
    | empty => simp
    | @insert σ T hσ ih =>
      rw [Finset.sup_insert]
      change (p∈(arrangementAtom a j c σ).val ∨ p∈(T.sup (arrangementAtom a j c)).val) ↔ _
      rw [ih]
      simp only [Finset.mem_insert,exists_eq_or_imp]
  have he : P.val=barrierComponentCell B x := by
    ext p
    rw [hmem]
    constructor
    · rintro ⟨σ,hσ,hp⟩
      obtain ⟨q,hq,hqx⟩ := (Finset.mem_filter.mp hσ).2
      have hqp := arrangementAtom_same_component hB σ q p hq hp
      change p.val∈connectedComponentIn (barrierRegion B) x
      rw [connectedComponentIn_eq hqx]
      exact hqp
    · intro hp
      refine ⟨arrangementPattern a j c p,?_,mem_arrangementPattern a j c p⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,mem_arrangementPattern a j c p,hp⟩
  exact he ▸ P.property

end BarrierCells

section BarrierPartitions
open Classical Set

noncomputable def barrierPolygonAt {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) (p : GenericSquare a) : polygonAlgebra a :=
  ⟨barrierComponentCell B p.val,barrierComponentCell_polygon hB p.val⟩

theorem barrierPolygonAt_eq_of_pattern {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) {p q : GenericSquare a}
    (h : arrangementPattern a j c p=arrangementPattern a j c q) :
    barrierPolygonAt hB p=barrierPolygonAt hB q := by
  have hp := mem_arrangementPattern a j c p
  rw [h] at hp
  have hq := mem_arrangementPattern a j c q
  have hh := connectedComponentIn_eq (arrangementAtom_same_component hB _ p q hp hq)
  apply Subtype.ext
  change {r : GenericSquare a | r.val∈connectedComponentIn (barrierRegion B) p.val}=
    {r : GenericSquare a | r.val∈connectedComponentIn (barrierRegion B) q.val}
  rw [hh]

theorem barrierPolygonAt_finite_range {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) : (Set.range (barrierPolygonAt hB)).Finite := by
  let f (σ : ι → Bool) : polygonAlgebra a :=
    if h : ∃p : GenericSquare a,arrangementPattern a j c p=σ then
      barrierPolygonAt hB h.choose else ⊥
  apply (Set.finite_range f).subset
  rintro C ⟨p,rfl⟩
  refine ⟨arrangementPattern a j c p,?_⟩
  have h : ∃q : GenericSquare a,arrangementPattern a j c q=arrangementPattern a j c p := ⟨p,rfl⟩
  simp only [f,dite_eq_left h]
  exact barrierPolygonAt_eq_of_pattern hB h.choose_spec

noncomputable def finiteBarrierPartition {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) : FinitePolygonPartition a where
  cells := (barrierPolygonAt_finite_range hB).toFinset
  nonempty := by
    intro C hC
    obtain ⟨p,rfl⟩ := (Set.Finite.mem_toFinset _).mp hC
    exact ⟨p,mem_connectedComponentIn (generic_mem_barrierRegion hB p)⟩
  cover := by
    intro p
    refine ⟨barrierPolygonAt hB p,⟨?_,?_⟩,?_⟩
    · exact (Set.Finite.mem_toFinset _).mpr ⟨p,rfl⟩
    · exact mem_connectedComponentIn (generic_mem_barrierRegion hB p)
    · intro C hC
      obtain ⟨q,rfl⟩ := (Set.Finite.mem_toFinset _).mp hC.1
      apply Subtype.ext
      change {r : GenericSquare a | r.val∈connectedComponentIn (barrierRegion B) q.val}=
        {r : GenericSquare a | r.val∈connectedComponentIn (barrierRegion B) p.val}
      rw [connectedComponentIn_eq hC.2]

end BarrierPartitions

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

noncomputable def barrierMarkedParameters {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j))) : Finset ℝ :=
  (M.filter (fun z => z.val.1=i ∧ barrierSitePoint z∈squareInterior ∧
    cutForm a j (barrierSitePoint z)=ordinary c)).image
      (fun z => barrierLineParameter j (barrierSitePoint z))

noncomputable def barrierSubdivision {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j))) : Finset ℝ :=
  {barrierLineLower a j c,barrierLineUpper a j c} ∪ barrierMarkedParameters ha i j c M

noncomputable def barrierActivation {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (s : ℝ) : Bool := decide (∃z,z.val.1=i ∧
      barrierSitePoint z=barrierLinePoint a j c s ∧ b z=true)

noncomputable def barrierActiveIntervals {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :
    Finset (ℝ×ℝ) :=
  ((barrierSubdivision ha i j c M) ×ˢ (barrierSubdivision ha i j c M)).filter
    (fun st => ConsecutiveSubdivision (barrierSubdivision ha i j c M) st.1 st.2 ∧
      barrierActivation ha i j c b st.1=true)

noncomputable def sampledBarriers {a m : ℕ} (ha : 0<a) (i : Fin m) (N : ℝ)
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :
    Set (ℝ×ℝ) :=
  {p | ∃l : BarrierLineIndex a N,∃st∈barrierActiveIntervals ha i l.1 l.2.val (M l.1) (b l.1),
    p∈barrierLinePoint a l.1 l.2.val '' Icc st.1 st.2}

theorem sampledBarriers_supported {a m : ℕ} (ha : 0<a) (i : Fin m) (N : ℝ)
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :
    SupportedBarriers a (fun l : BarrierLineIndex a N => l.1) (fun l => l.2.val)
      (sampledBarriers ha i N M b) := by
  rintro p ⟨l,st,hst,t,ht,rfl⟩
  exact ⟨l,cutForm_barrierLinePoint a l.1 l.2.val t⟩

noncomputable def sampledPolygonPartition {a m : ℕ} (ha : 0<a) (i : Fin m)
    {N : ℝ} (hN : 0<N)
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :
    FinitePolygonPartition a := by
  letI := barrierLineIndexFintype a hN
  exact finiteBarrierPartition (sampledBarriers_supported ha i N M b)

end BarrierAlgorithm

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

abbrev PartitionCell {a m : ℕ} (P : TrackPolygonPartition a m) := Σi : Fin m,↥(P i).cells

noncomputable def partitionCellSet {a m : ℕ} {P : TrackPolygonPartition a m}
    (c : PartitionCell P) : Set (TrackPoint a m) := {x | x.1=c.1 ∧ x.2∈c.2.val.val}

theorem partitionCellSet_nonempty {a m : ℕ} {P : TrackPolygonPartition a m}
    (c : PartitionCell P) : (partitionCellSet c).Nonempty := by
  obtain ⟨p,hp⟩ := (P c.1).nonempty c.2.val c.2.property
  exact ⟨(c.1,p),rfl,hp⟩

theorem partitionCellSet_cover {a m : ℕ} (P : TrackPolygonPartition a m) (x : TrackPoint a m) :
    ∃!c : PartitionCell P,x∈partitionCellSet c := by
  obtain ⟨C,⟨hC,hx⟩,hu⟩ := (P x.1).cover x.2
  refine ⟨⟨x.1,⟨C,hC⟩⟩,⟨rfl,hx⟩,?_⟩
  rintro ⟨i,D,hD⟩ ⟨hi,hxD⟩
  dsimp at hi
  subst i
  have he := hu D ⟨hD,hxD⟩
  subst D
  rfl

theorem partitionCellSet_eq_of_mem {a m : ℕ} {P : TrackPolygonPartition a m}
    {c d : PartitionCell P} {x : TrackPoint a m}
    (hc : x∈partitionCellSet c) (hd : x∈partitionCellSet d) : c=d :=
  (partitionCellSet_cover P x).unique hc hd

def PartitionArrow {a m : ℕ} (P Q : TrackPolygonPartition a m) (g : polygonFullGroup a m) : Prop :=
  ∀c : PartitionCell P,∃d : PartitionCell Q,
    g.val '' partitionCellSet c=partitionCellSet d ∧ ∃u : CutRing×CutRing,
      ∀x∈partitionCellSet c,(g.val x).2.val=x.2.val+(ordinary u.1,ordinary u.2)

namespace PartitionArrow
variable {a m : ℕ} {P Q R : TrackPolygonPartition a m} {g h : polygonFullGroup a m}

theorem one (P : TrackPolygonPartition a m) : PartitionArrow P P 1 := by
  intro c
  refine ⟨c,?_,0,?_⟩
  · exact Set.image_id _
  · intro x _
    change x.2.val=x.2.val+(ordinary (0:CutRing),ordinary (0:CutRing))
    simp only [map_zero]
    exact (add_zero x.2.val).symm

theorem mul (hg : PartitionArrow Q R g) (hh : PartitionArrow P Q h) : PartitionArrow P R (g*h) := by
  intro c
  obtain ⟨d,hd,u,hu⟩ := hh c
  obtain ⟨e,he,v,hv⟩ := hg d
  refine ⟨e,?_,u+v,?_⟩
  · change (g.val ∘ h.val) '' partitionCellSet c=partitionCellSet e
    exact (Set.image_image g.val h.val (partitionCellSet c)).symm.trans (by rw [hd,he])
  · intro x hx
    have hhx : h.val x∈partitionCellSet d := by rw [←hd]; exact ⟨x,hx,rfl⟩
    change (g.val (h.val x)).2.val=x.2.val+_
    rw [hv _ hhx,hu _ hx]
    simp only [Prod.fst_add,Prod.snd_add,map_add,Prod.mk_add_mk,add_assoc]

theorem inv (hg : PartitionArrow P Q g) : PartitionArrow Q P g⁻¹ := by
  intro d
  obtain ⟨y,hy⟩ := partitionCellSet_nonempty d
  obtain ⟨c,hc,-⟩ := partitionCellSet_cover P (g.val.symm y)
  obtain ⟨e,he,u,hu⟩ := hg c
  have hye : y∈partitionCellSet e := by rw [←he]; exact ⟨g.val.symm y,hc,g.val.apply_symm_apply y⟩
  have hde : d=e := partitionCellSet_eq_of_mem hy hye
  subst e
  refine ⟨c,?_, -u,?_⟩
  · rw [←he]
    exact g.val.symm_image_image _
  · intro x hx
    obtain ⟨w,hw,rfl⟩ := (Set.mem_image g.val _ _).mp (he.symm ▸ hx)
    have h := hu w hw
    change (g.val.symm (g.val w)).2.val=(g.val w).2.val+_
    rw [g.val.symm_apply_apply,h]
    simp only [Prod.fst_neg,Prod.snd_neg,map_neg]
    apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> ring

end PartitionArrow
end PartitionArrows

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_FinitePartitionArrows
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
section FinitePartitionArrows
open Classical Set
namespace PartitionArrow
variable {a m : ℕ} {P Q : TrackPolygonPartition a m} {g h : polygonFullGroup a m}

noncomputable def cellMap (hg : PartitionArrow P Q g) (c : PartitionCell P) : PartitionCell Q :=
  (hg c).choose

theorem cellMap_image (hg : PartitionArrow P Q g) (c : PartitionCell P) :
    g.val '' partitionCellSet c=partitionCellSet (hg.cellMap c) := (hg c).choose_spec.1

theorem eq_of_cellMap (hg : PartitionArrow P Q g) (hh : PartitionArrow P Q h)
    (he : hg.cellMap=hh.cellMap) : g=h := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨c,hc,-⟩ := partitionCellSet_cover P x
  obtain ⟨u,hu⟩ := (hg c).choose_spec.2
  obtain ⟨v,hv⟩ := (hh c).choose_spec.2
  have him : g.val '' partitionCellSet c=h.val '' partitionCellSet c := by
    rw [hg.cellMap_image,hh.cellMap_image,he]
  have hne := partitionCellSet_nonempty c
  have hxshift : ordinary u.1=ordinary v.1 := by
    refine bounded_coordinate_shift_unique (partitionCellSet c) (fun t => t.2.val.1)
      (fun t => t.2.val.1) hne (show BddAbove ((fun t => t.2.val.1) '' partitionCellSet c) from ?_)
      g.val h.val him (ordinary u.1) (ordinary v.1) ?_ ?_
    · exact ⟨1,by rintro y ⟨z,hz,rfl⟩; exact z.2.property.1.2.le⟩
    · intro z hz
      exact congrArg Prod.fst (hu z hz)
    · intro z hz
      exact congrArg Prod.fst (hv z hz)
  have hyshift : ordinary u.2=ordinary v.2 := by
    refine bounded_coordinate_shift_unique (partitionCellSet c) (fun t => t.2.val.2)
      (fun t => t.2.val.2) hne (show BddAbove ((fun t => t.2.val.2) '' partitionCellSet c) from ?_)
      g.val h.val him (ordinary u.2) (ordinary v.2) ?_ ?_
    · exact ⟨1,by rintro y ⟨z,hz,rfl⟩; exact z.2.property.2.1.2.le⟩
    · intro z hz
      exact congrArg Prod.snd (hu z hz)
    · intro z hz
      exact congrArg Prod.snd (hv z hz)
  apply Prod.ext
  · have hgc : g.val x∈partitionCellSet (hg.cellMap c) := by rw [←hg.cellMap_image]; exact ⟨x,hc,rfl⟩
    have hhc : h.val x∈partitionCellSet (hh.cellMap c) := by rw [←hh.cellMap_image]; exact ⟨x,hc,rfl⟩
    rw [he] at hgc
    exact hgc.1.trans hhc.1.symm
  · apply Subtype.ext
    rw [hu x hc,hv x hc,hxshift,hyshift]

instance arrows_finite (P Q : TrackPolygonPartition a m) :
    Finite {g : polygonFullGroup a m // PartitionArrow P Q g} := by
  apply Finite.of_injective (fun g : {g : polygonFullGroup a m // PartitionArrow P Q g} => g.property.cellMap)
  intro g h he
  apply Subtype.ext
  exact eq_of_cellMap g.property h.property he

end PartitionArrow
end FinitePartitionArrows

section SampledPartitionMotion
open Classical Set

noncomputable def BarrierSignalSystem.sampledPartition {a m : ℕ} {ha : 0 < a} {Q B : ℝ}
    (S : BarrierSignalSystem a ha Q B) (n : ℕ) (b : BarrierBits a m ha) : TrackPolygonPartition a m :=
  fun i => sampledPolygonPartition ha i (sourceDyadicN_pos n)
    (fun j => S.marks (sourceDyadicN_pos n) j (barrierFirstBits b j)) (barrierSecondBits b)

end SampledPartitionMotion

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_UniformShapeMatchings
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
section UniformShapeMatchings
open Classical Set

noncomputable def partitionShapeSetoid (a m : ℕ) : Setoid (TrackPolygonPartition a m) where
  r P Q := ∃g : polygonFullGroup a m,PartitionArrow P Q g
  iseqv := ⟨fun P => ⟨1,PartitionArrow.one P⟩,
    fun ⟨g,hg⟩ => ⟨g⁻¹,hg.inv⟩,
    fun ⟨g,hg⟩ ⟨h,hh⟩ => ⟨h*g,hh.mul hg⟩⟩

noncomputable def partitionBaseline {a m : ℕ} (P : TrackPolygonPartition a m) : TrackPolygonPartition a m :=
  (Quotient.mk (partitionShapeSetoid a m) P).out

noncomputable def matchingSupport {a m : ℕ} (P : TrackPolygonPartition a m) : Finset (polygonFullGroup a m) :=
  (show Set.Finite {g : polygonFullGroup a m | PartitionArrow (partitionBaseline P) P g} from
    @Set.toFinite _ _ (PartitionArrow.arrows_finite (partitionBaseline P) P)).toFinset

@[simp] theorem mem_matchingSupport {a m : ℕ} (P : TrackPolygonPartition a m) (g : polygonFullGroup a m) :
    g∈matchingSupport P ↔ PartitionArrow (partitionBaseline P) P g := Set.Finite.mem_toFinset _

end UniformShapeMatchings

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TranslationRoutingHelpers
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
section TranslationRoutingHelpers

namespace PrivateRoutingBank
variable {m : ℕ} {i : Fin 5 → Fin m} (P : PrivateRoutingBank i)

noncomputable def blockOffsets (d : Fin m → CutRing × CutRing) : Fin m → CutRing × CutRing :=
  Function.extend (fun p : Fin 5 × Fin 5 => P.row p.1 p.2) (fun p => d (i p.1)) 0

@[simp] theorem blockOffsets_apply (d : Fin m → CutRing × CutRing) (j k : Fin 5) :
    P.blockOffsets d (P.row j k)=d (i j) := by
  have hf : Function.FactorsThrough (fun p : Fin 5 × Fin 5 => d (i p.1))
      (fun p : Fin 5 × Fin 5 => P.row p.1 p.2) := by
    intro p q he
    obtain ⟨j,k⟩ := p
    obtain ⟨l,t⟩ := q
    change P.row j k=P.row l t at he
    change d (i j)=d (i l)
    by_cases hk : k=0 <;> by_cases ht : t=0
    · subst k; subst t
      rw [P.source j,P.source l] at he
      exact congrArg d he
    · subst k
      rw [P.source j] at he
      exact (P.fresh l t ht j he.symm).elim
    · subst t
      rw [P.source l] at he
      exact (P.fresh j k hk l he).elim
    · exact congrArg (fun q => d (i q)) (P.separate j k l t hk ht he).1
  exact hf.extend_apply 0 (j,k)

end PrivateRoutingBank

end TranslationRoutingHelpers

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedNerve
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimplicialDiagonal.diagonal_connected _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C) [W.IsMultiplicative]
noncomputable def homologyIso (n : ℕ) :
    (SimplicialDiagonal.nerveDiagonal.obj (horizontal W)).homology DiagonalResolution.Z n ≅
      (nerve C).homology DiagonalResolution.Z n := by
  haveI := SimplicialDiagonal.nerveDiagonal_isIso (constantMap W)
    (fun p => inferInstanceAs (constant W p.unop.len).IsEquivalence) n
  exact (SSet.homologyFunctor DiagonalResolution.Z n).mapIso (diagonalIso W) ≪≫
    (asIso (SSet.homologyMap (SimplicialDiagonal.nerveDiagonal.map (constantMap W))
      DiagonalResolution.Z n)).symm ≪≫
    (SSet.homologyFunctor DiagonalResolution.Z n).mapIso (constantDiagonalIso (C:=C))
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapEssSurj _root_.OAI.IntervalBar.Diagram.mapFaithful _root_.OAI.IntervalBar.Diagram.mapFull _root_.OAI.IntervalBar.Diagram.mapIsEquivalence _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_nerve_connected _root_.OAI.IntervalBar.Diagram.zero_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramGroupoid _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory MonoidalCategory
namespace RestrictedNerve

open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable (I : Type) [Preorder I]

variable {I}
noncomputable def untransposeDiagramObj {n : ℕ} (F : Strings (diagramProperty W I) n) :
    Diagram (Strings W n) I where
  obj i j h := ⟨{
    obj t := ((F.obj.obj t).obj i j h).obj
    map f := (F.obj.map f).hom.app i j h
    map_id t := congrArg (fun f => f.hom.app i j h) (F.obj.map_id t)
    map_comp f g := congrArg (fun f => f.hom.app i j h) (F.obj.map_comp f g) }⟩
  unit i := {
    hom := ⟨{
      app t := ((F.obj.obj t).unit i).hom.hom
      naturality t s f := by
        have he := (F.obj.map f).hom.unit i
        change (F.obj.map f).hom.app i i le_rfl ≫ (((F.obj.obj s).unit i).hom.hom ≫ 𝟙 _) =
          ((F.obj.obj t).unit i).hom.hom ≫ 𝟙 _ at he
        erw [Category.comp_id, Category.comp_id] at he
        change (F.obj.map f).hom.app i i le_rfl ≫ ((F.obj.obj s).unit i).hom.hom =
          ((F.obj.obj t).unit i).hom.hom ≫ 𝟙 _
        erw [Category.comp_id]
        exact he }, fun t => ((F.obj.obj t).unit i).hom.property⟩
    inv := ⟨{
      app t := ((F.obj.obj t).unit i).inv.hom
      naturality t s f := by
        have he := (F.obj.map f).hom.unit i
        change (F.obj.map f).hom.app i i le_rfl ≫ (((F.obj.obj s).unit i).hom.hom ≫ 𝟙 _) =
          ((F.obj.obj t).unit i).hom.hom ≫ 𝟙 _ at he
        erw [Category.comp_id, Category.comp_id] at he
        change 𝟙 _ ≫ ((F.obj.obj s).unit i).inv.hom =
          ((F.obj.obj t).unit i).inv.hom ≫ (F.obj.map f).hom.app i i le_rfl
        apply (cancel_mono ((F.obj.obj s).unit i).hom.hom).mp
        erw [Category.id_comp, wide_inv_hom, Category.assoc, he, wide_inv_hom] },
          fun t => ((F.obj.obj t).unit i).inv.property⟩
    hom_inv_id := by
      apply WideSubcategory.hom_ext; ext t
      exact congrArg (fun g => g.hom) ((F.obj.obj t).unit i).hom_inv_id
    inv_hom_id := by
      apply WideSubcategory.hom_ext; ext t
      exact congrArg (fun g => g.hom) ((F.obj.obj t).unit i).inv_hom_id }
  cut i j k hij hjk := {
    hom := ⟨{
      app t := ((F.obj.obj t).cut i j k hij hjk).hom.hom
      naturality t s f := by
        have he := (F.obj.map f).hom.cut i j k hij hjk
        change ((F.obj.map f).hom.app i j hij ⊗ₘ (F.obj.map f).hom.app j k hjk) ≫
          (𝟙 _ ≫ ((F.obj.obj s).cut i j k hij hjk).hom.hom) =
          (𝟙 _ ≫ ((F.obj.obj t).cut i j k hij hjk).hom.hom) ≫ (F.obj.map f).hom.app i k _ at he
        erw [Category.id_comp, Category.id_comp] at he
        exact he },fun t => ((F.obj.obj t).cut i j k hij hjk).hom.property⟩
    inv := ⟨{
      app t := ((F.obj.obj t).cut i j k hij hjk).inv.hom
      naturality t s f := by
        have he := (F.obj.map f).hom.cut i j k hij hjk
        change ((F.obj.map f).hom.app i j hij ⊗ₘ (F.obj.map f).hom.app j k hjk) ≫
          (𝟙 _ ≫ ((F.obj.obj s).cut i j k hij hjk).hom.hom) =
          (𝟙 _ ≫ ((F.obj.obj t).cut i j k hij hjk).hom.hom) ≫ (F.obj.map f).hom.app i k _ at he
        erw [Category.id_comp, Category.id_comp] at he
        change (F.obj.map f).hom.app i k _ ≫ ((F.obj.obj s).cut i j k hij hjk).inv.hom =
          ((F.obj.obj t).cut i j k hij hjk).inv.hom ≫
          ((F.obj.map f).hom.app i j hij ⊗ₘ (F.obj.map f).hom.app j k hjk)
        apply (cancel_epi ((F.obj.obj t).cut i j k hij hjk).hom.hom).mp
        repeat' erw [← Category.assoc]
        erw [wide_hom_inv, Category.id_comp]
        erw [←he,Category.assoc,wide_hom_inv]
        exact Category.comp_id _ },
          fun t => ((F.obj.obj t).cut i j k hij hjk).inv.property⟩
    hom_inv_id := by
      apply WideSubcategory.hom_ext; ext t
      exact congrArg (fun g => g.hom) ((F.obj.obj t).cut i j k hij hjk).hom_inv_id
    inv_hom_id := by
      apply WideSubcategory.hom_ext; ext t
      exact congrArg (fun g => g.hom) ((F.obj.obj t).cut i j k hij hjk).inv_hom_id }
  left_unit i j h := by
    apply WideSubcategory.hom_ext; ext t
    exact congrArg (fun g => g.hom) ((F.obj.obj t).left_unit i j h)
  right_unit i j h := by
    apply WideSubcategory.hom_ext; ext t
    exact congrArg (fun g => g.hom) ((F.obj.obj t).right_unit i j h)
  associativity i j k l hij hjk hkl := by
    apply WideSubcategory.hom_ext; ext t
    exact congrArg (fun g => g.hom) ((F.obj.obj t).associativity i j k l hij hjk hkl)
noncomputable def untransposeDiagramHom {n : ℕ} {A B : Strings (diagramProperty W I) n} (f : A ⟶ B) :
    untransposeDiagramObj W A ⟶ untransposeDiagramObj W B where
  app i j h := ⟨{
    app t := (f.hom.app t).hom.app i j h
    naturality t s g := congrArg (fun f => f.hom.app i j h) (f.hom.naturality g) },
      fun t => f.property t i j h⟩
  unit i := by
    apply WideSubcategory.hom_ext; ext t
    have he := (f.hom.app t).hom.unit i
    change (f.hom.app t).hom.app i i le_rfl ≫ (((B.obj.obj t).unit i).hom.hom ≫ 𝟙 _) =
      ((A.obj.obj t).unit i).hom.hom ≫ 𝟙 _ at he
    change (f.hom.app t).hom.app i i le_rfl ≫ ((B.obj.obj t).unit i).hom.hom =
      ((A.obj.obj t).unit i).hom.hom
    erw [Category.comp_id, Category.comp_id] at he
    exact he
  cut i j k hij hjk := by
    apply WideSubcategory.hom_ext; ext t
    have he := (f.hom.app t).hom.cut i j k hij hjk
    change ((f.hom.app t).hom.app i j hij ⊗ₘ (f.hom.app t).hom.app j k hjk) ≫
        (𝟙 _ ≫ ((B.obj.obj t).cut i j k hij hjk).hom.hom) =
      (𝟙 _ ≫ ((A.obj.obj t).cut i j k hij hjk).hom.hom) ≫ (f.hom.app t).hom.app i k _ at he
    change ((f.hom.app t).hom.app i j hij ⊗ₘ (f.hom.app t).hom.app j k hjk) ≫
      ((B.obj.obj t).cut i j k hij hjk).hom.hom =
      ((A.obj.obj t).cut i j k hij hjk).hom.hom ≫ (f.hom.app t).hom.app i k _
    erw [Category.id_comp, Category.id_comp] at he
    exact he
noncomputable def untransposeDiagram (n : ℕ) : Strings (diagramProperty W I) n ⥤ Diagram (Strings W n) I where
  obj := untransposeDiagramObj W
  map := untransposeDiagramHom W
  map_id A := by
    apply Hom.ext; intro i j h
    apply WideSubcategory.hom_ext; ext t; rfl
  map_comp f g := by
    apply Hom.ext; intro i j h
    apply WideSubcategory.hom_ext; ext t; rfl
noncomputable def diagramEquivalence (n : ℕ) : Diagram (Strings W n) I ≌ Strings (diagramProperty W I) n where
  functor := transposeDiagram W n
  inverse := untransposeDiagram W n
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp A := by
    change (transposeDiagram W n).map (𝟙 A) ≫ 𝟙 _ = 𝟙 _
    erw [Category.comp_id]
    exact (transposeDiagram W n).map_id A
noncomputable instance instIsEquivalenceDiagramStringsPosDiagramsDiagramPropertyTransposeDiagram (n : ℕ) : (transposeDiagram (I:=I) W n).IsEquivalence :=
  (diagramEquivalence W n).isEquivalence_functor
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedMonoidalTranspose
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Functor.LaxMonoidal
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable instance posDiagramInclusionMonoidal (I : Type) [Preorder I] :
    (posDiagramInclusion W I).Monoidal := InducedMonoidal.inclusionMonoidal (diagramInclusion W I)
noncomputable instance posDiagramInclusionEssSurj (n : ℕ) :
    (posDiagramInclusion W (Fin (n+1))).EssSurj where
  mem_essImage X := ⟨(diagramInclusion W (Fin (n+1))).objPreimage X,
    ⟨(diagramInclusion W (Fin (n+1))).objObjPreimageIso X⟩⟩
noncomputable instance posDiagramInclusionEquivalence (n : ℕ) :
    (posDiagramInclusion W (Fin (n+1))).IsEquivalence where
  full := inferInstanceAs (inducedFunctor _).Full
  faithful := inferInstanceAs (inducedFunctor _).Faithful
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedTripleMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
lemma map₂_reindex_unit_app {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Diagram (Strings W m) I) J) (i : J)
    (j k : I) (h : j ≤ k) (t : Fin (n+1)) :
    ((((Diagram.map (Diagram.map (reindex W u))).obj A).unit i).hom.app j k h).hom.app t =
      ((A.unit i).hom.app j k h).hom.app (u.obj t) := by
  change (((Diagram.map (reindex W u)).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (Diagram.map (reindex W u))).app j k h).hom.app t = _
  erw [comp_app, map_η_app (I:=I) (reindex W u)]
  change ((A.unit i).hom.app j k h).hom.app (u.obj t) ≫ 𝟙 _ = _
  exact Category.comp_id _

lemma map₂_reindex_cut_app {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Diagram (Strings W m) I) J) (i j k : J)
    (hij : i ≤ j) (hjk : j ≤ k) (l r : I) (h : l ≤ r) (t : Fin (n+1)) :
    ((((Diagram.map (Diagram.map (reindex W u))).obj A).cut i j k hij hjk).hom.app l r h).hom.app t =
      ((A.cut i j k hij hjk).hom.app l r h).hom.app (u.obj t) := by
  change 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l r h).hom.app (u.obj t) = _
  exact Category.id_comp _

lemma map₃_reindex_unit_app {q₁ q₂ q₃ n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Diagram (Diagram (Strings W m) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) (i : (Fin (q₃+1)))
    (j k : (Fin (q₂+1))) (h : j ≤ k) (l r : (Fin (q₁+1))) (hlr : l ≤ r) (t : Fin (n+1)) :
    (((((Diagram.map (I:=(Fin (q₃+1))) (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u)))).obj A).unit i).hom.app j k h).app l r hlr).hom.app t =
      (((A.unit i).hom.app j k h).app l r hlr).hom.app (u.obj t) := by
  change ((((Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u))).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u)))).app j k h).app l r hlr).hom.app t = _
  erw [comp_app, map_η_app (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u))]
  erw [map_η_app (I:=(Fin (q₁+1))) (reindex W u)]
  change (((A.unit i).hom.app j k h).app l r hlr).hom.app (u.obj t) ≫ 𝟙 _ = _
  exact Category.comp_id _

lemma map₃_reindex_cut_app {q₁ q₂ q₃ n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Diagram (Diagram (Strings W m) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) (i j k : (Fin (q₃+1)))
    (hij : i ≤ j) (hjk : j ≤ k) (l r : (Fin (q₂+1))) (h : l ≤ r)
    (v w : (Fin (q₁+1))) (hvw : v ≤ w) (t : Fin (n+1)) :
    (((((Diagram.map (I:=(Fin (q₃+1))) (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u)))).obj A).cut i j k hij hjk).hom.app l r h).app v w hvw).hom.app t =
      (((A.cut i j k hij hjk).hom.app l r h).app v w hvw).hom.app (u.obj t) := by
  change 𝟙 _ ≫ (((A.cut i j k hij hjk).hom.app l r h).app v w hvw).hom.app (u.obj t) = _
  exact Category.id_comp _

lemma map₃_reindex_comp_cut_app (q₁ q₂ q₃ : ℕ) {n m k : ℕ}
    (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1))
    (A : Diagram (Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1)))
    (i j z : Fin (q₃+1)) (hij : i ≤ j) (hjz : j ≤ z)
    (l r : Fin (q₂+1)) (h : l ≤ r)
    (first last : Fin (q₁+1)) (ordered : first ≤ last) (t : Fin (n+1)) :
    (((((Diagram.map (I:=Fin (q₃+1)) (Diagram.map (I:=Fin (q₂+1))
        (Diagram.map (I:=Fin (q₁+1)) (reindex W (u ⋙ v))))).obj A).cut i j z hij hjz).hom.app l r h).app first last ordered).hom.app t =
    (((((Diagram.map (I:=Fin (q₃+1)) (Diagram.map (I:=Fin (q₂+1))
        (Diagram.map (I:=Fin (q₁+1)) (reindex W u)))).obj
          ((Diagram.map (I:=Fin (q₃+1)) (Diagram.map (I:=Fin (q₂+1))
            (Diagram.map (I:=Fin (q₁+1)) (reindex W v)))).obj A)).cut i j z hij hjz).hom.app l r h).app first last ordered).hom.app t := by
  exact (map₃_reindex_cut_app (q₁:=q₁) (q₂:=q₂) (q₃:=q₃) W (u ⋙ v) A
    i j z hij hjz l r h first last ordered t).trans
    ((map₃_reindex_cut_app (q₁:=q₁) (q₂:=q₂) (q₃:=q₃) W u
      ((Diagram.map (I:=Fin (q₃+1)) (Diagram.map (I:=Fin (q₂+1))
        (Diagram.map (I:=Fin (q₁+1)) (reindex W v)))).obj A)
      i j z hij hjz l r h first last ordered t).trans
      (map₃_reindex_cut_app (q₁:=q₁) (q₂:=q₂) (q₃:=q₃) W v A
        i j z hij hjz l r h first last ordered (u.obj t))).symm

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedTripleDegree
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
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
noncomputable abbrev property₂ (p q:ℕ) := diagramProperty (diagramProperty W (Fin (p+1))) (Fin (q+1))
noncomputable abbrev property₃ (p q r:ℕ) := diagramProperty (property₂ W p q) (Fin (r+1))
noncomputable abbrev pos₃ (p q r:ℕ) := PosDiagrams (property₂ W p q) (Fin (r+1))
noncomputable def tripleTranspose (p q r n:ℕ) :
    Diagram (Diagram (Diagram (Strings W n) (Fin (p+1))) (Fin (q+1))) (Fin (r+1)) ⥤
      Strings (property₃ W p q r) n :=
  Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (transposeDiagram (I:=Fin (p+1)) W n)) ⋙
    Diagram.map (I:=Fin (r+1)) (transposeDiagram (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) n) ⋙
      transposeDiagram (I:=Fin (r+1)) (property₂ W p q) n
noncomputable instance tripleTransposeEquivalence (p q r n:ℕ) :
    (tripleTranspose W p q r n).IsEquivalence := by unfold tripleTranspose; infer_instance

noncomputable def triplePosInclusion (p q r:ℕ) : pos₃ W p q r ⥤
    Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1)) :=
  posDiagramInclusion (property₂ W p q) (Fin (r+1)) ⋙
    Diagram.map (I:=Fin (r+1)) (posDiagramInclusion (diagramProperty W (Fin (p+1))) (Fin (q+1))) ⋙
      Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (posDiagramInclusion W (Fin (p+1))))
noncomputable instance triplePosInclusionEquivalence (p q r:ℕ) :
    (triplePosInclusion W p q r).IsEquivalence := by unfold triplePosInclusion; infer_instance

noncomputable def triplePosHomologyIso (p q r j:ℕ) :
    (nerve (pos₃ W p q r)).homology DiagonalResolution.Z j ≅
      (nerve (Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1)))).homology DiagonalResolution.Z j :=
  NerveHomotopy.homologyIso (triplePosInclusion W p q r).asEquivalence DiagonalResolution.Z j

noncomputable def tripleRestrictedHomologyIso (p q r j:ℕ) :
    (SimplicialDiagonal.nerveDiagonal.obj (horizontal (property₃ W p q r))).homology DiagonalResolution.Z j ≅
      (nerve (Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1)))).homology DiagonalResolution.Z j :=
  homologyIso (property₃ W p q r) j ≪≫ triplePosHomologyIso W p q r j
end RestrictedNerve

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_MonoidalCongruence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
noncomputable abbrev transposeReindexLeft {p q:SimplexCategoryᵒᵖ} (f:p⟶q) := (Diagram.map (I:=I) (reindex W f.unop.toOrderHom.toFunctor) ⋙ transposeDiagram W q.unop.len)
noncomputable abbrev transposeReindexRight {p q:SimplexCategoryᵒᵖ} (f:p⟶q) := (transposeDiagram (I:=I) W p.unop.len ⋙ reindex (diagramProperty W I) f.unop.toOrderHom.toFunctor)
lemma transpose_comp_app {n : ℕ}
    {A B D : Strings (diagramProperty W I) n} (f : A ⟶ B) (g : B ⟶ D)
    (t : Fin (n+1)) (i j : I) (h : i ≤ j) :
    ((f ≫ g).hom.app t).hom.app i j h =
      (f.hom.app t).hom.app i j h ≫ (g.hom.app t).hom.app i j h := rfl
lemma transpose_tensor_app {n : ℕ}
    {A B D E : Strings (diagramProperty W I) n} (f : A ⟶ B) (g : D ⟶ E)
    (t : Fin (n+1)) (i j : I) (h : i ≤ j) :
    ((f ⊗ₘ g).hom.app t).hom.app i j h =
      (f.hom.app t).hom.app i j h ⊗ₘ (g.hom.app t).hom.app i j h := by
  change ((f.hom.app t ⊗ₘ g.hom.app t).hom.app i j h) = _
  exact posTensor_app W I (f.hom.app t) (g.hom.app t) i j h
lemma transposeReindexLeft_μ_app {p q:SimplexCategoryᵒᵖ} (f:p⟶q)
    (A B:Diagram (Strings W p.unop.len) I)
    (t:Fin (q.unop.len+1)) (i j:I) (h:i≤j) :
    ((Functor.LaxMonoidal.μ (transposeReindexLeft (I:=I) W f) A B).hom.app t).hom.app i j h =
      𝟙 ((A.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t) ⊗
        (B.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t)) := by
  change (𝟙 _) ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _
end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedFunctorial
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.triplePosInclusionEquivalence _root_.OAI.RestrictedNerve.tripleTransposeEquivalence _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

lemma posReindex_inclusion (u:I→oJ) :
    posReindex W u ⋙ posDiagramInclusion W I =
      posDiagramInclusion W J ⋙ Diagram.reindex u := by
  refine CategoryTheory.Functor.ext (fun A=>rfl) ?_
  intro A B f
  erw [Category.id_comp, Category.comp_id]
  rfl
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_NestedPosReindex
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
noncomputable def nestedPosReindex (u:I→oJ) :
    PosDiagrams (diagramProperty W J) K ⥤ PosDiagrams (diagramProperty W I) K where
  obj A := (Diagram.map (I:=K) (widePosReindex W u)).obj A
  map {A B} f := InducedCategory.homMk {
    app i j h := (posReindex W u).map (f.hom.app i j h)
    unit i := by
      apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
      have he := congrArg (fun z => z.hom.app (u x) (u y) (u.monotone h)) (f.hom.unit i)
      change (f.hom.app i i (le_refl i)).hom.app (u x) (u y) (u.monotone h) ≫
          ((B.unit i).hom.hom.hom.app (u x) (u y) (u.monotone h) ≫ 𝟙 _) =
        (A.unit i).hom.hom.hom.app (u x) (u y) (u.monotone h) ≫ 𝟙 _ at he
      change (f.hom.app i i (le_refl i)).hom.app (u x) (u y) (u.monotone h) ≫
          (((B.unit i).hom.hom.hom.app (u x) (u y) (u.monotone h) ≫ 𝟙 _) ≫ 𝟙 _) =
        ((A.unit i).hom.hom.hom.app (u x) (u y) (u.monotone h) ≫ 𝟙 _) ≫ 𝟙 _
      simpa only [Category.comp_id] using he
    cut i j k hij hjk := by
      apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
      have he := congrArg (fun z => z.hom.app (u x) (u y) (u.monotone h)) (f.hom.cut i j k hij hjk)
      change ((f.hom.app i j hij ⊗ₘ f.hom.app j k hjk).hom.app (u x) (u y) (u.monotone h)) ≫
          (𝟙 _ ≫ (B.cut i j k hij hjk).hom.hom.hom.app (u x) (u y) (u.monotone h)) =
        (𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.hom.app (u x) (u y) (u.monotone h)) ≫
          (f.hom.app i k (le_trans hij hjk)).hom.app (u x) (u y) (u.monotone h) at he
      erw [posTensor_app] at he
      change (((posReindex W u).map (f.hom.app i j hij) ⊗ₘ
          (posReindex W u).map (f.hom.app j k hjk)).hom.app x y h) ≫
          (𝟙 _ ≫ 𝟙 _ ≫ (B.cut i j k hij hjk).hom.hom.hom.app (u x) (u y) (u.monotone h)) =
        (𝟙 _ ≫ 𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.hom.app (u x) (u y) (u.monotone h)) ≫
          (f.hom.app i k (le_trans hij hjk)).hom.app (u x) (u y) (u.monotone h)
      erw [posTensor_app]
      simpa only [posReindex, Category.id_comp] using! he }
  map_id A := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (posReindex W u).map_id _
  map_comp f g := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (posReindex W u).map_comp _ _
lemma nestedPosReindex_property (u:I→oJ) {A B:PosDiagrams (diagramProperty W J) K} (f:A⟶B)
    (hf:diagramProperty (diagramProperty W J) K f) :
    diagramProperty (diagramProperty W I) K ((nestedPosReindex W u).map f) :=
  fun i j h => posReindex_property W u (f.hom.app i j h) (hf i j h)
lemma nestedPosReindex_inclusion_obj (u:I→oJ) (A:PosDiagrams (diagramProperty W J) K) :
    (nestedPosReindex (K:=K) W u ⋙ posDiagramInclusion (diagramProperty W I) K).obj A =
      (posDiagramInclusion (diagramProperty W J) K ⋙ Diagram.map (posReindex W u)).obj A := by
  refine ext_heq rfl ?_ ?_
  · apply heq_of_eq; funext i; apply Iso.ext
    apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
    simp [nestedPosReindex,diagramInclusion,mapObj]
    simp [posReindex,widePosReindex]
    rfl
  · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext
    apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
    simp [nestedPosReindex,diagramInclusion,mapObj]
    simp [posReindex,widePosReindex]
    rfl

lemma nestedPosReindex_inclusion (u:I→oJ) :
    nestedPosReindex (K:=K) W u ⋙ posDiagramInclusion (diagramProperty W I) K =
      posDiagramInclusion (diagramProperty W J) K ⋙ Diagram.map (posReindex W u) := by
  refine CategoryTheory.Functor.ext (nestedPosReindex_inclusion_obj W u) ?_
  intro A B f
  apply Hom.ext; intro i j h
  apply InducedCategory.hom_ext; apply Hom.ext; intro x y hxy
  simp [nestedPosReindex,posReindex,Diagram.map]
  erw [Diagram.eqToHom_app, Diagram.eqToHom_app]
  erw [comp_app, comp_app, eqToHom_pos_app, eqToHom_pos_app]
  change (f.hom.app i j h).hom.app (u x) (u y) (u.monotone hxy) =
    𝟙 _ ≫ (f.hom.app i j h).hom.app (u x) (u y) (u.monotone hxy) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

lemma nested_comp_app {A B D:PosDiagrams (diagramProperty W I) K}
    (f:A⟶B) (g:B⟶D) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y) :
    ((f ≫ g).hom.app i j h).hom.app x y hxy =
      (f.hom.app i j h).hom.app x y hxy ≫ (g.hom.app i j h).hom.app x y hxy := rfl

lemma nested_eqToHom_app {A B:PosDiagrams (diagramProperty W I) K}
    (e:A=B) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y) :
    ((eqToHom e).hom.app i j h).hom.app x y hxy =
      eqToHom (congrArg (fun A:PosDiagrams (diagramProperty W I) K =>
        ((diagramInclusion W I).obj (A.obj i j h).obj).obj x y hxy) e) := by
  cases e
  rfl

lemma twiceTransposed_comp_app {n:ℕ}
    {A B D:Strings (diagramProperty (diagramProperty W I) K) n}
    (f:A⟶B) (g:B⟶D) (t:Fin (n+1)) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y) :
    (((f ≫ g).hom.app t).hom.app i j h).hom.app x y hxy =
      ((f.hom.app t).hom.app i j h).hom.app x y hxy ≫
        ((g.hom.app t).hom.app i j h).hom.app x y hxy := rfl

lemma twiceTransposed_eqToHom_app {n:ℕ}
    {A B:Strings (diagramProperty (diagramProperty W I) K) n}
    (e:A=B) (t:Fin (n+1)) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y) :
    (((eqToHom e).hom.app t).hom.app i j h).hom.app x y hxy =
      eqToHom (congrArg (fun A:Strings (diagramProperty (diagramProperty W I) K) n =>
        (((A.obj.obj t).obj i j h).obj.obj x y hxy).obj) e) := by
  cases e
  rfl

lemma twiceTransposed_transport_ext {n:ℕ}
    {A A' B B':Strings (diagramProperty (diagramProperty W I) K) n}
    (eA:A=A') (eB:B'=B) (f:A⟶B) (g:A'⟶B')
    (hf:∀ (t:Fin (n+1)) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y),
      ((f.hom.app t).hom.app i j h).hom.app x y hxy =
        eqToHom (congrArg (fun A:Strings (diagramProperty (diagramProperty W I) K) n =>
          (((A.obj.obj t).obj i j h).obj.obj x y hxy).obj) eA) ≫
        ((g.hom.app t).hom.app i j h).hom.app x y hxy ≫
        eqToHom (congrArg (fun A:Strings (diagramProperty (diagramProperty W I) K) n =>
          (((A.obj.obj t).obj i j h).obj.obj x y hxy).obj) eB)) :
    f = eqToHom eA ≫ g ≫ eqToHom eB := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  apply InducedCategory.hom_ext; apply Hom.ext; intro x y hxy
  erw [twiceTransposed_comp_app, twiceTransposed_comp_app,
    twiceTransposed_eqToHom_app, twiceTransposed_eqToHom_app]
  exact hf t i j h x y hxy

end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PositionalInclusionMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
noncomputable instance posReindex_inclusion_monoidal (u:I→oJ) :
    NatTrans.IsMonoidal (eqToHom (posReindex_inclusion W u)) where
  unit := by
    apply Hom.ext; intro i j h
    simp only [CategoryTheory.eqToHom_app]
    simp only [Functor.LaxMonoidal.comp_ε,posInclusion_ε,posReindex_ε,IntervalBar.Diagram.reindex_ε]
    simp [posReindex,diagramInclusion,Diagram.reindex,mapεHom]
    erw [Diagram.eqToHom_app]
    change (𝟙 (𝟙_ C) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
  tensor A B := by
    apply Hom.ext; intro i j h
    simp only [CategoryTheory.eqToHom_app]
    simp only [Functor.LaxMonoidal.comp_μ,posInclusion_μ,posReindex_μ,IntervalBar.Diagram.reindex_μ]
    simp [posReindex,diagramInclusion,Diagram.reindex,mapμHom]
    erw [Diagram.eqToHom_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    change (𝟙 ((A.obj (u i) (u j) (u.monotone h)).obj ⊗
      (B.obj (u i) (u j) (u.monotone h)).obj) ≫ 𝟙 _) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [id_tensorHom_id, Category.comp_id]
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]

lemma triplePosInclusion_outerReindex (p q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    posReindex (property₂ W p q) u ⋙ triplePosInclusion W p q r =
      triplePosInclusion W p q s ⋙ Diagram.reindex u := by
  unfold triplePosInclusion
  rw [←Functor.assoc,←Functor.assoc,posReindex_inclusion]
  simp only [Functor.assoc]
  rw [←Functor.assoc (Diagram.reindex u),Diagram.reindex_map]
  simp only [Functor.assoc]
  rw [Diagram.reindex_map]
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StringEvaluation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory

section
open IntervalBar IntervalBar.Diagram

section
variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C) [W.IsMultiplicative]
noncomputable def stringEvaluation {n:ℕ} (t:Fin (n+1)) : Strings W n ⥤ C where
  obj A := A.obj.obj t
  map f := f.hom.app t
  map_id _ := rfl
  map_comp _ _ := rfl
@[simp] lemma stringEvaluation_obj {n:ℕ} (t:Fin (n+1)) (A:Strings W n) :
    (stringEvaluation W t).obj A=A.obj.obj t := rfl
@[simp] lemma stringEvaluation_map {n:ℕ} (t:Fin (n+1)) {A B:Strings W n} (f:A⟶B) :
    (stringEvaluation W t).map f=f.hom.app t := rfl
end

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable instance stringEvaluationMonoidal {n:ℕ} (t:Fin (n+1)) :
    (stringEvaluation W t).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left := by intros; simp
  μIso_hom_natural_right := by intros; simp
  associativity := by intros; simp
  left_unitality := by intros; simp
  right_unitality := by intros; simp }
noncomputable instance stringEvaluationBraided {n:ℕ} (t:Fin (n+1)) :
    (stringEvaluation W t).Braided where
  braided _ _ := by
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
omit [Fact W.StableUnderInverse] in
@[simp] lemma stringEvaluation_η {n:ℕ} (t:Fin (n+1)) :
    Functor.OplaxMonoidal.η (stringEvaluation W t)=𝟙 _ := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma stringEvaluation_ε {n:ℕ} (t:Fin (n+1)) :
    Functor.LaxMonoidal.ε (stringEvaluation W t)=𝟙 _ := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma stringEvaluation_μ {n:ℕ} (t:Fin (n+1)) (A B:Strings W n) :
    Functor.LaxMonoidal.μ (stringEvaluation W t) A B=𝟙 _ := rfl
variable {I:Type} [Preorder I]
lemma transpose_evaluation {n:ℕ} (t:Fin (n+1)) :
    transposeDiagram (I:=I) W n ⋙ stringEvaluation (diagramProperty W I) t ⋙
      posDiagramInclusion W I = Diagram.map (stringEvaluation W t) := by
  refine CategoryTheory.Functor.ext (fun _=>?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i; apply Iso.ext
      simp [transposeDiagram,transposeDiagramObj,stringVertex,mapObj,diagramInclusion]
      rfl
    · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext
      simp [transposeDiagram,transposeDiagramObj,stringVertex,mapObj,diagramInclusion]
      rfl
  · intro A B f
    apply Hom.ext; intro i j h
    simp [transposeDiagram,transposeDiagramHom,Diagram.map]
    erw [Diagram.eqToHom_app, Diagram.eqToHom_app]
    change (f.app i j h).hom.app t = 𝟙 _ ≫ (f.app i j h).hom.app t ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
end

section
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
omit [Fact W.StableUnderInverse] in
@[simp] lemma restrictionInclusion_ε : Functor.LaxMonoidal.ε (inclusion W)=𝟙 _ := rfl
variable {I:Type} [Preorder I]
noncomputable instance transpose_evaluation_monoidal {n:ℕ} (t:Fin (n+1)) :
    NatTrans.IsMonoidal (eqToHom (transpose_evaluation (I:=I) W t)) where
  unit := by
    apply Hom.ext; intro i j h
    simp only [Functor.LaxMonoidal.comp_ε,posInclusion_ε,stringEvaluation_ε,
      IntervalBar.Diagram.map_ε,transpose_ε]
    simp [transposeε, mapεHom,diagramInclusion]
    erw [Diagram.eqToHom_app]
    change (𝟙 (𝟙_ C) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
    simp only [Category.comp_id]
  tensor A B := by
    apply Hom.ext; intro i j h
    simp only [Functor.LaxMonoidal.comp_μ,posInclusion_μ,stringEvaluation_μ,
      IntervalBar.Diagram.map_μ,transpose_μ]
    simp [transposeμ,mapμHom,diagramInclusion]
    erw [Diagram.eqToHom_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    change (𝟙 ((A.obj i j h).obj.obj t ⊗ (B.obj i j h).obj.obj t) ≫ 𝟙 _) ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
    simp only [id_tensorHom_id, Category.comp_id]
end

open IntervalBar IntervalBar.Diagram

end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_Supplemental
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
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
noncomputable def innerNerveRows (q r:ℕ) : SimplicialObject SSet where
  obj p := nerve (Diagram (Diagram (Diagram C (Fin (p.unop.len+1))) (Fin (q+1))) (Fin (r+1)))
  map f := nerveMap (Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)))
  map_id p := by
    change nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
      (Diagram.reindex (C:=C) (OrderHom.id (α:=Fin (p.unop.len+1))))))=𝟙 _
    rw [Diagram.map_map_reindex_id]
    rfl
  map_comp f g := by
    change nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
      (Diagram.reindex (C:=C) (f.unop.toOrderHom.comp g.unop.toOrderHom)))) = _
    rw [Diagram.map_map_reindex_comp]
    rfl

noncomputable def innerNerveRowsMiddle (r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    innerNerveRows (C:=C) s r ⟶ innerNerveRows (C:=C) q r where
  app p := nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram C (Fin (p.unop.len+1))) u))
  naturality n m f := by
    change nerveMap (Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)) ⋙
      Diagram.map (Diagram.reindex u)) = nerveMap (Diagram.map (Diagram.reindex u) ⋙
      Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)))
    rw [Diagram.map_map_reindex]

lemma innerNerveRowsMiddle_id (q r:ℕ) :
    innerNerveRowsMiddle (C:=C) r (OrderHom.id (α:=Fin (q+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext p
  change nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram C (Fin (p.unop.len+1)))
    (OrderHom.id (α:=Fin (q+1))))) = _
  rw [Diagram.map_reindex_id]
  rfl
lemma innerNerveRowsMiddle_comp (r:ℕ) {p q s:ℕ}
    (u:Fin (p+1)→oFin (q+1)) (v:Fin (q+1)→oFin (s+1)) :
    innerNerveRowsMiddle (C:=C) r (v.comp u) =
      innerNerveRowsMiddle (C:=C) r v ≫ innerNerveRowsMiddle (C:=C) r u := by
  apply NatTrans.ext; funext n
  change nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram C (Fin (n.unop.len+1)))
    (v.comp u))) = _
  rw [Diagram.map_reindex_comp]
  rfl
noncomputable def middleNerveRows (r:ℕ) : SimplicialObject SSet where
  obj q := SimplicialDiagonal.diagonal.obj (innerNerveRows (C:=C) q.unop.len r)
  map f := SimplicialDiagonal.diagonal.map (innerNerveRowsMiddle (C:=C) r f.unop.toOrderHom)
  map_id q := by
    change SimplicialDiagonal.diagonal.map (innerNerveRowsMiddle (C:=C) r (OrderHom.id (α:=Fin (q.unop.len+1)))) = _
    rw [innerNerveRowsMiddle_id,CategoryTheory.Functor.map_id]
  map_comp f g := by
    change SimplicialDiagonal.diagonal.map (innerNerveRowsMiddle (C:=C) r (f.unop.toOrderHom.comp g.unop.toOrderHom)) = _
    rw [innerNerveRowsMiddle_comp,Functor.map_comp]
noncomputable def innerNerveRowsOuter (q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    innerNerveRows (C:=C) q s ⟶ innerNerveRows (C:=C) q r where
  app p := nerveMap (Diagram.reindex (C:=Diagram (Diagram C (Fin (p.unop.len+1))) (Fin (q+1))) u)
  naturality n m f := by
    change nerveMap (Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)) ⋙
      Diagram.reindex u) = nerveMap (Diagram.reindex u ⋙
      Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)))
    rw [Diagram.reindex_map]
lemma innerNerveRowsMiddleOuter_commute {q s r t:ℕ}
    (u:Fin (q+1)→oFin (s+1)) (v:Fin (r+1)→oFin (t+1)) :
    innerNerveRowsMiddle (C:=C) t u ≫ innerNerveRowsOuter (C:=C) q v =
      innerNerveRowsOuter (C:=C) s v ≫ innerNerveRowsMiddle (C:=C) r u := by
  apply NatTrans.ext; funext p
  change nerveMap (Diagram.map (Diagram.reindex u) ⋙ Diagram.reindex v) =
    nerveMap (Diagram.reindex v ⋙ Diagram.map (Diagram.reindex u))
  rw [Diagram.reindex_map]
noncomputable def middleNerveRowsOuter {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    middleNerveRows (C:=C) s ⟶ middleNerveRows (C:=C) r where
  app q := SimplicialDiagonal.diagonal.map (innerNerveRowsOuter (C:=C) q.unop.len u)
  naturality n m f := by
    change SimplicialDiagonal.diagonal.map (innerNerveRowsMiddle (C:=C) s f.unop.toOrderHom) ≫
      SimplicialDiagonal.diagonal.map (innerNerveRowsOuter (C:=C) m.unop.len u) = _
    rw [←Functor.map_comp,innerNerveRowsMiddleOuter_commute,Functor.map_comp]
    rfl
lemma innerNerveRowsOuter_id (q r:ℕ) :
    innerNerveRowsOuter (C:=C) q (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext p
  change nerveMap (Diagram.reindex (C:=Diagram (Diagram C (Fin (p.unop.len+1))) (Fin (q+1)))
    (OrderHom.id (α:=Fin (r+1)))) = _
  rw [Diagram.reindex_id]
  rfl
lemma innerNerveRowsOuter_comp (q:ℕ) {p r s:ℕ}
    (u:Fin (p+1)→oFin (r+1)) (v:Fin (r+1)→oFin (s+1)) :
    innerNerveRowsOuter (C:=C) q (v.comp u) =
      innerNerveRowsOuter (C:=C) q v ≫ innerNerveRowsOuter (C:=C) q u := by
  apply NatTrans.ext; funext n
  change nerveMap (Diagram.reindex (C:=Diagram (Diagram C (Fin (n.unop.len+1))) (Fin (q+1)))
    (v.comp u)) = _
  rw [Diagram.reindex_comp]
  rfl
lemma middleNerveRowsOuter_id (r:ℕ) :
    middleNerveRowsOuter (C:=C) (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerNerveRowsOuter (C:=C) q.unop.len (OrderHom.id (α:=Fin (r+1)))) = _
  rw [innerNerveRowsOuter_id,CategoryTheory.Functor.map_id]
  rfl
lemma middleNerveRowsOuter_comp {p r s:ℕ}
    (u:Fin (p+1)→oFin (r+1)) (v:Fin (r+1)→oFin (s+1)) :
    middleNerveRowsOuter (C:=C) (v.comp u) =
      middleNerveRowsOuter (C:=C) v ≫ middleNerveRowsOuter (C:=C) u := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerNerveRowsOuter (C:=C) q.unop.len (v.comp u)) = _
  rw [innerNerveRowsOuter_comp,Functor.map_comp]
  rfl
noncomputable def outerNerveRows : SimplicialObject SSet where
  obj r := SimplicialDiagonal.diagonal.obj (middleNerveRows (C:=C) r.unop.len)
  map f := SimplicialDiagonal.diagonal.map (middleNerveRowsOuter (C:=C) f.unop.toOrderHom)
  map_id r := by
    change SimplicialDiagonal.diagonal.map (middleNerveRowsOuter (C:=C) (OrderHom.id (α:=Fin (r.unop.len+1)))) = _
    rw [middleNerveRowsOuter_id,CategoryTheory.Functor.map_id]
  map_comp f g := by
    change SimplicialDiagonal.diagonal.map (middleNerveRowsOuter (C:=C) (f.unop.toOrderHom.comp g.unop.toOrderHom)) = _
    rw [middleNerveRowsOuter_comp,Functor.map_comp]
end

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma reverseDiagonalReindex {I J:Type} [Preorder I] [Preorder J] (u:I→oJ) :
    Diagram.reindex (C:=Diagram (Diagram C J) J) u ⋙
      Diagram.map (I:=I) (Diagram.reindex (C:=Diagram C J) u) ⋙
      Diagram.map (I:=I) (Diagram.map (I:=I) (Diagram.reindex (C:=C) u)) =
        diagonalReindex (C:=C) u := by
  unfold diagonalReindex
  rw [←Functor.assoc,Diagram.reindex_map,Functor.assoc]
  rw [Diagram.reindex_map]
  rw [←Functor.assoc,←Diagram.map_map_reindex,Functor.assoc]
noncomputable def totalNerveBarIso :
    SimplicialDiagonal.diagonal.obj (outerNerveRows (C:=C)) ≅ bar₃ (C:=C) :=
  NatIso.ofComponents (fun _=>Iso.refl _) (by
    intro n m f
    ext x
    exact congrArg (fun F => f.unop.toOrderHom.toFunctor ⋙ x ⋙ F)
      (reverseDiagonalReindex (C:=C) f.unop.toOrderHom))
end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end



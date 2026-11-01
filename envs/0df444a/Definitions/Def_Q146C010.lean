-- Prove2me | Definitions.Def_Q146C010
-- name    : Q146C010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:22:02.159161+00:00
-- url     : https://prove2.me/theorems/4c42230d-8949-476d-afff-e96362c03974
-- title:
--   Definitions bundle Q146C010 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 239 declarations of OpenAI's Lean: 45 definitions, 7 inductive types or structures and 187 theorems. The definitions and types are `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask`, `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRoundDisks.traceInterval`, `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRoundDisks.traceScalarCenter`, `OAI.CircleDomainRigidity.MatchedConformalEnds.realMaskValue`, `OAI.CircleDomainRigidity.MatchedConformalEnds.realSelectedScalar`, `OAI.CircleDomainRigidity.MatchedConformalEnds.selectedPlane`, `OAI.CircleDomainRigidity.MatchedConformalEnds.selectedTarget`, `OAI.CircleDomainRigidity.OrderedCollarLift`, `OAI.CircleDomainRigidity.OrderedCollarLift.circuit`, `OAI.CircleDomainRigidity.PhysicalRealCoordinate.continuousTest`, `OAI.CircleDomainRigidity.RecursiveMeanOutput`, `OAI.CircleDomainRigidity.RetainedRealCircleModel`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.HoleFilling`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.HoleFilling.filled`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.ScalarWeakLimit`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.ScalarWeakLimit.boundedRepresentative`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.ScalarWeakLimit.continuedScalar_witness`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.ScalarWeakLimit.planarWeakGradient`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.compactScalarCircleModel`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.continuedScalar`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.imageScalar`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.projectedPlaneFunction`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.select`, `OAI.CircleDomainRigidity.RetainedRealCircleModel.transferred`, `OAI.CircleDomainRigidity.SelectableMaskedCoordinate.CompatibleWith`, `OAI.CircleDomainRigidity.SelectableMaskedCoordinate.pathData`, `OAI.CircleDomainRigidity.SelectableMaskedCoordinate.priorLevels`, `OAI.CircleDomainRigidity.SelectedLevelPresentation.rebase`, `OAI.CircleDomainRigidity.SelectedMixedModels`, `OAI.CircleDomainRigidity.SelectedMixedModels.realCoordinates`, `OAI.CircleDomainRigidity.SelectedMixedModels.withRadius`, `OAI.CircleDomainRigidity.SmoothRegularJordanCollars`, `OAI.CircleDomainRigidity.UngatedRealTest.levelPresentation`, `OAI.CircleDomainRigidity.UngatedRealTest.of_barrier`, `OAI.CircleDomainRigidity.UngatedRealTest.openEnds`, `OAI.CircleDomainRigidity.compactArcStartingAngleLaw`, `OAI.CircleDomainRigidity.finiteScalarSeedTests`, `OAI.CircleDomainRigidity.finiteSeededRealFamily`, `OAI.CircleDomainRigidity.liftedMeanGeometricIndex`, `OAI.CircleDomainRigidity.maskedLevelData` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `AccessibleJoin`, `BoundaryContinuity2`, `CircleDomains_Modulus_FilledScalarNormBounds`, `CircleDomains_Modulus_RealBarrierTests`, `CircleDomains_Rigidity_ExactTraceFamily`, `CircleDomains_Rigidity_FiniteMatchedField`, `CircleDomains_Rigidity_MaskedLevelData`, `CircleDomains_Rigidity_MatchedRealMaskData`, `CircleDomains_Rigidity_MatchedScalarIntervals`, `CircleDomains_Rigidity_OrderedMaskedSelection`, `CircleDomains_Rigidity_ProjectedZeroTrace`, `CircleDomains_Rigidity_SeededMaskedSelection`, `CircleDomains_Rigidity_SelectableMaskedCoordinate`, `CircleDomains_Rigidity_ZeroTraceConformalTransport`, `CircleDomains_Selection_ActualScalarJump`, `CircleDomains_Selection_ActualVerticalScalarJump`, `CircleDomains_Selection_ContinuousScalarRepresentative`, `CircleDomains_Selection_CountableUncoveredTestEnds`, `CircleDomains_Selection_FiniteSeededRealFamily`, `CircleDomains_Selection_GeometricIndexLocal`, `CircleDomains_Selection_LiftedMeanContinuity`, `CircleDomains_Selection_PrescribedScalarSeed`, `CircleDomains_Selection_PresentedRealCoordinates`, `CircleDomains_Selection_RealSeedPresentation`, `CircleDomains_Selection_RealTestLevelData`, `CircleDomains_Selection_RebasedLevelPresentations`, `CircleDomains_Selection_RecursiveMeanExclusion`, `CircleDomains_Selection_ScalarBoundedRepresentative`, `CircleDomains_Selection_ScalarEndIdentification`, `CircleDomains_Selection_ScalarLocalizedRange`, `CircleDomains_Selection_ScalarRegionLowerRange`, `CircleDomains_Selection_ScalarRegionRange`, `CircleDomains_Selection_ScalarTerminalRange`, `CircleDomains_Selection_SeededLevelPresentations`, `CircleDomains_Selection_SelectedMixedSmallness`, `CircleDomains_Sobolev_ClippedScalarEnergy`, `CircleDomains_Sobolev_ContinuousScalarSobolev`, `CircleDomains_Sobolev_EnergyTransportIntegrability`, `CircleDomains_Sobolev_FilledScalarEnergy`, `CircleDomains_Sobolev_FilledScalarGlobalEnergy`, `CircleDomains_Sobolev_FilledScalarL2`, `CircleDomains_Sobolev_FilledScalarSliceDerivative`, `CircleDomains_Sobolev_FilledScalarTestIntegrals`, `CircleDomains_Sobolev_NormalizedCircleEnergy`, `CircleDomains_Sobolev_RetainedSobolevContinuations`, `CircleDomains_Sobolev_ScalarContinuationEnergy`, `CircleDomains_Sobolev_ScalarEnergySaturation`, `CircleDomains_Sobolev_ScalarImageEnergy`, `CircleDomains_Sobolev_ScalarImageGradient`, `CircleDomains_Sobolev_ScalarLocalLp`, `CircleDomains_Sobolev_ScalarWeakEnergy`, `CircleDomains_Sobolev_ScalarWeakLimits`, `CircleDomains_Sobolev_SmoothImageScalar`, `CircleDomains_Sobolev_SmoothPlaneEnergyTransport`, `CircleDomains_Sobolev_SobolevConformalTransport`, `CircleDomains_Sobolev_SphereCircleEnergy`, `CircleDomains_Sobolev_TransportedRealEnergy`, `CircleDomains_Sobolev_VerticalFilledDerivative`, `CircleDomains_Topology_ClosedComponentCorrespondence`, `CircleDomains_Topology_CompactScalarCircleModel`, `CircleDomains_Topology_CompactScalarContinuation`, `CircleDomains_Topology_ComponentRelationSelection`, `CircleDomains_Topology_DiskRayTranslates`, `CircleDomains_Topology_MeanIndexBoundary`, `CircleDomains_Topology_OrderedCollarLift`, `CircleDomains_Topology_ProjectedPlaneFunction`, `CircleDomains_Topology_RegularJordanCollar`, `CircleDomains_Topology_RetainedCircleModel`, `CircleDomains_Topology_ScalarCircleModel`, `CircleDomains_Topology_TransportedCircleCoordinates`, `CircleDomains_Transfer_BoundedScalarFillings`, `CircleDomains_Transfer_PointDustModels`, `CircleDomains_Transfer_RealPresentationTransfer`, `CircleDomains_Transfer_RetainedOriginalTest`, `CircleDomains_Transfer_RetainedScalarEstimates`, `CircleDomains_Transfer_ScalarHoleFillings`, `CircleDomains_Transfer_ScalarImageIdentification`, `CircleDomains_Transfer_SelectedMixedModels`, `CircleDomains_Transfer_TransportedRealCoordinates`, `CircleDomains_Uniformization_ActualScalarJumpLimit`, `CircleDomains_Uniformization_ActualVerticalJumpLimit`, `CircleDomains_Uniformization_ScalarDistributionalLimit`, `CircleDomains_Uniformization_ScalarLimitWitness`, `CircleDomains_Uniformization_ScalarPointwiseLimit`, `GeneralCrosscut`, `GeneratedStructure`, `InitialPairFixed`, `Inversion`, `JordanClosed`, `LimitMap`, `PolyArcRealize`, `RefinementStars`, `SquareCycle`, `SquareMesh`, `SquareMover`.
--
--   **Imports.** It imports the published bundle `Def_KoebeCircleDomains`; the bundles `Q146C006`, `Q146C007` and `Q146C008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q146C011` and `Q146C012`; the statements `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs`, `OAI.CircleDomainRigidity.MatchedConformalEnds.normalized_identity_of_trace`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean`, `OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver`, `OAI.CircleDomainRigidity.countable_uncovered_test_endpoints`, `OAI.CircleDomainRigidity.countable_uncovered_test_endpoints_of_range`, `OAI.CircleDomainRigidity.exists_ordered_protrusion_test`, `OAI.CircleDomainRigidity.exists_signed_compact_scalar_circle_model`, `OAI.CircleDomainRigidity.koebeCircleDomainConjecture_of_constructed_quotient`, `OAI.CircleDomainRigidity.selected_limit_isCircleDomain` and `OAI.CircleDomainRigidity.smoothRegularJordanCollars`; the proofs of `OAI.CircleDomainRigidity.AppendingSequence.exists_tracked_global_weak_limit`, `OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests`, `OAI.CircleDomainRigidity.FiniteTransfer.exists_countable_mixed_stages`, `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs`, `OAI.CircleDomainRigidity.MatchedConformalEnds.normalized_identity_of_trace`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean`, `OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels`, `OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver`, `OAI.CircleDomainRigidity.countable_uncovered_test_endpoints`, `OAI.CircleDomainRigidity.countable_uncovered_test_endpoints_of_range`, `OAI.CircleDomainRigidity.exists_ordered_protrusion_test`, `OAI.CircleDomainRigidity.exists_signed_compact_scalar_circle_model`, `OAI.CircleDomainRigidity.exists_small_selected_height_data`, `OAI.CircleDomainRigidity.exists_smooth_mean_coordinate_with_small_budget`, `OAI.CircleDomainRigidity.koebeCircleDomainConjecture_of_constructed_quotient`, `OAI.CircleDomainRigidity.selected_limit_isCircleDomain` and `OAI.CircleDomainRigidity.smoothRegularJordanCollars`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C006
import Definitions.Def_Q146C007
import Definitions.Def_Q146C008

section
-- module Solutions.Q146_CD.AccessibleJoin
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Joining accessible boundary points

Two boundary points of a region that are each reachable by a polygonal arc from inside can be
joined by a *single* simple polygonal arc whose interior stays inside the region. This is
`lem:accessible-endpoints`, and the same extraction — applied to a finite polygonal skeleton
rather than to a pair of access arcs — is `lem:skeleton-crosscuts`.

## The predicate

`Schoenflies.PolyAccessible Ω a` says that `a` admits a *polygonal access arc* from `Ω`: a
vertex list starting at `a`, ending inside `Ω`, all of whose points other than `a` lie in `Ω`.

The definition deliberately does **not** ask the access arc to be simple. A consumer that has
only a self-crossing approach path can still supply the hypothesis, and nothing is lost: the
extraction below re-runs `lem:finite-polygonal-union` on the whole union anyway, so simplicity
of the input is never used. `PolyAccessible.exists_simple` recovers the blueprint's literal
phrasing (*a simple polygonal arc from `a` to a point of `Ω`*) for a point off `Ω`, so the two
readings agree where the blueprint uses them.

Note also that neither the definition nor the theorems below mention `frontier Ω`. The
blueprint states `lem:accessible-endpoints` for `a, b ∈ ∂Ω`, but boundary membership plays no
role in the proof — only `a ≠ b` does — so the statements here are the stronger ones with the
hypothesis dropped. A consumer holding `a, b ∈ ∂Ω` simply does not pass it.

## The method, and where the difficulty actually is

Take an access arc from `a` and one from `b`, join their far ends inside `Ω` by
`lem:polygonal-connected` (`Schoenflies.exists_poly_of_isPreconnected`), and extract a simple
arc from the resulting three-piece polygonal union by `lem:finite-polygonal-union`
(`Schoenflies.exists_simple_poly_of_union`).

The whole content is that the extraction must keep the two endpoints and must keep everything
else inside `Ω`. Both are free from the interface actually on `main`:
`Schoenflies.exists_simple_poly_of_union` already returns a vertex list whose `head` is `a` and
whose `getLast` is `b`, together with `IsArcBetween _ a b`, so the endpoints are pinned; and it
returns the arc as a *subset of the union it was extracted from*, so `poly ws \ {a, b} ⊆ Ω`
follows from the same inclusion for the union. No endpoint-pinning lemma had to be added.

What *was* missing is a version of the extraction indexed by an arbitrary finite family rather
than by a `List (Set Plane)`: a skeleton arrives as a finite set of edges, and turning it into a
list at the call site is noise. `Schoenflies.exists_simple_poly_of_biUnion_finite` is that
version and belongs beside `Schoenflies.exists_simple_poly_of_union` in
`Schoenflies/SimpleArc.lean`.

## Blueprint

* `Schoenflies.PolyAccessible` — "admitting a polygonal access arc from `Ω`", the hypothesis of
  `lem:accessible-endpoints`.
* `Schoenflies.PolyAccessible.of_openSegment`, `Schoenflies.StronglyAccessible.polyAccessible`,
  `Schoenflies.polyAccessible_of_poly`, `Schoenflies.polyAccessible_of_poly'` — the ways the
  construction produces the hypothesis: a straight access segment, Definition 8.1 (strong
  accessibility), and a chain already known to run into `Ω` from either of its ends.
* `Schoenflies.PolyAccessible.exists_simple` — the blueprint's literal reading of the
  hypothesis, for a point off `Ω`.
* `Schoenflies.exists_simple_poly_of_biUnion_finite`,
  `Schoenflies.exists_simple_arc_of_biUnion_finite`, `Schoenflies.exists_simple_poly_pinned`,
  `Schoenflies.exists_simple_poly_of_isPolygonal_pinned` — `lem:finite-polygonal-union` over a
  finite family, and with the "off the endpoints, stay in the region" clause attached. These
  four belong in `Schoenflies/SimpleArc.lean`.
* `Graph.pointSet_eq_biUnion`, `Graph.exists_simple_poly_of_pointSet` — the same extraction on
  the point set of a finite plane graph with polygonal edges, which is the shape a skeleton
  stage arrives in. Root `Graph` namespace, per the convention of `Schoenflies/Graph/*`.
* `Schoenflies.exists_simple_poly_of_polyAccessible`,
  `Schoenflies.exists_simple_arc_of_polyAccessible` — `lem:accessible-endpoints`.
* `Schoenflies.exists_crosscut_of_polyAccessible` — `lem:accessible-endpoints` in crosscut form:
  when `Ω` misses a set `C` carrying `a` and `b`, the arc meets `C` exactly at its endpoints.
* `Schoenflies.exists_crosscut_of_biUnion_finite`,
  `Schoenflies.exists_crosscut_arc_of_biUnion_finite` — `lem:skeleton-crosscuts`, the extraction
  step: a connected finite polygonal union meeting `C` in exactly two points carries a simple
  polygonal crosscut between them.

`lem:skeleton-crosscuts` has two further halves that are **not** here, because the objects they
speak about are not yet in Lean: the construction of the connected union `Y = e_a ∪ |Λ| ∪ e_b`
from a finite stage of the skeleton, and the transport of the crosscut through the finite
skeleton homeomorphism. Both need the stage/anchor machinery of §"Continuity at the Jordan
curve"; the extraction between them is what this module supplies.
-/

open Metric Set

namespace Schoenflies

variable {Ω C D S : Set Plane} {a b z : Plane}

/-! ### Polygonal accessibility -/

/-! ### `lem:finite-polygonal-union` over a finite family

`Schoenflies.exists_simple_poly_of_union` takes the union as a `List (Set Plane)`. A skeleton
arrives as a finite *set* of edges, so the list is pure friction at the call site. This
paragraph removes it; it belongs in `Schoenflies/SimpleArc.lean`. -/

/-! ### `lem:skeleton-crosscuts`: the extraction step

The blueprint's proof of `lem:skeleton-crosscuts` builds, from a finite stage of the skeleton, a
connected finite union `Y = e_a ∪ |Λ| ∪ e_b` of polygonal arcs with `Y ∩ C = {a, b}`, and then
says: *subdivide `Y` at its finitely many vertices; the resulting finite graph is connected, so
it contains a simple graph path `P` from `a` to `b`, as in the proof of
`lem:finite-polygonal-union`; this path meets `C` only at its endpoints and is therefore a
polygonal crosscut.* That last step is what this paragraph is. The construction of `Y` from the
skeleton needs the stage machinery and is not here. -/

/-! ### `lem:accessible-endpoints` -/

/-- **`lem:accessible-endpoints`**, at the level of sets. -/
theorem exists_simple_arc_of_polyAccessible (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hab : a ≠ b) (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P a b ∧ P \ {a, b} ⊆ Ω := by
  obtain ⟨ws, -, -, -, hsub, harc⟩ :=
    exists_simple_poly_of_polyAccessible hΩ hconn hab ha hb
  exact ⟨poly ws, ⟨ws, rfl⟩, harc, hsub⟩

end Schoenflies

/-! ### The extraction on the point set of a finite polygonal plane graph

A skeleton stage arrives as a plane graph, and what the crosscut is extracted from is its point
set. Splitting that into "one singleton per vertex, one arc per edge" is the only step between
`Schoenflies.exists_simple_poly_of_biUnion_finite` and the graph, so it is done once here.

Following the convention of `Schoenflies/Graph/*`, these live in the root `Graph` namespace. -/
end

section
-- module Solutions.Q146_CD.SquareMover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.overlayGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Moving an interior point of the square

The pointed form of the bounded theorem needs a self-homeomorphism of the closed square that
fixes the boundary pointwise and carries one prescribed interior point to another. The
blueprint builds it by coning: the four triangles `conv {x, vᵢ, vᵢ₊₁}` triangulate the square,
and the affine map of each onto `conv {y, vᵢ, vᵢ₊₁}` fixing the two corners pastes with its
neighbours along the radial edges.

The construction here is the same map in different coordinates, and it is written so that no
pasting of four affine pieces is needed. It is the composite of two *shears*. A shear bends
one coordinate by the piecewise-linear self-map of `[-r, r]` that fixes the two endpoints and
moves a chosen breakpoint (`bend`), with a displacement that is scaled by a tent function of
the *other* coordinate (`tent`), so that it dies away to zero on the two transverse sides of
the square. The first shear moves the first coordinate of `x` to that of `y`, the second moves
the second coordinate.

Two features make this cheap. Writing the tent as a minimum of two affine functions makes it
continuous with no case split at all. And the family of shears is closed under inversion: the
shear with displacement parameters `k, k'` is undone by the shear with parameters `k + k',
-k'`, so bijectivity and the continuity of the inverse come from one composition identity
(`bend_bend`) instead of from a compactness argument, and no map has to be inverted by hand.

## Blueprint

* `Plane.exists_squareMover` — Lemma (Moving an interior point of the square): for interior
  points `x`, `y` of the square there are mutually inverse boundary-fixing self-maps `M`, `N`
  of the closed square with `M x = y`. `Plane.IsSquareMover` bundles the properties that make
  `M` a homeomorphism of the square onto itself, `Plane.IsSquareMover.homeomorph` repackages
  it as a `Homeomorph`, and `Plane.IsSquareMover.eqOn_frontier` states the boundary condition
  against the topological frontier, which `Plane.frontier_closedSquare` identifies with the
  blueprint's boundary square `S`.
* `Plane.iInter_eq_singleton_of_mem_tail` — the point-set kernel of Proposition (Skeleton
  agreement). The proposition itself is not statable in the present development; see the
  section comment at that lemma for exactly what is and is not proved.

Supporting material, of independent use: `Plane.tent` and `Plane.bend` with their algebra,
`Plane.continuousOn_bend`, the coordinate lemmas `Plane.abs_sub_le_supDist`,
`Plane.supDist_le_of_forall`, `Plane.exists_abs_sub_eq_of_supDist_eq`,
and `Plane.interior_closedSquare`.
-/

open Metric Set

namespace Schoenflies

namespace Plane

/-! ### The tent function -/

variable {r p q u : ℝ}

/-! ### Bending an interval -/

/-! ### Coordinates of the square -/

theorem abs_sub_lt_of_mem_openSquare {z c : Plane} {r : ℝ} (hz : z ∈ openSquare c r)
    (l : Fin 2) : |z l - c l| < r :=
  lt_of_le_of_lt (abs_sub_le_supDist z c l) hz

/-- The coordinate of a point of the open square, as a member of the open interval. -/
theorem mem_Ioo_of_mem_openSquare {z c : Plane} {r : ℝ} (hz : z ∈ openSquare c r) (l : Fin 2) :
    z l - c l ∈ Ioo (-r) r := by
  have := abs_sub_lt_of_mem_openSquare hz l
  rw [abs_lt] at this
  exact ⟨this.1, this.2⟩

/-! ### Shearing the square along one coordinate -/

variable {c : Plane} {a b k k' : ℝ} {i j l : Fin 2} {z : Plane}

/-- On the square, the level weight is a weight. -/
theorem shearWeight_mem (h : IsShear r a b k k') (hz : z ∈ closedSquare c r) :
    shearWeight c r b j z ∈ Icc (0 : ℝ) 1 := by
  have hb := abs_sub_le_supDist z c j
  have : |z j - c j| ≤ r := le_trans hb hz
  rw [abs_le] at this
  exact ⟨tent_nonneg h.peak.1 h.peak.2 this.1 this.2, tent_le_one h.peak.1 h.peak.2 _⟩

/-- On the square, the breakpoint of the bend performed by the shear is interior. -/
theorem shear_mid_mem (h : IsShear r a b k k') (hz : z ∈ closedSquare c r) :
    a + k * shearWeight c r b j z ∈ Ioo (-r) r :=
  mem_Ioo_of_weight h.base h.mid (shearWeight_mem h hz)

/-- On the square, the image of the breakpoint is interior. -/
theorem shear_top_mem (h : IsShear r a b k k') (hz : z ∈ closedSquare c r) :
    a + (k + k') * shearWeight c r b j z ∈ Ioo (-r) r :=
  mem_Ioo_of_weight h.base h.top (shearWeight_mem h hz)

/-- The shear maps the closed square to itself. -/
theorem shear_mapsTo (h : IsShear r a b k k') (i j : Fin 2) :
    MapsTo (shear c r a b k k' i j) (closedSquare c r) (closedSquare c r) := by
  intro z hz
  refine supDist_le_of_forall fun l => ?_
  by_cases hl : l = i
  · subst hl
    rw [shear_apply_same]
    have hu : |z l - c l| ≤ r := le_trans (abs_sub_le_supDist z c l) hz
    rw [abs_le] at hu
    have := bend_mem (shear_mid_mem (j := j) h hz).1 (shear_mid_mem (j := j) h hz).2
      (shear_top_mem (j := j) h hz).1 (shear_top_mem (j := j) h hz).2 hu.1 hu.2
    rw [show c l + bend r (a + k * shearWeight c r b j z)
      (a + (k + k') * shearWeight c r b j z) (z l - c l) - c l
      = bend r (a + k * shearWeight c r b j z)
        (a + (k + k') * shearWeight c r b j z) (z l - c l) by ring, abs_le]
    exact this
  · rw [shear_apply_ne hl]
    exact le_trans (abs_sub_le_supDist z c l) hz

/-- The shear with parameters `k + k', -k'` undoes the shear with parameters `k, k'`. -/
theorem shear_shear (h : IsShear r a b k k') (hij : j ≠ i) (hz : z ∈ closedSquare c r) :
    shear c r a b (k + k') (-k') i j (shear c r a b k k' i j z) = z := by
  have hweight : shearWeight c r b j (shear c r a b k k' i j z) = shearWeight c r b j z := by
    rw [shearWeight, shearWeight, shear_apply_ne hij]
  ext l
  by_cases hl : l = i
  · subst hl
    rw [shear_apply_same, hweight, shear_apply_same, show
      c l + bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
        (z l - c l) - c l
      = bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
        (z l - c l) by ring, show k + k' + -k' = k by ring]
    rw [bend_bend (shear_mid_mem (j := j) h hz).1 (shear_mid_mem (j := j) h hz).2
      (shear_top_mem (j := j) h hz).1 (shear_top_mem (j := j) h hz).2]
    ring
  · rw [shear_apply_ne hl, shear_apply_ne hl]

/-- The shear fixes the boundary of the square pointwise. -/
theorem shear_eq_self_of_boundary (h : IsShear r a b k k') (hij : j ≠ i)
    (hz : z ∈ closedSquare c r) (hbd : supDist z c = r) : shear c r a b k k' i j z = z := by
  have hr : 0 < r := pos_of_lt_lt h.peak.1 h.peak.2
  obtain ⟨m, hm⟩ := exists_abs_sub_eq_of_supDist_eq hbd
  ext l
  by_cases hl : l = i
  · subst hl
    rw [shear_apply_same]
    by_cases hml : m = l
    · -- the extreme coordinate is the bent one, and the bend fixes the two endpoints
      subst hml
      rcases (abs_eq hr.le).1 hm with he | he
      · rw [he, bend_right (shear_mid_mem (j := j) h hz).2]
        linarith
      · rw [he, bend_left (shear_mid_mem (j := j) h hz).1.le]
        linarith
    · -- the extreme coordinate is the transverse one: the level weight there is zero
      have hmj : m = j := fin2_eq_of_ne_of_ne hij hml
      subst hmj
      have hw : shearWeight c r b m z = 0 := by
        rcases (abs_eq hr.le).1 hm with he | he
        · rw [shearWeight, he]; exact tent_right h.peak.1 h.peak.2
        · rw [shearWeight, show z m - c m = -r by linarith [he]]
          exact tent_left h.peak.1 h.peak.2
      rw [hw]
      simp only [mul_zero, add_zero]
      rw [bend_refl h.base.1 h.base.2]
      ring
  · rw [shear_apply_ne hl]

/-- The shear is continuous on the square. -/
theorem shear_continuousOn (h : IsShear r a b k k') (i j : Fin 2) :
    ContinuousOn (shear c r a b k k' i j) (closedSquare c r) := by
  have hW : Continuous fun z : Plane => shearWeight c r b j z :=
    (continuous_tent r b).comp ((continuous_coord j).sub continuous_const)
  have hU : Continuous fun z : Plane => z i - c i := (continuous_coord i).sub continuous_const
  have hP : Continuous fun z : Plane => a + k * shearWeight c r b j z :=
    continuous_const.add (continuous_const.mul hW)
  have hQ : Continuous fun z : Plane => a + (k + k') * shearWeight c r b j z :=
    continuous_const.add (continuous_const.mul hW)
  have hbend := continuousOn_bend r (s := closedSquare c r) (isClosed_closedSquare c r) hP hQ hU
    (fun z hz => by linarith [(shear_mid_mem (j := j) h hz).1])
    (fun z hz => by linarith [(shear_mid_mem (j := j) h hz).2])
  exact continuous_id.continuousOn.add ((hbend.sub hU.continuousOn).smul continuousOn_const)

/-! ### Movers of the square -/

/-- A shear, together with the shear that undoes it, is a mover of the square. -/
theorem isSquareMover_shear (h : IsShear r a b k k') (hij : j ≠ i) :
    IsSquareMover c r (shear c r a b k k' i j) (shear c r a b (k + k') (-k') i j) where
  mapsTo := shear_mapsTo h i j
  mapsTo_inv := shear_mapsTo h.inv i j
  continuousOn := shear_continuousOn h i j
  continuousOn_inv := shear_continuousOn h.inv i j
  invOn := by
    refine ⟨fun z hz => shear_shear h hij hz, fun z hz => ?_⟩
    have hz' := shear_shear h.inv hij hz
    rwa [show k + k' + -k' = k by ring, neg_neg] at hz'
  fixes := fun z hz hbd => shear_eq_self_of_boundary h hij hz hbd
  fixes_inv := fun z hz hbd => shear_eq_self_of_boundary h.inv hij hz hbd

/-! ### Moving an interior point -/

/-- Blueprint Lemma (Moving an interior point of the square). For any two interior points `x`
and `y` of the closed square about `c` of radius `r` there is a self-homeomorphism of the
square carrying `x` to `y` and fixing the boundary pointwise.

The map is built as two shears: the first moves the first coordinate of `x` to that of `y`
along the level line of `x`, the second moves the second coordinate along the level line of
the result. Each shear bends one coordinate by a piecewise-linear map whose displacement dies
away to zero at the two transverse sides, which is exactly the piecewise-affine cone
construction of the blueprint, written in coordinates. -/
theorem exists_squareMover {c x y : Plane} {r : ℝ} (hx : x ∈ openSquare c r)
    (hy : y ∈ openSquare c r) :
    ∃ M N : Plane → Plane, IsSquareMover c r M N ∧ M x = y ∧ N y = x := by
  have hx0 := mem_Ioo_of_mem_openSquare hx 0
  have hx1 := mem_Ioo_of_mem_openSquare hx 1
  have hy0 := mem_Ioo_of_mem_openSquare hy 0
  have hy1 := mem_Ioo_of_mem_openSquare hy 1
  have hne : (1 : Fin 2) ≠ 0 := by decide
  have hne' : (0 : Fin 2) ≠ 1 := by decide
  -- the first shear moves the first coordinate, along the level line of `x`
  have h₁ : IsShear r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) := by
    refine ⟨hx1, hx0, by simpa using hx0, ?_⟩
    rw [show x 0 - c 0 + (0 + (y 0 - x 0)) = y 0 - c 0 by ring]
    exact hy0
  -- the second shear moves the second coordinate, along the level line of the result
  have h₂ : IsShear r (x 1 - c 1) (y 0 - c 0) 0 (y 1 - x 1) := by
    refine ⟨hy0, hx1, by simpa using hx1, ?_⟩
    rw [show x 1 - c 1 + (0 + (y 1 - x 1)) = y 1 - c 1 by ring]
    exact hy1
  have hmover := (isSquareMover_shear (c := c) h₁ hne).comp (isSquareMover_shear (c := c) h₂ hne')
  have hMx : (shear c r (x 1 - c 1) (y 0 - c 0) 0 (y 1 - x 1) 1 0 ∘
      shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1) x = y := by
    -- the composite carries `x` to `y`
    have hW₁ : shearWeight c r (x 1 - c 1) 1 x = 1 := by
      rw [shearWeight, tent_self hx1.1 hx1.2]
    have hfirst0 : shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1 x 0 = y 0 := by
      rw [shear_apply_same, hW₁]
      simp only [add_zero, zero_add, mul_one]
      rw [bend_self hx0.1]
      ring
    have hfirst1 : shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1 x 1 = x 1 :=
      shear_apply_ne hne
    have hW₂ : shearWeight c r (y 0 - c 0) 0
        (shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1 x) = 1 := by
      rw [shearWeight, hfirst0, tent_self hy0.1 hy0.2]
    simp only [Function.comp_apply]
    ext l
    revert l
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [shear_apply_ne hne', hfirst0]
    · rw [shear_apply_same, hW₂, hfirst1]
      simp only [add_zero, zero_add, mul_one]
      rw [bend_self hx1.1]
      ring
  refine ⟨_, _, hmover, hMx, ?_⟩
  have hinv := hmover.invOn.1 (show supDist x c ≤ r from hx.le)
  rwa [hMx] at hinv

/-! ### The boundary of the square -/

/-- A mover is the identity on the boundary square `S`. -/
theorem IsSquareMover.eqOn_frontier {M N : Plane → Plane} (h : IsSquareMover c r M N) :
    EqOn M id (frontier (closedSquare c r)) := by
  intro z hz
  rw [frontier_closedSquare, mem_setOf_eq] at hz
  exact h.fixes z (le_of_eq hz) hz

/-! ### The mover as a homeomorphism -/

/-! ### The point-set kernel of skeleton agreement

The blueprint's Proposition (Skeleton agreement) says that the limit map `F`, defined at `x`
as the unique point of the nested intersection `⋂ n, T n x` of closed target stars, agrees
with every finite skeleton map: if `x ∈ G_N ∩ D` then `F x = g_N x`. Its proof is one line of
point-set topology once the combinatorics is in place — the value `g_N x` lies in `T n x` for
every `n ≥ N`, hence in the intersection, hence is *the* point of the intersection.

That one line is what follows. The proposition itself cannot be stated in this development
yet: matched cell structures, carriers, stars, the skeleton homeomorphisms `g_n` and the limit
map `F` do not exist here. What is proved is exactly the implication the proposition rests on,
with the nested stars as an abstract antitone sequence of shrinking compacta and `g_N x` as an
abstract point of all late terms. -/

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.Inversion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Inversion in the unit circle, and the density of strongly accessible points

Two consequences of the Jordan curve theorem which have nothing to do with one another beyond
becoming available at the same moment.

## Inversion exchanges the two sides

Inversion about the unit circle centred at `a`,

    I_a(x) = a + (x - a) / ‖x - a‖²,

is the device that turns the *bounded* Schönflies theorem into the unbounded one: it swaps the
two sides of a Jordan curve `C` around any interior point `a`, sending the exterior of `C` onto
the interior of `C^a = I_a(C)` punctured at `a`. So a closed-interior extension for `C^a`,
pushed back through `I_a`, is a closed-*exterior* extension for `C`, which is
`prop:exterior-extension` and the second half of `thm:main`.

The map is Mathlib's `EuclideanGeometry.inversion a 1`, repackaged here as `Schoenflies.invert`
with the three facts the geometry needs: `Schoenflies.dist_invert_center`
(`‖I_a(x) - a‖ = 1/‖x - a‖`), `Schoenflies.invert_involutive`, and continuity away from `a`.
`Schoenflies.invertHomeo` bundles it as a self-homeomorphism of the punctured plane, which is
the form the conjugation `I_b ∘ f ∘ I_a` of `prop:exterior-extension` will want.

The proof of `lem:inversion-sides` is the blueprint's. Put `U = I_a(Ext C) ∪ {a}`. It is

* *open*: away from `a` because `I_a` is a homeomorphism of the punctured plane, and at `a`
  because `C ∪ Int(C)` is bounded, so the complement of a large closed ball `B̄(a, R)` lies in
  `Ext(C)` and inverts onto `B(a, 1/R) ∖ {a}`;
* *bounded*: a ball `B(a, δ)` lies in `Int(C)`, so exterior points stay at distance `≥ δ` from
  `a` and their inverses at distance `≤ 1/δ`;
* *connected*: the continuous image of `Ext(C)`, together with `a`, which is a limit of it
  because `Ext(C)` is unbounded;
* *bounded by `C^a`*: the third region `I_a(Int(C) ∖ {a})` is open, so the frontier of `U` can
  only be `C^a`, and every point of `C^a` is in it because `C = ∂Ext(C)`.

Being open, connected and with frontier disjoint from `(C^a)ᶜ`, `U` is a component of `(C^a)ᶜ`
(`Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`); being bounded, it is
`Int(C^a)`.

## The closed-exterior extension

`prop:exterior-extension` is the short assembly that sits on top of it, stated parametrically
over `prop:pointed-extension`. `Schoenflies.PointedInteriorExtension` is that interface, written
out: the bounded theorem with a prescribed interior point. `Schoenflies/Endgame.lean` derives
it from the closed-interior extension together with `lem:square-point-mover`, and
`Schoenflies/JordanSchoenflies.lean` supplies the square-extension input.

The assembly needs a name for "restricts to a homeomorphism onto", since it composes four of
them; `Schoenflies.IsHomeoOn` is that, in the unbundled `Schoenflies.Plane.IsSquareMover`
style.

## Density of strongly accessible points

`lem:tangent-dense` is three lines on top of `thm:jordan` and `lem:nearest-strong`: a point of
`C` is a limit of points of the region because `C` is the region's frontier, and the nearest
point of `C` to such a point is strongly accessible and no further from `p` than twice the
distance we started with. It is stated here for either region, since nothing in the argument
distinguishes them.

Everything below inherits the standing hypothesis of `thm:jordan` on `main`,

    harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ

threaded verbatim through every statement that consumes
`Schoenflies.IsJordanCurve.isSeparating`. The two density statements, which are about an
abstract `IsSeparating` curve, do not need it.

## Blueprint

* `Schoenflies.invert` and its algebra — the map `I_a` of §"The closed exteriors".
* `Schoenflies.invertHomeo` — "`I_a` is an involutive homeomorphism of `ℝ² ∖ {a}`".
* `Schoenflies.IsJordanCurve.invert_image` — "`C^a` is a Jordan curve", the first sentence of
  the proof of `lem:inversion-sides`.
* `Schoenflies.invert_image_outside`, `Schoenflies.invert_image_outside_union_singleton`,
  `Schoenflies.invert_image_inside_diff`, `Schoenflies.invert_image_union_outside`,
  `Schoenflies.inversion_sides` — `lem:inversion-sides`.
* `Schoenflies.exists_stronglyAccessible_dist_lt`, `Schoenflies.tangent_dense`,
  `Schoenflies.tangent_dense_inside` — `lem:tangent-dense`.
* `Schoenflies.PointedInteriorExtension` — the `prop:pointed-extension` interface, discharged
  by `Schoenflies.pointed_extension` in `Schoenflies/Endgame.lean`.
* `Schoenflies.exterior_extension` — `prop:exterior-extension`, parametrically on that interface.
* `Schoenflies.IsHomeoOn` — no blueprint statement; the language "restricts to a homeomorphism
  of `S` onto `T`" that `prop:exterior-extension` is phrased in.
-/

open Bornology Metric Set

namespace Schoenflies

variable {C Ω : Set Plane} {a p x y : Plane} {ε : ℝ}

/-! ### Inversion about the unit circle centred at a point

`Schoenflies.invert a` is `EuclideanGeometry.inversion a 1`, which Mathlib defines for every
point including the centre, sending `a` to itself. That convention is what makes
`Schoenflies.invert_involutive` hypothesis-free, and it costs nothing: every statement below
that cares about the centre says so. -/

/-! ### The image of a Jordan curve

Inversion is a homeomorphism on a neighbourhood of a curve avoiding the centre, so it carries
loops to loops. -/

/-! ### Inversion exchanges the two sides

The whole of `lem:inversion-sides`. The proof is carried in one theorem, because every step
speaks about the same set `U = I_a(Ext C) ∪ {a}`; the consequences that consumers want are
peeled off afterwards. -/

/-- **`lem:inversion-sides`.** For `a` interior to the Jordan curve `C`, the image of the
exterior of `C` under inversion about `a`, *together with the centre*, is exactly the interior
of `C^a = I_a(C)`.

This is the form the proof produces; `Schoenflies.invert_image_outside` is the blueprint's
statement, obtained by removing `a` from both sides. -/
theorem invert_image_outside_union_singleton
    (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' outside C ∪ {a} = inside (invert a '' C) := by
  have hsep : IsSeparating C := hC.isSeparating harc
  have haC : a ∉ C := ha.1
  have haout : a ∉ outside C := Set.disjoint_left.1 disjoint_inside_outside ha
  have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact haout hz
  -- The three ingredients: a big radius `R`, a small radius `δ`, and the openness of the image.
  obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
  obtain ⟨δ, hδ, hδin⟩ := Metric.isOpen_iff.1 hsep.isOpen_inside a ha
  have hTopen : IsOpen (invert a '' outside C) :=
    isOpen_invert_image hsep.isOpen_outside haout
  -- Exterior points keep their distance from `a`, since a whole ball about `a` is interior.
  have hfar : ∀ z ∈ outside C, δ ≤ dist z a := by
    intro z hz
    by_contra h
    push Not at h
    exact Set.disjoint_left.1 disjoint_inside_outside (hδin (mem_ball.2 h)) hz
  -- (1) `U` is bounded, by `1/δ`.
  have hUbdd : IsBounded (invert a '' outside C ∪ {a}) := by
    refine (isBounded_iff_subset_closedBall a).2 ⟨δ⁻¹, ?_⟩
    rintro z (⟨w, hw, rfl⟩ | rfl)
    · rw [mem_closedBall, dist_invert_center]
      exact inv_anti₀ hδ (hfar w hw)
    · simpa using inv_nonneg.2 hδ.le
  -- (2) `U` is open: it contains the ball `B(a, 1/R)`, whose inverse image is beyond `B̄(a,R)`.
  have hUball : ball a R⁻¹ ⊆ invert a '' outside C ∪ {a} := by
    intro z hz
    rcases eq_or_ne z a with rfl | hza
    · exact Or.inr rfl
    · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
      have hpos : 0 < dist z a := dist_pos.2 hza
      rw [mem_compl_iff, mem_closedBall, dist_invert_center]
      exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
  have hUopen : IsOpen (invert a '' outside C ∪ {a}) := by
    have hrw : invert a '' outside C ∪ {a} = invert a '' outside C ∪ ball a R⁻¹ := by
      refine Subset.antisymm (union_subset subset_union_left ?_)
        (union_subset subset_union_left hUball)
      rintro z rfl
      exact Or.inr (mem_ball_self (by positivity))
    rw [hrw]
    exact hTopen.union isOpen_ball
  -- (3) `U` is connected: `a` is a limit of the image of the (unbounded) exterior.
  have hacl : a ∈ closure (invert a '' outside C) := by
    rw [Metric.mem_closure_iff]
    intro e he
    obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
      by_contra hcon
      push Not at hcon
      exact hsep.not_isBounded_outside
        ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
    refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
    rw [dist_comm, dist_invert_center]
    exact inv_lt_of_inv_lt₀ he hzfar
  have hUconn : IsPreconnected (invert a '' outside C ∪ {a}) :=
    (hsep.isConnected_outside.image _
      ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
      (union_subset subset_closure (by rintro z rfl; exact hacl))
  -- (4) `U` misses `C^a`, since inversion is injective and `a` is not on `C`.
  have hUD : invert a '' outside C ∪ {a} ⊆ (invert a '' C)ᶜ := by
    rintro z (⟨w, hw, rfl⟩ | rfl)
    · rintro ⟨u, hu, huw⟩
      exact hw.1 (invert_injective a huw ▸ hu)
    · rintro ⟨u, hu, hua⟩
      exact haC (invert_eq_center_iff.1 hua ▸ hu)
  -- (5) The third region: the image of the punctured interior is open, and misses `U`.
  have hAopen : IsOpen (invert a '' (inside C \ {a})) :=
    isOpen_invert_image (hsep.isOpen_inside.sdiff isClosed_singleton) (fun h => h.2 rfl)
  have hAU : Disjoint (invert a '' (inside C \ {a})) (invert a '' outside C ∪ {a}) := by
    rw [Set.disjoint_left]
    rintro z ⟨w, ⟨hwin, hwne⟩, rfl⟩ (⟨u, hu, huw⟩ | hza)
    · exact Set.disjoint_left.1 disjoint_inside_outside hwin (invert_injective a huw ▸ hu)
    · exact hwne (mem_singleton_iff.2
        (invert_eq_center_iff.1 (mem_singleton_iff.1 hza)))
  -- The complement of `U` is covered by `C^a` and that third region.
  have hcompl : (invert a '' outside C ∪ {a})ᶜ ⊆
      invert a '' C ∪ invert a '' (inside C \ {a}) := by
    intro z hz
    by_cases hzC : invert a z ∈ C
    · exact Or.inl ⟨invert a z, hzC, invert_invert a z⟩
    · have hmem : invert a z ∈ inside C ∪ outside C := by
        rw [inside_union_outside]; exact hzC
      rcases hmem with hin | hout
      · refine Or.inr ⟨invert a z, ⟨hin, ?_⟩, invert_invert a z⟩
        intro hsing
        have hza : z = a := by
          rw [← invert_invert a z, mem_singleton_iff.1 hsing, invert_center]
        exact hz (Set.mem_union_right _ (mem_singleton_iff.2 hza))
      · exact absurd (show z ∈ invert a '' outside C ∪ {a} from
          Or.inl ⟨invert a z, hout, invert_invert a z⟩) hz
  -- (6) Hence the frontier of `U` is exactly `C^a`.
  have hfrontier : frontier (invert a '' outside C ∪ {a}) = invert a '' C := by
    refine Subset.antisymm (fun z hz => ?_) ?_
    · have hzU : z ∉ invert a '' outside C ∪ {a} := by
        rw [hUopen.frontier_eq] at hz; exact hz.2
      refine (hcompl hzU).resolve_right fun hA => ?_
      exact Set.disjoint_left.1 (hAU.closure_right hAopen) hA (frontier_subset_closure hz)
    · rintro z ⟨w, hwC, rfl⟩
      have hwne : w ≠ a := fun h => haC (h ▸ hwC)
      rw [hUopen.frontier_eq]
      refine ⟨closure_mono subset_union_left
        (mem_closure_image (continuousAt_invert hwne) ?_), fun hmem => hUD hmem ⟨w, hwC, rfl⟩⟩
      rw [← hsep.frontier_outside] at hwC
      exact frontier_subset_closure hwC
  -- (7) `U` is a component of the complement of `C^a`, and it is bounded, so it is the inside.
  have hsepa : IsSeparating (invert a '' C) := (hC.invert_image haC).isSeparating harc
  have haU : a ∈ invert a '' outside C ∪ {a} := Or.inr rfl
  have hcomp : connectedComponentIn (invert a '' C)ᶜ a = invert a '' outside C ∪ {a} :=
    Plane.connectedComponentIn_eq_of_frontier_disjoint hUopen hUconn hUD
      (by rw [hfrontier]; exact Set.inter_compl_self _) haU
  have hain : a ∈ inside (invert a '' C) := ⟨hUD haU, by rw [hcomp]; exact hUbdd⟩
  exact hcomp.symm.trans (hsepa.connectedComponentIn_eq_inside hain)

/-- **`lem:inversion-sides`**, the blueprint's statement:
`I_a(Ext(C)) = Int(C^a) ∖ {a}`. -/
theorem invert_image_outside (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' outside C = inside (invert a '' C) \ {a} := by
  rw [← invert_image_outside_union_singleton harc hC ha]
  refine (Set.union_sdiff_cancel_right ?_).symm
  rintro z ⟨⟨w, hw, rfl⟩, hza⟩
  exact Set.disjoint_left.1 disjoint_inside_outside ha
    (invert_eq_center_iff.1 (mem_singleton_iff.1 hza) ▸ hw)

/-- The closed-exterior form of `lem:inversion-sides`: inversion carries `C ∪ Ext(C)` onto
`(C^a ∪ Int(C^a)) ∖ {a}`. -/
theorem invert_image_union_outside (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' (C ∪ outside C) =
      (invert a '' C ∪ inside (invert a '' C)) \ {a} := by
  rw [Set.image_union, invert_image_outside harc hC ha, Set.union_sdiff_distrib,
    Set.sdiff_singleton_eq_self (notMem_invert_image ha.1)]

/-- The centre of the inversion is interior to the inverted curve. -/
theorem mem_inside_invert_image (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) : a ∈ inside (invert a '' C) := by
  rw [← invert_image_outside_union_singleton harc hC ha]
  exact Or.inr rfl

/-! ### Homeomorphisms between subsets of the plane

`prop:exterior-extension` is a composition of four restricted homeomorphisms, so it needs a
name for "`f` restricts to a homeomorphism of `S` onto `T`". `Schoenflies.IsHomeoOn` is that
name, written the way `Schoenflies.Plane.IsSquareMover` writes the same thing: unbundled, with
the inverse named, so that composing two of them composes two honest functions `Plane → Plane`
instead of producing a subtype-valued `Homeomorph` that must be unwrapped at every use.

**This notion is general and belongs in a lower module.** It is here because
`prop:exterior-extension` is the first statement that needs it; the integrator should hoist it
(and check that no concurrent branch introduced a twin). -/

/-! ### The closed-exterior extension

`prop:exterior-extension`, assuming `prop:pointed-extension`. That is the blueprint's own
citation, and it is the one statement of the endgame that is not yet available: it rests on
`thm:closed-interior-extension` (open) together with `lem:square-point-mover`
(`Schoenflies.Plane.exists_squareMover`, on `main`) and `lem:jordan-circle`
(`Schoenflies.IsJordanCurve.homeomorph`, on `main`).

Everything that inversion contributes is here; discharging
`Schoenflies.PointedInteriorExtension` finishes the exterior half of `thm:main`. -/

/-- **`prop:exterior-extension` (closed-exterior extension).** Every homeomorphism between two
Jordan curves extends to a homeomorphism of their closed exteriors.

Assumes `prop:pointed-extension` (`Schoenflies.PointedInteriorExtension`) and the standing
hypothesis `harc` of `thm:jordan`. The proof is the blueprint's: choose `a ∈ Int(C)` and
`b ∈ Int(C')`, invert about each, extend the conjugated boundary map `I_b ∘ f ∘ I_a` over the
interior of `C^a` so that `a ↦ b`, delete the two centres, and conjugate back — the deleted
punctured closed interiors being exactly the closed exteriors, by `lem:inversion-sides`. -/
theorem exterior_extension (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hpt : PointedInteriorExtension) {C C' : Set Plane} {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ outside C) (C' ∪ outside C') ∧ EqOn F f C := by
  -- Two interior points, from `thm:jordan`.
  obtain ⟨a, ha⟩ := (hC.isSeparating harc).isConnected_inside.nonempty
  obtain ⟨b, hb⟩ := (hC'.isSeparating harc).isConnected_inside.nonempty
  have haC : a ∉ C := ha.1
  have hbC' : b ∉ C' := hb.1
  -- Inversion, on the curves alone …
  have hIa : IsHomeoOn (invert a) (invert a) C (invert a '' C) := isHomeoOn_invert haC
  have hIb : IsHomeoOn (invert b) (invert b) C' (invert b '' C') := isHomeoOn_invert hbC'
  -- … and on the closed exteriors, which is `lem:inversion-sides`.
  have haout : a ∉ C ∪ outside C := by
    rintro (h | h)
    · exact haC h
    · exact Set.disjoint_left.1 disjoint_inside_outside ha h
  have hbout : b ∉ C' ∪ outside C' := by
    rintro (h | h)
    · exact hbC' h
    · exact Set.disjoint_left.1 disjoint_inside_outside hb h
  have hEa : IsHomeoOn (invert a) (invert a) (C ∪ outside C)
      ((invert a '' C ∪ inside (invert a '' C)) \ {a}) := by
    rw [← invert_image_union_outside harc hC ha]
    exact isHomeoOn_invert haout
  have hEb : IsHomeoOn (invert b) (invert b) (C' ∪ outside C')
      ((invert b '' C' ∪ inside (invert b '' C')) \ {b}) := by
    rw [← invert_image_union_outside harc hC' hb]
    exact isHomeoOn_invert hbout
  -- The conjugated boundary homeomorphism `f* = I_b ∘ f ∘ I_a : C^a → (C')^b`.
  have hstar : IsHomeoOn (invert b ∘ f ∘ invert a) (invert a ∘ g ∘ invert b)
      (invert a '' C) (invert b '' C') := by
    have := (hIa.symm.comp hfg).comp hIb
    simpa [Function.comp_assoc] using this
  -- Extend it over the interior of `C^a`, sending `a` to `b`.
  obtain ⟨Φ, Ψ, hΦ, hΦeq, hΦa⟩ := hpt (invert a '' C) (invert b '' C') _ _ a b
    (hC.invert_image haC) (hC'.invert_image hbC') hstar
    (mem_inside_invert_image harc hC ha) (mem_inside_invert_image harc hC' hb)
  -- Delete the two centres, then conjugate back.
  have hΦ' := hΦ.sdiff_singleton
    (Set.mem_union_right _ (mem_inside_invert_image harc hC ha)) hΦa
  refine ⟨invert b ∘ Φ ∘ invert a, invert a ∘ Ψ ∘ invert b, ?_, ?_⟩
  · have := (hEa.comp hΦ').comp hEb.symm
    simpa [Function.comp_assoc] using this
  · -- On `C` the conjugate is `f`, because `I_a` and `I_b` are involutions.
    intro z hz
    have h1 : invert a z ∈ invert a '' C := ⟨z, hz, rfl⟩
    simp only [Function.comp_apply, hΦeq h1, invert_invert]

/-! ### Density of strongly accessible points

`lem:tangent-dense`. Nothing here distinguishes the two regions, so the lemma is proved for
either. The hypotheses are those of `Schoenflies.stronglyAccessible_of_isMinOn`: the region
swallows the component of each of its points, and the curve is in its closure — which for a
separating curve is `C = ∂Ω`. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.GeneralCrosscut
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.overlayGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The crosscut theorem for a general Jordan curve

`P` is a simple polygonal arc with distinct endpoints `p, q` on a Jordan curve `C` and all its
remaining points in `D = Int(C)`; `A₁, A₂` are the two arcs of `C` from `p` to `q`. Then
`D ∖ P` has exactly two components, namely `Int(A₁ ∪ P)` and `Int(A₂ ∪ P)`, and consequently
`ℝ² ∖ (C ∪ P)` has precisely three regions, with boundaries `C`, `A₁ ∪ P`, `A₂ ∪ P`.

The proof is short because both halves already exist. `Schoenflies.crosscut_cells` exhibits two
distinct components of `D ∖ P`; `Schoenflies.crosscut_components_exhaust` says there are no
others; and the final paragraph is `Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`
applied three times. All this module does is fit the pieces together and name the result.

## The two sides are named by their arcs, and they are `inside (Aᵢ ∪ P)`

Everything Part II asks of this theorem is asked of *one labelled side*:
`lem:crosscut-side-correspondence` wants "the component whose closure meets `C` in `Aᵢ`" as a
function of `i`, and `prop:initial-pair`, `lem:cellulation-invariants` and `thm:finite-transfer`
all consume the labelled form. So there is no existential anywhere in the conclusions below: the
side belonging to the arc `A` is literally `Schoenflies.inside (A ∪ P)`, which is already a
function of `A`, carries the whole `inside`/`IsSeparating` API, and is exactly the set the
blueprint writes `Int(A ∪ P)`. The labelling lemma is `IsCrosscut.closure_side_inter`:

    closure (inside (A₁ ∪ P)) ∩ C = A₁.

Each statement is proved for `A₁` only; `IsCutPair.symm` swaps the two arcs, so
`h.foo hjordan hcut.symm` is the `A₂` instance of `h.foo hjordan hcut`. That is why no lemma
below mentions `A₂` in its conclusion.

## What is assumed

Two hypotheses are threaded through, both of which are being discharged elsewhere right now:

* `hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S` — `thm:jordan`. Only the
  separation clause is used; the boundary clause is part of `Schoenflies.IsSeparating`, so no
  second hypothesis is needed.
* `hcollars : HasArcCollars (inside C) P` — blueprint Lemma 1.8 (b) for the arc `P` inside the
  Jordan domain, the standing hypothesis of `Schoenflies/CrosscutAtMostTwo.lean`.

Neither is a restatement of anything proved here.

## Blueprint

* `Schoenflies.IsCrosscut` — the hypotheses of `thm:general-crosscut` on `C, P, p, q`.
* `Schoenflies.IsCutPair` — "`A₁, A₂` the two arcs of `C` from `p` to `q`, as in
  `lem:jordan-circle`"; `Schoenflies.exists_isCutPair` produces one from
  `IsJordanCurve.two_arcs`.
* `Schoenflies.IsCrosscut.side_subset`, `.side_isComponent`, `.closure_side_inter`,
  `.side_ne`, `.disjoint_sides`, `.components_eq`, `.inside_diff_eq` — the first half of
  `thm:general-crosscut`, one labelled side at a time, and then the exhaustion. The side's own
  topology comes with it: `.isOpen_side`, `.isConnected_side`, `.isBounded_side`,
  `.side_nonempty`, `.frontier_side`, `.closure_side`.
* `Schoenflies.general_crosscut` — `thm:general-crosscut`, first sentence, bundled.
* `Schoenflies.IsCrosscut.compl_eq`, `.compl_eq_three`, `.outside_isComponent`,
  `.side_isComponent_compl`, `.three_regions` — the "consequently" sentence.
* `Schoenflies.general_crosscut_three_regions` — `thm:general-crosscut`, second sentence,
  bundled, with the three boundaries.
* `Schoenflies.IsArcBetween.not_subset_pair` — an arc is more than its two endpoints; general,
  and the only new fact about arcs this module needs.
-/

open Bornology Set unitInterval

namespace Schoenflies

variable {C P A A₁ A₂ : Set Plane} {p q z : Plane}

/-! ### An arc is more than its two endpoints

This is what `Schoenflies.arcs_ne` needs in order to conclude `A₁ ≠ A₂` from the fact that the
two arcs meet only at `p` and `q`. It is a general fact about arcs and belongs in
`Schoenflies/Curve.lean`; it is here because nothing on `main` states it. -/

/-! ### The configuration

Two bundles of hypotheses. `IsCrosscut C P p q` is the blueprint's "`P` is a simple polygonal
arc with distinct endpoints `p, q ∈ C` and all other points in `D = Int(C)`"; distinctness of
`p` and `q` is *not* a field, since an arc between two points always has them distinct.
`IsCutPair C p q A₁ A₂` is "`A₁, A₂` are the two arcs of `C` from `p` to `q`". The two are kept
apart because the arcs are a *choice* — swapping them is a symmetry of the whole theorem, and
`IsCutPair.symm` is what makes every statement below need proving only once. -/

/-! ### Elementary consequences of the configuration

Nothing here needs `thm:jordan`: these are the set-theoretic facts that turn "the crosscut runs
inside the curve" into the hypotheses `Schoenflies.crosscut_cells` takes. -/

/-- **Theorem "Crosscut theorem", first sentence** (`thm:general-crosscut`). `Int(C) ∖ P` has
exactly two components, namely `Int(A₁ ∪ P)` and `Int(A₂ ∪ P)`.

"Exactly two" is spelled out: the two sets are nonempty, disjoint, each is a component, they
cover, they are distinct, and every component is one of them. The last two clauses are the
labelling `closure (inside (Aᵢ ∪ P)) ∩ C = Aᵢ`, which is what tells the two apart. Each clause
is separately available as a lemma in the `Schoenflies.IsCrosscut` namespace; this bundle exists
only so that the blueprint statement appears once, in one place. -/
theorem general_crosscut (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧ closure (inside (A₂ ∪ P)) ∩ C = A₂ :=
  ⟨h.inside_diff_eq hjordan hcut hcollars, h.disjoint_sides hjordan hcut,
    h.side_nonempty hjordan hcut, h.side_nonempty hjordan hcut.symm, h.side_ne hjordan hcut,
    h.side_isComponent hjordan hcut, h.side_isComponent hjordan hcut.symm,
    h.components_eq hjordan hcut hcollars, h.closure_side_inter hjordan hcut,
    h.closure_side_inter hjordan hcut.symm⟩

/-! ### The three regions of `ℝ² ∖ (C ∪ P)`

The blueprint's final paragraph. `P` misses `Ext(C)`, so the complement of `C ∪ P` splits as
`Ext(C) ⊔ (Int(C) ∖ P)`; the first half has just split the second summand in two; and each of
the three pieces is a component of the whole because its boundary misses it
(`lem:clopen-component`, here `Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`). -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolyArcRealize
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Realizing a simple polygonal arc as a `PolyArc`

`Schoenflies/ArcCollars.lean` proves blueprint Lemma 1.8 (b) — the two-sided collar of an arc,
hence `Schoenflies.HasArcCollars` — for an arc *presented by its vertex list*, a
`Schoenflies.PolyArc`, and carries the presentation itself as the hypothesis
`Schoenflies.IsPolyArcCarrier`. Nothing on `main` could supply that hypothesis for anything but
a straight segment, so `lem:crosscut-at-most-two` and `thm:general-crosscut` were not in fact
unblocked. This module closes the gap: a set that is both an arc between two points and
polygonal *is* the carrier of a `PolyArc`.

This is the arc analogue of `Schoenflies.exists_closedPolygon`, and the route is the one
`Schoenflies/Realization.lean` takes in the closed case, on a linear index instead of a cyclic
one. The closed-case machinery is reused verbatim wherever it does not mention the loop.

## The three steps

1. **Cut the point set into pieces.** `Schoenflies.exists_isClean` gives a finite list `Q` of
   nondegenerate segments occupying `P`, with pairwise disjoint interiors and no end interior to
   any of them; the two endpoints `a`, `b` of the arc are put on the cut list, so both are ends
   of pieces.
2. **Order the pieces along the arc.** The parametrisation `f` reaches an end of a piece at
   finitely many parameters; listed in increasing order they cut `[0, 1]` into gaps. A gap image
   is connected and misses the ends, so it lies in one piece interior; the interior is connected
   and covered by the closed gap images, so it lies in that one gap. Gaps and pieces correspond
   one to one and the ends, in the order `f` reaches them, are a *linear* vertex list.

   The only change from the closed case is bookkeeping at the far end. There the loop returns to
   `f 0`, so the parameters live in `[0, 1)` and the last gap wraps; here `f 1 = b` is a genuine
   extra vertex. Taking the parameter set to be `{t ∈ [0, 1) | f t` is an end of a piece`}` —
   *exactly* the set `Schoenflies/Realization.lean` uses — makes `Schoenflies.parNext` of the
   last index equal `1` by definition, which is precisely the missing right end. So
   `Schoenflies.par`, `Schoenflies.parNext` and `Schoenflies.exists_mem_gap` are used unchanged,
   and `n` parameters give `n` edges and `n + 1` vertices.
3. **Delete redundant vertices.** `Schoenflies.PreArc` is a `PolyArc` less its `corner` field,
   and `Schoenflies.PreArc.deleteVertex` removes one vertex at which the two edges are
   collinear. Each deletion shortens the list by one, so the induction terminates; unlike the
   cyclic case it can never get stuck, because a one-edge arc satisfies `corner` vacuously.

## Why the arc is not closed into a curve first

The tempting shortcut is to join `b` back to `a` by one extra polygonal path far from the arc,
apply `Schoenflies.exists_closedPolygon_arcs` to the resulting Jordan curve, and read the arc off
the cyclic list. It is circular. The return path has to meet `P` only at `a` and `b`, so it has
to leave `a` in a direction along which the arc does not run; knowing that there *is* such a
direction — that `P` is locally one segment at `a` — is a consequence of the realization, not an
input to it. A *straight* segment from `b` to `a` will not do either: an arc can perfectly well
cross the chord joining its endpoints. And avoiding `P` in the large needs `ℝ² ∖ P` connected,
which is `thm:arc-complement`, stated there with an explicit hypothesis. Route (A) below needs
none of this.

## Padding the vertex list

`PolyArc.vertex` is a function on all of `ℕ` asked to be *globally* injective — the convention
its docstring records, which supplies `A.tang i` and `A.len i` directly. A realization
produces `n + 1` vertices and nothing beyond, so the list has to be padded.
`Schoenflies.exists_injective_extend` does it once and for all, by walking off along the first
coordinate past every value the finite list takes.

## Blueprint

There is no blueprint label for this statement: like the closed-curve realization theorem of
`Schoenflies/Realization.lean` it is the bridge the blueprint takes for granted when it says
"let `P` be a simple polygonal arc with vertices `v_0, …, v_{n+1}`". Its consumers are
`lem:polygonal-collar` (b) and, through it, `lem:crosscut-at-most-two` and
`thm:general-crosscut`.

* `Schoenflies.exists_injective_extend` — a finite injective vertex list extends to an injective
  sequence.
* `Schoenflies.PreArc` — a `PolyArc` less the `corner` field: a simple polygonal arc presented by
  a vertex list, redundant vertices allowed. The arc analogue of `Schoenflies.PrePolygon`.
* `Schoenflies.skipIdx`, `Schoenflies.PreArc.deleteVertex`,
  `Schoenflies.PreArc.carrier_deleteVertex` — the blueprint's "delete redundant vertices at which
  two consecutive edges are collinear", as an operation. The arc analogue of
  `Schoenflies.PrePolygon.deleteLast`, and simpler: with a linear index no rotation is needed, so
  the vertex to be deleted stays where it is.
* `Schoenflies.PreArc.exists_polyArc` — the deletion run to completion. The arc analogue of
  `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`.
* `Schoenflies.exists_preArc_of_isArcBetween` — steps 1 and 2: a set-level simple polygonal arc
  is the carrier of a vertex list. The arc analogue of
  `Schoenflies.exists_prePolygon_of_isJordanCurve`.
* `Schoenflies.isPolyArcCarrier_of_isPolygonal` — **the realization theorem for arcs**, and the
  discharge of `Schoenflies.IsPolyArcCarrier`.
* `Schoenflies.hasArcCollars_of_isPolygonal` — blueprint Lemma 1.8 (b) for a set-level simple
  polygonal arc, with nothing left standing.
* `Schoenflies.IsCrosscut.hasArcCollars`, `Schoenflies.crosscut_at_most_two_of_isPolygonal` — the
  same at the call site of `thm:general-crosscut`.
-/

open Metric Set unitInterval

namespace Schoenflies

open Plane

/-! ## Padding a finite vertex list to an injective sequence

`PolyArc` asks for a globally injective `vertex : ℕ → Plane`; a realization only produces
`n + 2` points. The padding walks off along the first coordinate, past every value the finite
part takes, which keeps the extension injective and disjoint from the finite part. -/

/-! ## The index map of a deletion

On a linear index there is nothing to rotate: a vertex is deleted where it stands, and `skipIdx i`
is the inclusion of the shortened index set into the old one — the identity up to `i`, a shift by
one beyond it. It is the arc analogue of `Schoenflies.PrePolygon.emb`, and much simpler, because
that one has to wrap. -/

/-! ## Arcs before normalization

`PreArc` is `PolyArc` with the `corner` field removed, exactly as `Schoenflies.PrePolygon` is
`Schoenflies.ClosedPolygon` with it removed. Realization produces one of these; normalization
turns it into a `PolyArc`. -/

/-! ## From a clean presentation to a linear vertex list

The arc reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the arc reaches them, are the vertex list
of a `PreArc` whose edges are the pieces.

The parameter set is taken inside `[0, 1)`, exactly as in the closed case, so that
`Schoenflies.parNext` of the last index is `1` by definition. That is not a trick: `f 1 = b` is
the last vertex, and this is what puts it there. Both `a` and `b` are forced onto the cut list,
which is what makes `0` a parameter and `b` an end of a piece. -/

/-! ## The realization theorem for arcs

Realization followed by normalization. This is the statement
`Schoenflies/ArcCollars.lean` names at the end of its file as the one thing it does not prove. -/

/-! ## The collar hypothesis at the call site of `thm:general-crosscut`

`Schoenflies.IsCrosscut` carries exactly what the discharge needs: `P` is an arc from `p` to `q`,
`P` is polygonal, and `P ∖ {p, q}` lies in `inside C`, whose openness comes from the curve being
closed. So `hcollars` is never again a hypothesis of the crosscut theorem — only `thm:jordan`
is. -/

variable {C P A₁ A₂ : Set Plane} {p q : Plane}

/-- **Theorem "Crosscut theorem", first sentence** (`thm:general-crosscut`), with the collar
hypothesis discharged: only `thm:jordan` is left. -/
theorem general_crosscut' (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧ closure (inside (A₂ ∪ P)) ∩ C = A₂ :=
  general_crosscut hjordan h hcut h.hasArcCollars

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareCycle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The subdivided boundary of a square is a cycle

`Schoenflies.SquaresTwoConnected`, the last hypothesis between this library and
`thm:jordan`, discharged.

## What has to be built

`Schoenflies.squareGraph pieces points c r` is the part of a polygonal overlay lying on the
boundary of the axis-parallel square of `ℓ^∞`-radius `r` about `c`, when the four sides of that
square are among the overlay's source segments.  It is the subdivided boundary of the square,
so it is a cycle, and `Graph.IsLongCycle.isTwoConnected` finishes.  What is missing on `main`
is the **cyclic order** of the cut points: the graph is presented as a set of edges, with
nothing saying which edge follows which.

## The route

One real-valued coordinate does the whole of it.  `Schoenflies.sqCoord c r` is the *perimeter
coordinate*: the distance travelled from the north-east corner going counterclockwise round the
boundary, a number in `[0, 8r)`.  It is affine on each side, and it is the ordering tool of
`Schoenflies/SegmentOrder.lean` — distance from the side's first corner — with an offset.

* `Graph.IsIncWalk` is a walk along which a chosen real function strictly increases.  Such a
  walk is automatically a **path** (`Graph.IsIncWalk.isPath`): the freshness clause of
  `Graph.IsPath` says the vertex a step departs from is not visited later, and a vertex visited
  later has a strictly larger value.  This is the only place where "the cut points are in
  order" is turned into a combinatorial statement, and it replaces every argument about
  distinctness of vertices.
* `Schoenflies.exists_incWalk_of_chain` is the one-dimensional heart: a finite family of
  nondegenerate segments inside one ambient segment `[a, b]`, with pairwise disjoint interiors,
  with every end of every one of them interior to none of them, and covering `[a, b]`, is a
  **chain** from `a` to `b` — an `IsIncWalk` for the coordinate `dist a ·` whose edge list is
  exactly the family.  The induction is on the number of segments, and the step is
  `Schoenflies.exists_next_piece`: the piece leaving the current point is the one covering a
  point just beyond it, "just" being measured by the least end-coordinate strictly ahead.
* The four sides are chained separately and concatenated.  The concatenation is a closed walk
  at the north-east corner, so its last edge is split off (`Graph.IsIncWalk.split_last`) and
  becomes the distinguished edge of `Graph.IsCycleThrough`.

## Blueprint

* `Schoenflies.squaresTwoConnected` — the hypothesis `Schoenflies.SquaresTwoConnected` of
  `thm:arc-complement`, discharged.  In the blueprint this is the unstated step of
  "it follows inductively from `lem:union-two-connected` that `Γ_i` is 2-connected": the
  induction starts from one subdivided square boundary, and that it is a cycle is taken for
  granted there.
* `Schoenflies.exists_isLongCycle_squareGraph` — the cycle itself, with the clause that makes
  it usable: the cycle graph **is** `squareGraph`, not merely a subgraph of it.  A consumer
  wanting the boundary cycle of a square as an object, rather than 2-connectedness, takes it
  from here.
* `Schoenflies.exists_incWalk_insideEdges` — the subdivision of one source segment of a
  polygonal overlay, as a **path**.  `Schoenflies/SquareMeshConnected.lean` names exactly this
  as the theorem missing from `main` that blocks `prop:anchored-square-mesh` from being carried
  over to `Schoenflies.squareMesh`.  Its own ground is `Schoenflies.exists_incWalk_of_chain`,
  which knows nothing about overlays either.
* `Graph.IsIncWalk` — no blueprint statement; it is the device that makes
  `lem:polygonal-overlay`'s cut points into an ordered cycle.
-/

open Metric Set
open scoped Graph

/-! ## Part 1: a walk along which a real function increases -/

/-! ## Part 2: a tiling of one segment is a chain

Everything here happens along a single ambient segment `[a, b]`, and the coordinate is the one
`Schoenflies/SegmentOrder.lean` supplies: the distance from `a`.  A finite family of
nondegenerate pieces inside `[a, b]`, with disjoint interiors, no end interior to any of them,
and covering the part of `[a, b]` ahead of the current point, is walked through from the current
point to `b`, one piece at a time, in increasing distance from `a`. -/

namespace Schoenflies

open Plane

variable {a b p : Plane} {E : Set Piece}

/-! ## Part 3: the perimeter coordinate of a square boundary

The four sides of the square are axis-parallel, so on each of them the Euclidean distance from
the side's first corner is the difference of one coordinate.  `Schoenflies.sqCoord` glues the
four into one function on the plane: the distance travelled from the north-east corner going
counterclockwise.  It is `dist` from the side's first corner plus a multiple of `2r`, and that
is the *only* property of it that is ever used. -/

variable {c z : Plane} {r : ℝ}

open Plane

/-! ### The distance from a side's first corner, in coordinates -/

/-! ### Where two sides meet -/

/-! ### The perimeter coordinate -/

/-! ## Part 4: the overlay edges on one side

A nondegenerate straight segment inside the boundary of a square lies inside **one** side: its
midpoint is on the boundary, so one of the two coordinates is extreme there, and an average of
two numbers at most `c i + r` can only equal `c i + r` when both are.  That is
`Schoenflies.exists_side_of_mem_squareEdges`, and it is the only genuinely two-dimensional step
in the file. -/

variable {pieces : List Piece} {points : List Plane}

/-! ## Part 5: the four sides, chained

Each side of the square is a source segment of the overlay, so the edges lying on it tile it,
and Part 2 walks through them.  The four walks are then glued at the corners. -/

theorem mem_edgeSet_squareGraph_iff {Q : Piece} :
    Q ∈ E(squareGraph pieces points c r) ↔ Q ∈ squareEdges pieces points c r := Iff.rfl

/-! ### The subdivision of one source segment

Nothing about squares enters here.  `Schoenflies/SquareMeshConnected.lean` records this as the
theorem missing from `main` — "the subdivision of a segment at a finite point set is a path" —
that blocks `prop:anchored-square-mesh` from being carried over to `Schoenflies.squareMesh`. -/

/-- **The subdivision of one source segment of an overlay is a path**, from one end of the
segment to the other, taking every overlay edge inside it exactly once, in increasing distance
from the first end. -/
theorem exists_incWalk_insideEdges (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points) {P₀ : Piece}
    (hP₀ : P₀ ∈ pieces) (hP₀nd : P₀.Nondeg) :
    ∃ W : List Piece, (∀ Q, Q ∈ W ↔ Q ∈ insideEdges pieces points P₀) ∧
      (overlayGraph pieces points).IsIncWalk (fun z => dist P₀.1 z) P₀.1 W P₀.2 := by
  -- the far end of the source segment is a cut point, hence a vertex
  obtain ⟨Q, hQ, hend, -⟩ := exists_overlayPiece_end_subset (points := points) hnd
    (hEnds P₀ hP₀ P₀.2 (Or.inr rfl)) hP₀ (right_mem_segment ℝ P₀.1 P₀.2)
  exact exists_incWalk_of_chain (G := overlayGraph pieces points) hP₀nd ⟨Q, hQ, hend⟩
    _ P₀.1 _ rfl
    (isPieceChain_insideEdges hnd hEnds hMeets hP₀) fun R hR => ⟨hR.1, Or.inl ⟨rfl, rfl⟩⟩

/-! ## Part 6: the cycle, and `SquaresTwoConnected`

The four walks are concatenated into a closed walk at the north-east corner.  The perimeter
coordinate increases along the first three sides and along all of the fourth but its last step,
which returns to the corner where the coordinate is `0`; so that step is split off and becomes
the distinguished edge of `Graph.IsCycleThrough`. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.JordanClosed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Part I, with nothing assumed

The end of Part I. Everything below is already proved elsewhere; this module supplies the last
arguments and states the four headline theorems with no hypotheses at all, so that a consumer —
and the axiom audit — sees them in the form the blueprint states them.

Two hypotheses were carried, deliberately, across three waves of parallel work, under the
standing rule that a missing result is named rather than `sorry`-ed:

* `Schoenflies.SquaresTwoConnected`, in `Schoenflies/ArcComplement.lean` — a subdivided
  axis-parallel square boundary is 2-connected. Discharged by
  `Schoenflies.squaresTwoConnected` in `Schoenflies/SquareCycle.lean`.
* `Schoenflies.IsPolyArcCarrier`, in `Schoenflies/ArcCollars.lean` — every simple polygonal arc
  is the carrier of a `PolyArc`. Discharged by
  `Schoenflies.isPolyArcCarrier_of_isPolygonal` in `Schoenflies/PolyArcRealize.lean`, the arc
  analogue of the realization theorem that `Schoenflies/Realization.lean` proves for closed
  curves.

Discharging the first makes `thm:arc-complement`, and with it `lem:accessible-dense` and
`thm:jordan`. Supplying the second removes the collar hypothesis from
`lem:crosscut-at-most-two`, and with `thm:jordan` that finishes `thm:general-crosscut`.

## Blueprint

* `Schoenflies.arc_complement` — **`thm:arc-complement`**: the complement of a simple arc in
  the plane is connected.
* `Schoenflies.jordan_curve_theorem` — **`thm:jordan`**: a Jordan curve separates the plane
  into exactly two regions, one bounded and one unbounded, each with the curve as its boundary.
  Stated as `IsSeparating C`, the same predicate `thm:polygonal-jordan` uses, so that every
  consumer written against the polygonal case applies verbatim.
* `Schoenflies.crosscut_theorem`, `Schoenflies.crosscut_theorem_three_regions` —
  **`thm:general-crosscut`**.
-/

open Set

namespace Schoenflies

/-- **`thm:general-crosscut`, first sentence.** A polygonal crosscut of a Jordan domain cuts it
into exactly two components, the interiors of the two curves the crosscut makes with the two
arcs of `C`. The two sides are labelled by which arc of `C` their closure meets. -/
theorem crosscut_theorem {C P A₁ A₂ : Set Plane} {p q : Plane}
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧ closure (inside (A₂ ∪ P)) ∩ C = A₂ :=
  general_crosscut' (fun _ hS => jordan_curve_theorem hS) h hcut

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryContinuity2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Continuity at the Jordan curve, and `thm:square-extension`

The last three statements of the manuscript: `lem:crosscut-side-correspondence`,
`prop:boundary-continuity`, and the assembly of `thm:square-extension` from them.

`Schoenflies/BoundaryContinuity.lean` proves the statement with the real combinatorial content,
`lem:skeleton-crosscuts` (`Graph.IsStageOn.exists_crosscut`), for one finite
plane graph. This module takes the crosscuts as given and finishes the section.

## The construction inputs

This module isolates the construction-dependent data as explicit hypotheses. They are supplied
for the quantitative stage recursion in `Schoenflies/InteriorHomeomorphism.lean` and
`Schoenflies/BoundaryAnchors.lean`. Nothing else is assumed: `thm:jordan` and
`thm:general-crosscut` are used through `Schoenflies/JordanClosed.lean`, where their hypotheses
are supplied.

* **`prop:interior-homeomorphism`** enters as `IsHomeoOn F F' (inside C) (Plane.openSquare 0 1)`
  — the `Schoenflies.IsHomeoOn` shape of `Schoenflies/Inversion.lean`: a map, a named inverse,
  and the continuity and inverse laws on the two sets.
* **`lem:skeleton-crosscuts` + `prop:skeleton-agreement`** enter as
  `Schoenflies.HasAnchorCrosscuts`: for two distinct anchors `a, b` a crosscut `P` of `C` from
  `a` to `b`, a crosscut `P'` of `Q°` from `u a` to `u b`, and the agreement
  `F '' (P ∖ {a,b}) = P' ∖ {u a, u b}`. This is exactly what the finite skeleton homeomorphism
  produces once `Graph.IsStageOn.exists_crosscut` has been run in the stage containing `a`
  and `b` (see `Graph.IsStageOn.exists_isCrosscut` below, which does the packaging).
* **`lem:anchor-density`** enters as the two clauses `𝒜 ⊆ C` and `C ⊆ closure 𝒜`, plus its
  "incident with a nonboundary edge" clause in the germ form `Schoenflies.HasSpokes`: at an
  anchor `c`, arbitrarily small connected pieces `J` of the Jordan domain which cling to `c`
  and whose `F`-images cling to `u c`. That is the initial subarc of the spoke at `c`, and its
  image, which is the initial subarc of the target spoke — the *only* use the blueprint makes
  of the spokes, in the paragraph of `lem:crosscut-side-correspondence` beginning "Choose
  `c ∈ 𝒜` in the relative interior of `Aᵢ`".

`Schoenflies.HasLimitHomeomorphism` bundles the four over all curves, and
`Schoenflies.squareExtension_of_hasLimitHomeomorphism` derives
`Schoenflies.SquareExtension` — the exact `def` of
`Schoenflies/Endgame.lean` — from it. The proof of `HasLimitHomeomorphism` assembled in
`Schoenflies/JordanSchoenflies.lean` closes the full theorem.

## The two arguments

*Which side maps to which side* is `Schoenflies.crosscut_side_correspondence`. The homeomorphism
of the interiors carries `Int(C) ∖ P` onto `Q° ∖ P'` (`Schoenflies.image_inside_sdiff`), hence
carries each of the two components onto one of the two; the labels are pinned by a spoke germ
`J` at an anchor `c` in the relative interior of `A₁`. `J` is connected, misses `P` because it
is small and `c ∉ P`, so it lies in one side; `c ∈ closure J` and `closure(Uᵢ) ∩ C = Aᵢ` force
that side to be `U₁`. The same two facts on the target, applied to `F '' J`, force `F '' U₁` to
be `U'₁`.

*Boundary continuity* is `Schoenflies.tendsto_nhdsWithin_inside`. The blueprint argues on a
subsequence; the filter form of the same argument avoids extracting one. If `F` does not tend
to `u p` along `𝓝[Int C] p`, then `l' = 𝓝[Int C] p ⊓ 𝓟 (F⁻¹ Wᶜ)` is a nonzero filter for some
open `W ∋ u p`, and compactness of `Q` gives a cluster point `q ∈ Wᶜ` of `F` along `l'`. If
`q ∈ Q°` then pushing `l'` through `F'` shows `p = F' q ∈ Int(C)`, impossible. Otherwise
`q ∈ S`; anchors `a, b` separating `p` from `r = u⁻¹ q` give a crosscut whose `p`-side contains
every point of `Int(C)` near `p`, so `l'` sits on that side, so `q` lies in the closure of the
corresponding target side, whose trace on `S` is `u(A₁)` — and `r ∉ A₁`.

## Blueprint

* `Graph.IsStageOn.exists_isCrosscut` — **`lem:skeleton-crosscuts`** repackaged as
  `Schoenflies.IsCrosscut`, the form `thm:general-crosscut` consumes.
* `Schoenflies.IsCutPair.separates`, `Schoenflies.exists_separating_anchors` — the selection
  step of `prop:boundary-continuity`: two anchors putting two prescribed points of the curve on
  opposite arcs. Uses **`lem:anchor-density`** through the density hypothesis alone.
* `Schoenflies.IsCrosscut.image_of_injOn`, `Schoenflies.image_sdiff_eq_of_eqOn` — the two
  steps a consumer performs to discharge `Schoenflies.HasAnchorCrosscuts` from a finite skeleton
  homeomorphism. No blueprint statement of their own; they are the second paragraph of the
  proof of **`lem:skeleton-crosscuts`**, "the finite skeleton homeomorphism sends `P` to a
  simple path `P'`".
* `Schoenflies.crosscut_side_correspondence` — **`lem:crosscut-side-correspondence`**.
* `Schoenflies.extendByBoundary`, `Schoenflies.tendsto_nhdsWithin_inside`,
  `Schoenflies.boundary_continuity` — **`prop:boundary-continuity`**.
* `Schoenflies.isHomeoOn_extendByBoundary`,
  `Schoenflies.squareExtension_of_hasLimitHomeomorphism` —
  **`thm:square-extension`**.
-/

open Bornology Filter Metric Schoenflies Set Topology
open scoped _root_.Graph

namespace Schoenflies

variable {C 𝒜 A₁ A₂ B₁ B₂ P P' : Set Plane} {u v F F' : Plane → Plane} {a b p r : Plane}

/-! ### Two elementary facts about the model square

`Q° = Int(S)`: the open square is the Jordan domain of the model curve. This is the bridge
between the shape `prop:interior-homeomorphism` is stated in (a homeomorphism onto
`Plane.openSquare 0 1`) and the shape `thm:general-crosscut` speaks in (`inside modelCurve`). -/

/-- The closed square is compact. -/
theorem isCompact_closedSquare (c : Plane) (r : ℝ) : IsCompact (Plane.closedSquare c r) :=
  Metric.isCompact_of_isClosed_isBounded (Plane.isClosed_closedSquare c r)
    (Plane.isBounded_closedSquare c r)

/-! ### Pushing arcs forward

`lem:crosscut-side-correspondence` labels the target sides by `u(A₁)` and `u(A₂)`, so the two
target arcs have to be produced as images. Nothing here is specific to the square. -/

/-! ### Anchors that separate

The selection step of `prop:boundary-continuity`. Given two distinct points `p, r` of the curve
and a dense set `𝒜` of anchors, we need anchors `a, b` with `p` and `r` on opposite arcs of `C`
from `a` to `b`. Density produces one anchor on each of the two open arcs of `C` from `p` to
`r`; the separation is then automatic, because an arc from `a` to `b` avoiding `p` and `r`
would be a connected subset of `C ∖ {p, r}` meeting both of its two (relatively open) halves. -/

/-! ### The hypotheses

Two predicates, one for each thing that is still being built. Both are *statements about one
curve*, so a consumer can discharge them curve by curve. -/

/-! ### Discharging `HasAnchorCrosscuts` from a skeleton homeomorphism

The two steps a consumer has to perform, isolated so that they need not be reinvented: the
image of a crosscut under the finite skeleton homeomorphism is again a crosscut, and the
agreement clause follows from agreement of the limit map with that homeomorphism on the
crosscut. Neither says anything about the square, so both apply to the source and the target
side of any of the stages. -/

/-! ### `lem:crosscut-side-correspondence` -/

/-! ### `prop:boundary-continuity` -/

/-! ### `thm:square-extension` -/

/-! ### The assembled hypothesis, and `Schoenflies.SquareExtension` -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereCircleEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy transport through a metric-conformal sphere map

On the finite charts, the actual sphere map and actual intrinsic circle
coordinate satisfy the Dirichlet change-of-variables formula. The source
set may be any measurable part of a mask or of a localized tail.
-/

open Set Filter Matrix MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem integral_circleEnergy_metric_sphere_map
    {s W : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hW : IsOpen W)
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hsU : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef)
    (hfinite : ∀ x ∈ s, f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty)
    (hmap : MapsTo (sphereRealMap f) s W)
    (u : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u W) :
    (∫ y in sphereRealMap f '' s, fieldEnergy (circleGradient u) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient (u ∘ sphereRealMap f)) g x := by
  classical
  have hdata (x : ℝ × ℝ) (hx : x ∈ s) :=
    metric_conformal_real_chart (hf _ (hsU x hx)) (hg x hx) (hfinite x hx)
  let c (x : ℝ × ℝ) : ℝ := if hx : x ∈ s then (hdata x hx).2.2.choose else 1
  apply integral_circleEnergy_change_variables hs hW (sphereRealMap f)
    (fun x => fderiv ℝ (sphereRealMap f) x)
    (fun x hx => (hdata x hx).1.hasFDerivAt)
    (sphereRealMap_injOn hinj hsU hfinite)
    (fun x hx => (hdata x hx).2.1.ne') hmap u hu g c
  · intro x hx
    simpa only [c, dite_eq_left hx] using (hdata x hx).2.2.choose_spec.1
  · intro x hx
    simpa only [c, dite_eq_left hx] using (hdata x hx).2.2.choose_spec.2

/-- The same formula for a source coordinate identified locally with the
pullback. This is the equality used for the filled coordinates. -/
theorem integral_filled_circleEnergy_metric_sphere_map
    {s W : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hW : IsOpen W)
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hsU : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef)
    (hfinite : ∀ x ∈ s, f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty)
    (hmap : MapsTo (sphereRealMap f) s W)
    (u F : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u W)
    (hcoordinate : ∀ x ∈ s, (u ∘ sphereRealMap f) =ᶠ[𝓝 x] F) :
    (∫ y in sphereRealMap f '' s, fieldEnergy (circleGradient u) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient F) g x := by
  refine (integral_circleEnergy_metric_sphere_map hs hW hinj hsU hf hg hfinite hmap u hu).trans ?_
  apply setIntegral_congr_fun hs
  intro x hx
  simp only [fieldEnergy, circleGradient_congr_of_eventuallyEq (hcoordinate x hx)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_NormalizedCircleEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy transport for circle models fixing infinity

Fixing infinity eliminates the exceptional target point from the finite
chart. Thus the change-of-variables formula applies on every measurable
source set in the finite chart, including the whole localized tail.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem integral_filled_circleEnergy_normalized_sphere_map
    {s W : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hW : IsOpen W)
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hU : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hsU : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef)
    (hmap : MapsTo (sphereRealMap f) s W)
    (u F : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u W)
    (hcoordinate : ∀ x ∈ s, (u ∘ sphereRealMap f) =ᶠ[𝓝 x] F) :
    (∫ y in sphereRealMap f '' s, fieldEnergy (circleGradient u) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient F) g x :=
  integral_filled_circleEnergy_metric_sphere_map hs hW hinj hsU hf hg
    (fun x hx => finite_image_of_fixes_infty hinj hU hfix (hsU x hx)) hmap u F hu hcoordinate

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TransportedCircleCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual pushed-forward circle coordinates

A smooth coordinate on an open part of the source is composed with the
actual inverse of a normalized smooth sphere equivalence. Its target
domain is the actual image of that source region. It is smooth there,
its pullback is locally the original coordinate, and the full
Dirichlet change-of-variables formula follows.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem transported_circle_coordinate
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (hequiv : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → UnitAddCircle) (hF : SmoothCircleOn F O) :
    let W := sphereRealMap f '' O
    let v := F ∘ sphereRealMap fi
    IsOpen W ∧ SmoothCircleOn v W ∧
      (∀ x ∈ O, (v ∘ sphereRealMap f) =ᶠ[𝓝 x] F) := by
  dsimp only
  refine ⟨hequiv.isOpen_real_image hUinf hfix hV hO hOU, ?_, ?_⟩
  · apply smoothCircleOn_comp hF
    · rintro y ⟨x, hx, rfl⟩
      exact hequiv.real_smooth_inv hUinf hfix ((hequiv.real_bijOn hUinf hfix).mapsTo (hOU hx))
    · rintro y ⟨x, hx, rfl⟩
      rwa [hequiv.real_left_inv hUinf hfix (hOU hx)]
  · intro x hx
    filter_upwards [hO.mem_nhds hx] with y hy
    change F (sphereRealMap fi (sphereRealMap f y)) = F y
    rw [hequiv.real_left_inv hUinf hfix (hOU hy)]

theorem integral_transported_circle_coordinate
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (hequiv : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → UnitAddCircle) (hF : SmoothCircleOn F O)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsO : s ⊆ O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef) :
    (∫ y in sphereRealMap f '' s,
      fieldEnergy (circleGradient (F ∘ sphereRealMap fi)) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient F) g x := by
  obtain ⟨hW, hv, hpull⟩ := transported_circle_coordinate hequiv hV hUinf hfix hO hOU F hF
  exact integral_filled_circleEnergy_normalized_sphere_map hs hW hequiv.bijOn.injOn
    hUinf hfix (fun x hx => hOU (hsO hx)) hf hg
    (fun x hx => mem_image_of_mem _ (hsO hx)) (F ∘ sphereRealMap fi) F hv
    (fun x hx => hpull x (hsO hx))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_TransportedRealCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real barrier coordinates on normalized circle models

Real coordinates are transported by the actual smooth inverse. The
ordinary real gradient has the same energy as its intrinsic circle
differential, so the proved change-of-variables formula applies without
discarding the real lift or its values.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem transported_real_coordinate
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F O) :
    IsOpen (sphereRealMap f '' O) ∧
      ContDiffOn ℝ ∞ (F ∘ sphereRealMap fi) (sphereRealMap f '' O) ∧
      ∀ x ∈ O, ((F ∘ sphereRealMap fi) ∘ sphereRealMap f) =ᶠ[𝓝 x] F := by
  refine ⟨heq.isOpen_real_image hUinf hfix hV hO hOU, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    have hix : sphereRealMap fi (sphereRealMap f x) ∈ O := by
      rwa [heq.real_left_inv hUinf hfix (hOU hx)]
    exact ((hF.contDiffAt (hO.mem_nhds hix)).comp _
      (heq.real_smooth_inv hUinf hfix ((heq.real_bijOn hUinf hfix).mapsTo (hOU hx)))).contDiffWithinAt
  · intro x hx
    filter_upwards [hO.mem_nhds hx] with y hy
    change F (sphereRealMap fi (sphereRealMap f y)) = F y
    rw [heq.real_left_inv hUinf hfix (hOU hy)]

theorem integral_transported_real_coordinate
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F O)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsO : s ⊆ O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef) :
    (∫ y in sphereRealMap f '' s, gradientEnergy (F ∘ sphereRealMap fi) (fun _ => 1) y) =
      ∫ x in s, gradientEnergy F g x := by
  obtain ⟨hW, hv, _⟩ := transported_real_coordinate heq hV hUinf hfix hO hOU F hF
  have himage : MeasurableSet (sphereRealMap f '' s) :=
    hs.image_of_continuousOn_injOn
      (fun x hx => (heq.real_smooth hUinf hfix (hOU (hsO hx))).continuousAt.continuousWithinAt)
      ((heq.real_bijOn hUinf hfix).injOn.mono (hsO.trans hOU))
  have henergy := integral_transported_circle_coordinate heq hV hUinf hfix hO hOU
    (fun x => (F x : UnitAddCircle)) (smoothCircleOn_coe hO hF) hs hsO hf hg
  calc
    _ = ∫ y in sphereRealMap f '' s,
        fieldEnergy (circleGradient ((fun x => (F x : UnitAddCircle)) ∘ sphereRealMap fi))
          (fun _ => 1) y := by
      apply setIntegral_congr_fun himage
      intro y hy
      have hyW : y ∈ sphereRealMap f '' O := image_mono hsO hy
      have hd := circleGradient_coe_eq_planarGradient hW hv hyW
      change covectorEnergy _ _ = covectorEnergy _ _
      rw [show circleGradient ((fun x => (F x : UnitAddCircle)) ∘ sphereRealMap fi) y =
        planarGradient (F ∘ sphereRealMap fi) y from hd]
    _ = ∫ x in s, fieldEnergy (circleGradient (fun y => (F y : UnitAddCircle))) g x := henergy
    _ = _ := by
      apply setIntegral_congr_fun hs
      intro x hx
      change covectorEnergy _ _ = covectorEnergy _ _
      rw [circleGradient_coe_eq_planarGradient hO hF (hsO hx)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_EnergyTransportIntegrability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability in the metric energy change of variables

The Jacobian theorem gives integrability equivalence as well as equality
of integrals. This supplies the target finite-energy hypotheses required
by parallel-line payment from the actual source energy estimates.
-/

open Set Function Filter Matrix MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem integrable_filled_circleEnergy_metric_sphere_map_iff
    {s W : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hW : IsOpen W)
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hsU : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef)
    (hfinite : ∀ x ∈ s, f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty)
    (hmap : MapsTo (sphereRealMap f) s W)
    (u F : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u W)
    (hcoordinate : ∀ x ∈ s, (u ∘ sphereRealMap f) =ᶠ[𝓝 x] F) :
    IntegrableOn (fieldEnergy (circleGradient u) (fun _ => 1)) (sphereRealMap f '' s) ↔
      IntegrableOn (fieldEnergy (circleGradient F) g) s := by
  classical
  have hdata (x : ℝ × ℝ) (hx : x ∈ s) :=
    metric_conformal_real_chart (hf _ (hsU x hx)) (hg x hx) (hfinite x hx)
  let c (x : ℝ × ℝ) : ℝ := if hx : x ∈ s then (hdata x hx).2.2.choose else 1
  have heq := integrable_circleEnergy_change_variables_iff hs hW (sphereRealMap f)
    (fun x => fderiv ℝ (sphereRealMap f) x)
    (fun x hx => (hdata x hx).1.hasFDerivAt)
    (sphereRealMap_injOn hinj hsU hfinite)
    (fun x hx => (hdata x hx).2.1.ne') hmap u hu g c
    (fun x hx => by simpa only [c, dite_eq_left hx] using (hdata x hx).2.2.choose_spec.1)
    (fun x hx => by simpa only [c, dite_eq_left hx] using (hdata x hx).2.2.choose_spec.2)
  refine heq.trans (integrableOn_congr_fun ?_ hs)
  intro x hx
  simp only [fieldEnergy, circleGradient_congr_of_eventuallyEq (hcoordinate x hx)]

theorem integrable_transported_real_coordinate_iff
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F O)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsO : s ⊆ O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef) :
    IntegrableOn (gradientEnergy (F ∘ sphereRealMap fi) (fun _ => 1))
      (sphereRealMap f '' s) ↔ IntegrableOn (gradientEnergy F g) s := by
  obtain ⟨hW, hv, hpull⟩ := transported_real_coordinate heq hV hUinf hfix hO hOU F hF
  have himage : MeasurableSet (sphereRealMap f '' s) :=
    hs.image_of_continuousOn_injOn
      (fun x hx => (heq.real_smooth hUinf hfix (hOU (hsO hx))).continuousAt.continuousWithinAt)
      ((heq.real_bijOn hUinf hfix).injOn.mono (hsO.trans hOU))
  have henergy := integrable_filled_circleEnergy_metric_sphere_map_iff hs hW
    heq.bijOn.injOn (fun x hx => hOU (hsO hx)) hf hg
    (fun x hx => finite_image_of_fixes_infty heq.bijOn.injOn hUinf hfix (hOU (hsO hx)))
    (fun x hx => mem_image_of_mem _ (hsO hx))
    (fun x => ((F ∘ sphereRealMap fi) x : UnitAddCircle))
    (fun x => (F x : UnitAddCircle)) (smoothCircleOn_coe hW hv)
    (fun x hx => (hpull x (hsO hx)).fun_comp (fun t : ℝ => (t : UnitAddCircle)))
  calc
    _ ↔ IntegrableOn (fieldEnergy
        (circleGradient (fun x => ((F ∘ sphereRealMap fi) x : UnitAddCircle)))
        (fun _ => 1)) (sphereRealMap f '' s) := by
      apply integrableOn_congr_fun _ himage
      intro y hy
      change covectorEnergy _ _ = covectorEnergy _ _
      rw [circleGradient_coe_eq_planarGradient hW hv (image_mono hsO hy)]
    _ ↔ IntegrableOn (fieldEnergy (circleGradient (fun x => (F x : UnitAddCircle))) g) s :=
      henergy
    _ ↔ _ := by
      apply integrableOn_congr_fun _ hs
      intro x hx
      change covectorEnergy _ _ = covectorEnergy _ _
      rw [circleGradient_coe_eq_planarGradient hO hF (hsO hx)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TransportedRealEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-chart energy of the actual transported real function

Both integrability and the energy identity follow from the Jacobian
formula. Restriction to the bounded disk used by line payment only
decreases this energy.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem transported_real_energy
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (w : (ℝ × ℝ) → ℝ) (hw : ContDiffOn ℝ ∞ w (realChartDomain U))
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain U, (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain U)) :
    ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
        (((↑) : ℂ → Sphere) ⁻¹' V) ∧
      IntegrableOn (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
        (((↑) : ℂ → Sphere) ⁻¹' V) ∧
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' V),
        euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) =
        ∫ x in realChartDomain U, gradientEnergy w g x := by
  have hO := isOpen_realChartDomain hU
  have hW := isOpen_realChartDomain hV
  have himage := (heq.real_bijOn hUinf hfix).image_eq
  obtain ⟨_, hsmooth, _⟩ := transported_real_coordinate heq hV hUinf hfix hO
    (Subset.refl _) w hw
  rw [himage] at hsmooth
  have hi' := (integrable_transported_real_coordinate_iff heq hV hUinf hfix
    hO (Subset.refl _) w hw hO.measurableSet (Subset.refl _) hf hg).mpr hi
  rw [himage] at hi'
  have hdomain : Complex.equivRealProdCLM ⁻¹' realChartDomain V =
      ((↑) : ℂ → Sphere) ⁻¹' V := by
    ext z
    simp only [mem_preimage, realChartDomain, ContinuousLinearEquiv.symm_apply_apply]
  have hsmooth1 : ContDiffOn ℝ 1 (w ∘ sphereRealMap fi) (realChartDomain V) :=
    hsmooth.of_le (by norm_num)
  obtain ⟨hci, hce⟩ := real_gradient_energy_in_complex_coordinates hW hW.measurableSet
    (Subset.refl _) hsmooth1 hi'
  rw [hdomain, ← transported_sphereRealFunction_eq] at hci hce
  refine ⟨?_, hci, hce.trans ?_⟩
  · rw [transported_sphereRealFunction_eq, ← hdomain]
    exact hsmooth1.comp Complex.equivRealProdCLM.contDiff.contDiffOn (fun _ hz => hz)
  · have hid := integral_transported_real_coordinate heq hV hUinf hfix hO
      (Subset.refl _) w hw hO.measurableSet (Subset.refl _) hf hg
    rwa [himage] at hid

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real tests used by the countable selection. Compatibility is
with every finite sublist of previously selected tests, retaining repetitions. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace UngatedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}


def openEnds (c : UngatedRealTest d π EStar) : Set d.dust := Subtype.val ⁻¹' c.region

def of_barrier {previous : ℕ → PhysicalRealCoordinate d π} {flags : Set Sphere}
    {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere}
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ)
    (hopen : IsOpen (regions R.level)) : UngatedRealTest d π EStar where
  coordinate := R.coordinate
  region := regions R.level
  region_open := hopen
  zero := R.zero
  one := fun x hx => R.one x ⟨subset_closure hx.1, hx.2⟩
  exclusions := R.exclusions
  exclusions_countable := R.exclusions_countable
  weight := R.weight
  weight_finite := R.weight_finite
  weight_support := R.weight_support
  band_bound := R.band_bound

end UngatedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealTestLevelData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected real tests supply the actual level graphs and their
square-summable incidence weights for the next positive-law application. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

def realTestLevelData (d : PathCodeData Sphere Sphere) {π : Sphere → Sphere}
    {EStar : Set Sphere} (c : ℕ → UngatedRealTest d π EStar) : PathCodeData Sphere Sphere :=
  {d with
    levels := fun i => Prod.swap ⁻¹' circleBandGraph d.quotientDomain (c i).coordinate.quotient
    levelWeights := fun i => d.dust.indicator (c i).weight}

namespace realTestLevelData
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
  (c : ℕ → UngatedRealTest d π EStar)

def previous (i : ℕ) : PhysicalRealCoordinate (realTestLevelData d c) π :=
  (c i).coordinate.rebase rfl rfl

end realTestLevelData

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableUncoveredTestEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The greedy selection of tests misses only countably many ends at each
accuracy, by the positive-law recursion and alternating disk crossings. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def uncoveredTestEnds {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {EStar : Set Sphere} (A : Set (GradedRealTest d π EStar)) (k : ℕ) : Set Sphere :=
  {p | p ∈ d.dust ∧ ∀ b ∈ A, b.grade = k → p ∉ b.region}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayTranslates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Different integer translates of a lifted simple disk arc are disjoint. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def translatedDiskRay (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (k : ℤ) : C(DiskRayTime, ℝ × ℝ) :=
  ⟨fun t => (diskRayAngle γ hi he t + (k : ℝ), diskRayDepth γ t),
    ((continuous_diskRayAngle γ hi he).add continuous_const).prodMk
      (continuous_diskRayDepth γ hi he)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricIndexLocal
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local constancy of the greatest-translate index follows from the common
finite strip bound and local constancy of each of the finitely many relevant sides. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def rayIndexSide (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (z : RayIndexDomain γ hγ) : Bool :=
  (translatedHalfPlaneRay γ hγ k).side (rayJordan hsch γ hγ k)
    ⟨halfPlaneDisk z.val, Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le z.property.1), z.property.2 k⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LiftedMeanContinuity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous local representatives of the geometric mean index.
Point avoidance is transported through the actual injective Jordan map. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 def liftedMeanGeometricIndex (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (Ψ : ℂ → ℂ) (z : ℂ) : ℝ :=
  if h : 0 ≤ (Ψ z).im then meanGeometricIndex hsch K hKS η ⟨Ψ z, h⟩ else 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanCollar
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth inward collars for regular Jordan boundaries.

Published input: J. M. Lee, Introduction to Smooth Manifolds, second edition
(2013), Theorem 9.25, pp.222--223 (Collar Neighborhood Theorem), together with
its regular-domain interpretation in Proposition5.47, p.121. The formulation
below is the compact planar Jordan-boundary specialization: parametrize the
boundary circle (Milnor's compact one-manifold classification), take inward
collar slices, and use their bounded Jordan sides (planar Schoenflies).
It is a specialization/corollary, not a verbatim transcription of Theorem9.25.
The continuous-tangent clause retains the C¹ dependence of its smooth
collar embedding and is used only for the uniform boundary variation bound.
The regular-level hypothesis is retained explicitly.
https://thunv.wordpress.com/wp-content/uploads/2015/09/graduate-texts-in-mathematics-vol-218-john-m-lee-introduction-to-smooth-manifolds-springer-2013.pdf
DOI: 10.1007/978-1-4419-9982-5.
-/

open Set Function Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

/-- Explicit published-input parameter: the regular-level planar Jordan
specialization of the collar-neighborhood theorem described above. -/
def SmoothRegularJordanCollars : Prop :=
  ∀ (H : ℂ ≃ₜ ℂ) (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
    IsPlanarRegularValue f t → frontier (jordanInterior H) ⊆ {z | f z = t} →
    Nonempty (RegularJordanInwardCollar H)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedLevelData
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual marked band widths supply the level weights for the next
endpoint-law construction. This uses the full dust as a temporary label
set; the common countable mark restriction is performed after selection. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_21
def maskedLevelData (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : ℕ → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)) : PathCodeData Sphere Sphere :=
  { d with
    levels := fun i => Prod.swap ⁻¹' (C i).graph
    levelWeights := fun i => (C i).dustWeight }

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealSeedPresentation
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real barriers used as the seed already vanish on the anchor
neighborhood of infinity. This gives the compact support required by the
later generic-level estimates, with the identical quotient coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 def UngatedRealTest.levelPresentation
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    (R : UngatedRealTest d π EStar)
    (hπ : Continuous π) (hinfty : π OnePoint.infty ∈ interior EStar)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (hgraph : C.graph = circleBandGraph d.quotientDomain R.coordinate.quotient)
    (hmask : C.mask = univ)
    (hphysical : ∀ x, (R.coordinate.physical x : UnitAddCircle) = C.physical x)
    (hwidth : ∀ s, C.upper s - C.lower s =
      limsup R.coordinate.quotient (𝓝[d.quotientDomain] s.val) -
        liminf R.coordinate.quotient (𝓝[d.quotientDomain] s.val)) :
    RealCoordinatePresentation d π C where
  coordinate := R.coordinate
  graph_eq := hgraph
  mask_eq_univ := hmask
  physical_eq := hphysical
  band_width := hwidth
  compactSupport := ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' interior EStar)ᶜ
  isCompact_support := isCompact_finite_preimage
    (isOpen_interior.preimage hπ).isClosed_compl (fun h => h hinfty)
  zero_off := by
    intro z _ hz
    apply R.zero
    apply interior_subset
    by_contra hn
    exact hz hn
  zero_infty := fun _ => R.zero _ (interior_subset hinfty)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SelectableMaskedCoordinate
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected coordinate retains the precise level and flag data needed
for a later endpoint-law construction. Weighted coarea is proved for the
actual physical mean before placing it in this interface. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

def CompatibleWith (c : SelectableMaskedCoordinate d π)
    (A : Set (SelectableMaskedCoordinate d π)) : Prop :=
  (∀ a ∈ A, a.flags ⊆ c.flags) ∧
  ∀ (n : ℕ) (q : Fin n → SelectableMaskedCoordinate d π), (∀ i, q i ∈ A) →
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ c.flags) c.coordinate.graph
        (fun i : Fin n => (q i).coordinate.graph) id) = 0

local instance localInst_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
def priorLevels (c : ℕ → SelectableMaskedCoordinate d π) :
    PriorLevelFamily d.physicalDomain π where
  graph i := (c i).coordinate.graph
  closed i := (c i).coordinate.graph_closed
  weighted i := (c i).weighted

def pathData (c : ℕ → SelectableMaskedCoordinate d π) : PathCodeData Sphere Sphere :=
  maskedLevelData d π (fun i => (c i).coordinate)

end SelectableMaskedCoordinate

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_OrderedMaskedSelection
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected mixed family retains the complete seed before the new
coordinates. Empty selection steps use the seed zero coordinate. The
resulting order has type omega plus omega, not a rearranged natural order. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 def orderedSelectedCoordinates {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π) {T : Type*}
    (data : T → SelectableMaskedCoordinate d π) (q : ℕ → Option T) :
    ℕ ⊕ₗ ℕ → SelectableMaskedCoordinate d π :=
  fun j => match ofLex j with
    | .inl n => seed n
    | .inr n => (q n).elim (seed 0) data

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteSeededRealFamily
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate a prescribed finite prefix before the greedily selected tests,
retaining the actual functions and their ordered level compatibility. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

def finiteSeededRealFamily
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (q : ℕ → Option (GradedRealTest d π EStar)) (n : ℕ) : UngatedRealTest d π EStar :=
  if h : n < m + 1 then seed ⟨n, h⟩
  else (q (n - (m + 1))).elim (seed 0) GradedRealTest.toUngatedRealTest

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SeededMaskedSelection
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable open selection retains every seed and the actual order of
later masked coordinates. Its cover assertion concerns every candidate
compatible with the final list; geometric availability is proved separately. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 def seededMaskedAllowed {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π) {T : Type*}
    (data : T → SelectableMaskedCoordinate d π) (A : Set T) (c : T) : Prop :=
  (data c).CompatibleWith (range seed ∪ data '' A)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealPresentationTransfer
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain every selected real presentation in the mixed transfer, including
real barriers chosen after the initial seed. Its physical function and
actual marked band widths are the same ones used by the selection. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem PhysicalRealCoordinate.boundary_width_le_one
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (Q : PhysicalRealCoordinate d π) (hdense : Dense d.quotientDomain) (x : Sphere) :
    limsup Q.quotient (𝓝[d.quotientDomain] x) -
      liminf Q.quotient (𝓝[d.quotientDomain] x) ≤ 1 := by
  have hcl : x ∈ closure d.quotientDomain := by rw [hdense.closure_eq]; trivial
  let : NeBot (𝓝[d.quotientDomain] x) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hlo : 0 ≤ liminf Q.quotient (𝓝[d.quotientDomain] x) :=
    le_liminf_of_le (isBoundedUnder_of_eventually_le
      (Eventually.of_forall fun y => (Q.quotient_unit y).2)).isCoboundedUnder_ge
      (Eventually.of_forall fun y => (Q.quotient_unit y).1)
  have hhi : limsup Q.quotient (𝓝[d.quotientDomain] x) ≤ 1 :=
    limsup_le_of_le (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun y => (Q.quotient_unit y).1)).isCoboundedUnder_le
      (Eventually.of_forall fun y => (Q.quotient_unit y).2)
  linarith

 theorem RealCoordinatePresentation.width_le
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)}
    (R : RealCoordinatePresentation d π C) (hdense : Dense d.quotientDomain) (s : d.dust) :
    limsup R.coordinate.quotient (𝓝[d.quotientDomain] s.val) -
      liminf R.coordinate.quotient (𝓝[d.quotientDomain] s.val) ≤ C.upper s - C.lower s := by
  apply (ENNReal.ofReal_le_ofReal_iff (C.width_nonneg s)).mp
  apply band_width_le_of_fiber_subset (M := 1)
    (fun x _ => by
      rw [abs_of_nonneg (R.coordinate.quotient_unit x).1]
      exact (R.coordinate.quotient_unit x).2)
    (by rw [hdense.closure_eq]; trivial) (R.coordinate.boundary_width_le_one hdense s.val)
  intro θ hθ
  apply C.marked_fiber s
  rwa [R.graph_eq]

 def realSubfamily_of_presentations
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {L A : Type*}
    (C : L → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (ι : A → L) (R : ∀ j, RealCoordinatePresentation d π (C (ι j)))
    (hdense : Dense d.quotientDomain) : RealCoordinateSubfamily C ι where
  physical j := (R j).coordinate.physical
  quotient j := (R j).coordinate.quotient
  bound _ := 1
  bounded j x _ := by
    rw [abs_of_nonneg ((R j).coordinate.quotient_unit x).1]
    exact ((R j).coordinate.quotient_unit x).2
  full_mask j := (R j).mask_eq_univ
  smooth j := (R j).coordinate.physical_smooth
  energy j := (R j).coordinate.physical_energy
  pullback j x hx := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      ((R j).coordinate.pullback (Complex.equivRealProdCLM.symm x) hx).symm
  projection j x := (R j).physical_eq x
  width j s := (R j).width_le hdense s

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SeededLevelPresentations
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carry the actual real or mean presentation through the ordered selection, including
unused slots filled by the original zero coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 def orderedSelectedPresentations
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (seedPresentation : ∀ n, RealCoordinatePresentation d π (seed n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (presentation : ∀ t, SelectedLevelPresentation hsch d π (data t).coordinate)
    (q : ℕ → Option T) : ∀ j : ℕ ⊕ₗ ℕ,
      SelectedLevelPresentation hsch d π (orderedSelectedCoordinates seed data q j).coordinate := by
  intro j
  induction j using Lex.rec with
  | h j =>
    cases j with
    | inl n => exact Sum.inl (seedPresentation n)
    | inr n =>
      change SelectedLevelPresentation hsch d π ((q n).elim (seed 0) data).coordinate
      exact match q n with
        | none => Sum.inl (seedPresentation 0)
        | some t => presentation t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PresentedRealCoordinates
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic real family for a mixed model needs no artificial natural-number ordering.
Its actual band widths and functions are obtained from the selected presentations; finite
stages retain the inherited order of the whole mixed family. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 def realCoordinatesFromPresentations
    (base : PathCodeData Sphere Sphere) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    {L : Type*} (C : L → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val)) (ι : ℕ → L)
    (R : ∀ n, RealCoordinatePresentation base π (C (ι n)))
    (A : Set base.dust)
    (hsupport : ∀ l s, (C l).upper s - (C l).lower s ≠ 0 → s ∈ A) :
    CountableRealCoordinates base.physicalDomain π (fun s : A => s.val.val) := by
  let lo (n : ℕ) (s : Sphere) := liminf (R n).coordinate.quotient (𝓝[base.quotientDomain] s)
  let hi (n : ℕ) (s : Sphere) := limsup (R n).coordinate.quotient (𝓝[base.quotientDomain] s)
  have hunit (n : ℕ) (x : Sphere) (_ : x ∈ base.quotientDomain) :
      |(R n).coordinate.quotient x| ≤ 1 := by
    rw [abs_of_nonneg ((R n).coordinate.quotient_unit x).1]
    exact ((R n).coordinate.quotient_unit x).2
  have hclosure (x : Sphere) : x ∈ closure base.quotientDomain := by
    rw [hdense.closure_eq]; trivial
  have hnn (n : ℕ) (s : Sphere) : 0 ≤ hi n s - lo n s :=
    boundary_width_nonneg (hunit n) (hclosure s)
  have hband (n : ℕ) (s : Sphere) :
      {t : ℝ | (s, t) ∈ intervalFiberHull
        (clusterGraph base.quotientDomain (R n).coordinate.quotient)} = Icc (lo n s) (hi n s) :=
    intervalFiberHull_clusterGraph_eq_boundary_band (hunit n) (hclosure s)
  refine {
    source := base.quotientDomain
    source_open := hU
    coordinate := fun n => (R n).coordinate.quotient
    coordinate_continuous := fun n => (R n).coordinate.quotient_continuous
    bound := fun _ => 1
    coordinate_bounded := hunit
    physical := fun n => (R n).coordinate.physical
    physical_measurable := fun n => (R n).coordinate.physical_measurable
    physical_smooth := fun n => (R n).coordinate.physical_smooth
    physical_energy := fun n => (R n).coordinate.physical_energy
    source_map := ?_
    pullback := fun n => (R n).coordinate.pullback
    labels_injective := Subtype.val_injective.comp Subtype.val_injective
    labels_dust := fun s => hB ▸ s.val.property
    labels_closure := fun s => hclosure s.val.val
    lower := fun n s => lo n s.val.val
    upper := fun n s => hi n s.val.val
    width_nonneg := fun n s => hnn n s.val.val
    width_summable := ?_
    band := fun n s => hband n s.val.val
    free_trace := ?_ }
  · intro z hz
    rw [← he ⟨(z : Sphere), hz⟩]
    exact (base.domainEquiv ⟨(z : Sphere), hz⟩).property
  · intro n
    apply ((C (ι n)).width_summable.subtype (· ∈ A)).congr
    intro s
    exact congrArg (fun t : ℝ => t ^ 2) ((R n).band_width s.val)
  · intro x hx hfree n
    have hxB : x ∈ base.dust := hB.symm ▸ hx
    have hnot : (⟨x, hxB⟩ : base.dust) ∉ A := by
      intro hxA
      exact hfree ⟨⟨⟨x, hxB⟩, hxA⟩, rfl⟩
    have hwidth : (C (ι n)).upper ⟨x, hxB⟩ - (C (ι n)).lower ⟨x, hxB⟩ = 0 := by
      by_contra hn
      exact hnot (hsupport _ _ hn)
    rw [(R n).band_width] at hwidth
    change hi n x - lo n x = 0 at hwidth
    refine ⟨lo n x, ?_⟩
    rw [hband, sub_eq_zero.mp hwidth, Icc_self]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SelectedMixedModels
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable selected family produces actual mixed finite models. Every chosen real
presentation, including a real barrier selected after the seed, is retained with its exact
physical and quotient functions. The finite coordinates keep the selected family's order. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

structure SelectedMixedModels
    (hsch : PlanarSchoenflies) (base : PathCodeData Sphere Sphere)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (π : Sphere → Sphere)
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    {L : Type*} [LinearOrder L]
    (D : L → SelectableMaskedCoordinate base π)
    (presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate)
    (B₀ : Set base.dust) where
  marks : Set base.dust
  marks_countable : marks.Countable
  mandatory : B₀ ⊆ marks
  flags : ∀ l x, x ∈ (D l).flags → x ∈ Subtype.val '' marks
  singular : ∀ l, (D l).coordinate.singular ∈ marks
  support : ∀ l s, (D l).coordinate.upper s - (D l).coordinate.lower s ≠ 0 → s ∈ marks
  realLabels : ℕ → L
  real_injective : Injective realLabels
  realPresentation : ∀ n, RealCoordinatePresentation base π (D (realLabels n)).coordinate
  real_selected : ∀ n, presentation (realLabels n) = Sum.inl (realPresentation n)
  real_cover : ∀ l (r : RealCoordinatePresentation base π (D l).coordinate),
    presentation l = Sum.inl r → ∃ n, realLabels n = l ∧
      (realPresentation n).coordinate.physical = r.coordinate.physical ∧
      (realPresentation n).coordinate.quotient = r.coordinate.quotient
  model : MixedModelExhaustion
    (realCoordinatesFromPresentations base hU hdense π he hB
      (fun l => (D l).coordinate) realLabels realPresentation marks support)
    (fun l => (D l).coordinate.restrictMarks marks (singular l) (support l)) realLabels
    (markedNeighborhoods (fun s : marks => s.val.val)) modelError modelError

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedMixedSmallness
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real seed's collapse estimates survive the common mixed construction, even when
its real coordinates are enumerated differently and further marked points are retained. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {L : Type*} [LinearOrder L] {D : L → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 def realCoordinates (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀) :
    CountableRealCoordinates base.physicalDomain π (fun s : F.marks => s.val.val) :=
  realCoordinatesFromPresentations base hU hdense π he hB
    (fun l => (D l).coordinate) F.realLabels F.realPresentation F.marks F.support

 def withRadius (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (R : ℝ) (hR : F.model.real.radius ≤ R) :
    SelectedMixedModels hsch base hU hdense π he hB D presentation B₀ :=
  { F with model := F.model.withRadius R hR }

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanIndexBoundary
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mean index has the previously constructed positive
Stieltjes boundary coordinate for the actual starting-angle law. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def compactArcStartingAngleLaw (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure K) :
    ProbabilityMeasure UnitAddCircle := η.map (f := (fun γ : K => normalizedArgument (γ.val 0)))
      (measurable_normalizedArgument.comp
        ((continuous_eval_const 0).comp continuous_subtype_val).measurable).aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OrderedCollarLift
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A jointly lifted physical collar, normalized at the boundary. All
fields below are constructed from the regular collar and its actual disk
coordinate; in particular, positive winding is not an input assumption. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

structure OrderedCollarLift {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    (F : C(Sphere, ℂ)) where
  start : ℝ
  reverse : Bool
  width : ℝ
  width_pos : 0 < width
  width_le : width ≤ C.width
  angle : ℝ ≃o ℝ
  angle_zero : angle 0 = 0
  angle_one : angle 1 = 1
  lift : ℝ × ℝ → ClosedUpperHalfPlane
  continuous : ContinuousOn lift (Ioo (-width) width ×ˢ univ)
  projects : ∀ p ∈ Ioo (-width) width ×ˢ (univ : Set ℝ),
    diskRayProjection (lift p).val =
      F (C.curve |p.1| (orientedParameter start reverse p.2) : Sphere)
  period : ∀ ρ ∈ Ioo (-width) width, lift (ρ, 1) = (lift (ρ, 0)).translate 1
  boundary : ∀ t ∈ Icc (0 : ℝ) 1, (lift (0, t)).val = (angle t : ℂ)
  approach : ∀ ε > 0, ∃ η > 0, η < width ∧ ∀ ρ ∈ Ioo (-η) η,
    ∀ t ∈ Icc (0 : ℝ) 1, dist (lift (ρ, t)).val (angle t : ℂ) < ε

namespace OrderedCollarLift

 def circuit {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) (ρ : ℝ) : ℝ → ℂ :=
  C.curve ρ ∘ orientedParameter D.start D.reverse

end OrderedCollarLift
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveMeanExclusion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact recursive positive law constructs an inner masked mean
and its open map--disk exclusion. Its energy and point-hit hypotheses are all
supplied by the law; only the geometric collar and prescribed gate are inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

structure RecursiveMeanOutput (hsch : PlanarSchoenflies)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    {L : RecursiveCodeLaw base π Flags ω} {J : ℂ ≃ₜ ℂ} {ε : ℝ≥0∞}
    (Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J) ε)
    (F₀ : ℂ → ℂ)
    (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain))
    (c : ℂ) (r : ℝ≥0) (R δ : ℝ) where
  centered : CenteredTerminalFamily J L.data.target Q.arcs
  mask : Set Sphere
  closed : IsClosed mask
  frontier : frontier mask ⊆ base.quotientDomain
  target_mem : L.data.target ∈ mask
  infty_not_mem : π OnePoint.infty ∉ mask
  inner : mask ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J
  mean : SmoothMeanPeriodData hsch centered.diskArcs centered.terminal
    (Q.law.map centered.continuous_arcMap.measurable.aemeasurable) centered.map base.physicalDomain base.quotientDomain
    centered.punctured mask L.data.target π
  coordinate : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)
  graph : coordinate.graph = periodBandGraph base.quotientDomain mask L.data.target
    mean.patch mean.branch
  mask_eq : coordinate.mask = mask
  singular_eq : (coordinate.singular : Sphere) = L.data.target
  budget : coordinate.sourceStokesBudget R < δ
  exclusion : MeanExclusionWitness coordinate F₀ hF₀ c r R

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RebasedLevelPresentations
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adding a target or prior law changes the code space, but preserves the
actual selected coordinates and their real/mean presentations. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]
variable {d e : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData d.physicalDomain d.quotientDomain π (fun x : d.dust => x.val)}

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_25
def SelectedLevelPresentation.rebase {hsch : PlanarSchoenflies}
    (R : SelectedLevelPresentation hsch d π C)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hB : e.dust = d.dust) :
    SelectedLevelPresentation hsch e π (C.rebaseDust hG hU hB) :=
  R.map (fun Q => Q.rebase hG hU hB) (fun Q => Q.rebase hG hU hB)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedCircleModel
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual graded real seed, countable open exclusion selection,
common mixed models and their normal limit into a circle uniformization. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

open FiniteTransfer

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_36
/-- A circle-domain normal limit with the original finite scalar list retained
on the actual finite-transfer exhaustion. Sobolev continuation of its traces
is a separate conclusion proved from these data. -/
structure RetainedRealCircleModel (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    {m : ℕ} (Q : Fin m → PhysicalRealCoordinate base π) where
  marks : Set base.dust
  marks_countable : marks.Countable
  coordinates : CountableRealCoordinates base.physicalDomain π (fun s : marks => s.val.val)
  source : coordinates.source = base.quotientDomain
  model : RealModelExhaustion coordinates
    (markedNeighborhoods (fun s : marks => s.val.val)) modelError
  limit : AssignedRealModelLimit model
  circle : IsCircleDomain (extendAtInfinity limit.function '' base.physicalDomain)
  index : Fin m → ℕ
  physical : ∀ i, coordinates.physical (index i) = (Q i).physical
  quotient : ∀ i, coordinates.coordinate (index i) = (Q i).quotient

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedScalarEstimates
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy and terminal oscillation estimates for the unchanged scalar tests
on the actual finite stages of the selected circle model. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_37
def transferred (i : Fin m) (n : ℕ) : ℂ → ℝ :=
  (sphereRealFunction ((R.model.stages n).functions (prefixIndex (R.index i) n)) ∘
    (R.model.stages n).inverse) ∘ ((↑) : ℂ → Sphere)

 theorem width_zero (i : Fin m) (hQ : Continuous (Q i).quotient) (s : R.marks) :
    R.coordinates.upper (R.index i) s - R.coordinates.lower (R.index i) s = 0 :=
  R.coordinates.width_zero_of_continuous (R.index i) (R.quotient i ▸ hQ) s

 theorem eventually_oscillation (i : Fin m) (hQ : Continuous (Q i).quotient) :
    ∀ᶠ n in atTop, Real.sqrt (∑' s : (R.model.stages n).indices,
      terminalOscillation ((R.model.stages n).terminals.H s)
        ((R.model.stages n).functions (prefixIndex (R.index i) n)) ^ 2) < modelError n := by
  filter_upwards [prefixIndex_eq (R.index i)] with n hn
  have ho := (R.model.stages n).oscillation (prefixIndex (R.index i) n)
  simpa only [hn, R.width_zero i hQ, zero_pow (by decide : 2 ≠ 0),
    tsum_zero, Real.sqrt_zero, zero_add] using ho

 theorem eventually_energy (i : Fin m) :
    ∀ᶠ n in atTop,
      IntegrableOn (euclideanGradientEnergy (R.transferred i n))
        (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) ∧
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain),
        euclideanGradientEnergy (R.transferred i n) z) <
      (∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + modelError n := by
  filter_upwards [prefixIndex_eq (R.index i)] with n hn
  let M := R.model.stages n
  let l := prefixIndex (R.index i) n
  let : Fintype M.indices := M.finite_indices.fintype
  obtain ⟨_, hi, he⟩ := transported_real_energy M.equivalence
    (isOpen_openCompletedRegion M.terminals.H) M.circle_domain.1 M.source_infty M.principal.1
    (M.functions l) (M.functions_smooth_source l) M.metric_conformal
    (fun x _ => M.metric_pos x) (M.functions_integrable_source l)
  have hs := M.source_energy_lt l
  rw [← he] at hs
  refine ⟨hi, ?_⟩
  simpa only [l, hn, R.physical i, M, transferred] using hs

 theorem eventually_retained (i : Fin m) {K : Set Sphere}
    (hK : IsCompact K) (hKG : K ⊆ d.physicalDomain) :
    ∀ᶠ n in atTop, ∀ z : ℂ, (z : Sphere) ∈ K →
      (R.model.stages n).functions (prefixIndex (R.index i) n) (Complex.equivRealProdCLM z) =
        (Q i).physical (Complex.equivRealProdCLM z) := by
  simpa only [R.physical i] using R.model.eventually_test_eq hK hKG (R.index i)

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ScalarHoleFillings
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constant values for the actual finite target holes. Every finite cluster
value differs from the chosen fill by at most the original terminal oscillation. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem TerminalComponentAssignment.exists_scalar_fill_values
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (heq : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (w : (ℝ × ℝ) → ℝ) {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O) :
    ∃ value : I → ℝ, ∀ i t,
      t ∈ componentClusterValues V (a.point i) (sphereRealFunction w ∘ fi) →
      |t - value i| ≤ terminalOscillation (T i) w := by
  have hne (i : I) : (frontier (realJordanInterior (T i))).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (T i)).nonempty
    refine ⟨Complex.equivRealProdCLM z, ?_⟩
    rw [frontier_realJordanInterior]
    exact mem_image_of_mem _ hz
  choose point hpoint using hne
  refine ⟨fun i => w (point i), ?_⟩
  intro i t ht
  have hsub := a.cluster_values_subset_boundary heq i (sphereRealFunction w) (by
    rintro _ ⟨z, hz, rfl⟩
    apply continuousAt_sphereRealFunction
    apply hw.continuousAt (hO.mem_nhds (hTO i ?_))
    rw [frontier_realJordanInterior]
    exact mem_image_of_mem _ hz)
  obtain ⟨_, ⟨z, hz, rfl⟩, hzt⟩ := hsub ht
  have hzt' : w (Complex.equivRealProdCLM z) = t := by
    simpa only [sphereRealFunction, finiteCoord_coe] using hzt
  have hz' : Complex.equivRealProdCLM z ∈ frontier (realJordanInterior (T i)) := by
    rw [frontier_realJordanInterior]
    exact mem_image_of_mem _ hz
  have hb := ((realJordanInterior_geometry (T i)).2.1.image_of_continuousOn
    (hw.mono (hTO i))).isBounded
  simpa only [terminalOscillation, Real.dist_eq, hzt'] using
    dist_le_diam_of_mem hb (mem_image_of_mem w hz') (mem_image_of_mem w (hpoint i))

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

local instance instBorelSpaceSphere_39_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
structure HoleFilling (i : Fin m) (n : ℕ) where
  center : (R.model.stages n).indices → ℂ
  radius : (R.model.stages n).indices → ℝ
  radius_nonneg : ∀ s, 0 ≤ radius s
  component : ∀ s, connectedComponentIn (R.model.stages n).domainᶜ
    ((R.limit.assignment n).point s) = ((↑) : ℂ → Sphere) '' closedBall (center s) (radius s)
  disjoint : Pairwise (Disjoint on fun s => closedBall (center s) (radius s))
  complement : ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain =
    (⋃ s, closedBall (center s) (radius s))ᶜ
  value : (R.model.stages n).indices → ℝ
  cluster_error : ∀ s t, t ∈ componentClusterValues (R.model.stages n).domain
    ((R.limit.assignment n).point s)
    (sphereRealFunction ((R.model.stages n).functions (prefixIndex (R.index i) n)) ∘
      (R.model.stages n).inverse) →
    |t - value s| ≤ terminalOscillation ((R.model.stages n).terminals.H s)
      ((R.model.stages n).functions (prefixIndex (R.index i) n))

 theorem exists_hole_filling (i : Fin m) (n : ℕ) : Nonempty (R.HoleFilling i n) := by
  let M := R.model.stages n
  let a := R.limit.assignment n
  obtain ⟨c, r, hr, he, hd, hcomp⟩ := a.exists_disk_coordinates M.circle_domain
    (M.equivalence.infty_mem_target M.source_infty M.principal.1)
  obtain ⟨v, hv⟩ := a.exists_scalar_fill_values M.equivalence
    (M.functions (prefixIndex (R.index i) n)) M.extension_open M.terminal_frontier_extension
    (M.functions_smooth (prefixIndex (R.index i) n)).continuousOn
  exact ⟨⟨c, r, hr, he, hd, hcomp, v, hv⟩⟩

 theorem HoleFilling.radius_sq_bound
    (harea : ExteriorCoefficientAreaTheorem) {i : Fin m} {n : ℕ}
    (F : R.HoleFilling i n) :
    ∑' s, F.radius s ^ 2 ≤ (3 * R.model.radius) ^ 2 := by
  let M := R.model.stages n
  let : Fintype M.indices := M.finite_indices.fintype
  have hbound := (normalized_model_uniform_bound harea M.equivalence M.circle_domain.1
    R.model.radius_pos ((R.model.exterior_core n).trans (R.model.core_model n))
    ((R.model.core_conformal n).mono
      ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (R.model.exterior_core n)))
    M.principal).1
  simpa only [tsum_fintype] using sum_radii_sq_le_of_disjoint_closed_disks F.center F.radius
    F.radius_nonneg (mul_nonneg (by norm_num) R.model.radius_pos.le) F.disjoint
    (fun s => terminal_disk_subset_bound (F.component s) hbound)

 theorem eventually_hole_cost_bound (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      (∑' s, F.radius s * terminalOscillation ((R.model.stages n).terminals.H s)
        ((R.model.stages n).functions (prefixIndex (R.index i) n))) <
      3 * R.model.radius * modelError n := by
  filter_upwards [R.eventually_oscillation i hQ] with n hn F
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  rw [tsum_fintype]
  have hrad : Real.sqrt (∑ s, F.radius s ^ 2) ≤ 3 * R.model.radius := by
    have h := F.radius_sq_bound R harea
    rw [tsum_fintype] at h
    exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq (mul_nonneg (by norm_num) R.model.radius_pos.le))
  refine (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ F.radius _).trans_lt ?_
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrad (Real.sqrt_nonneg _))
  apply mul_lt_mul_of_pos_left _ (mul_pos (by norm_num) R.model.radius_pos)
  simpa only [tsum_fintype] using hn

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_BoundedScalarFillings
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded measurable fillings on the whole plane, equal to the clipped
transferred scalar in the domain and constant on each actual round hole. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_40_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem transferred_continuousOn (i : Fin m) (n : ℕ) :
    ContinuousOn (R.transferred i n) (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
  rw [transferred, transported_sphereRealFunction_eq]
  exact ((R.model.stages n).transported_smooth (prefixIndex (R.index i) n)).continuousOn.comp
    Complex.equivRealProdCLM.continuous.continuousOn (fun z hz => by
      simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz)

namespace HoleFilling
variable {R} {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

local instance instBorelSpaceSphere_40_r5345e3_2 : BorelSpace Sphere := ⟨rfl⟩
def filled (z : ℂ) : ℝ :=
  (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).indicator
    (clipScalar ∘ R.transferred i n) z +
    ∑' s, (closedBall (F.center s) (F.radius s)).indicator (fun _ => clipScalar (F.value s)) z

theorem filled_on_domain {z : ℂ} (hz : (z : Sphere) ∈ (R.model.stages n).domain) :
    F.filled z = clipScalar (R.transferred i n z) := by
  have hnot : z ∉ ⋃ s, closedBall (F.center s) (F.radius s) := by
    rw [← mem_compl_iff, ← F.complement]
    exact hz
  have hzero : ∀ s, (closedBall (F.center s) (F.radius s)).indicator
      (fun _ => clipScalar (F.value s)) z = 0 := by
    intro s
    exact indicator_of_notMem (fun h => hnot (mem_iUnion.mpr ⟨s, h⟩)) _
  have hz' : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain := hz
  simp only [filled, indicator_of_mem hz', hzero, tsum_zero, add_zero, comp_apply]

theorem filled_on_hole (s : (R.model.stages n).indices) {z : ℂ}
    (hz : z ∈ closedBall (F.center s) (F.radius s)) : F.filled z = clipScalar (F.value s) := by
  have hnot : z ∉ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain := by
    rw [F.complement]
    exact fun h => h (mem_iUnion.mpr ⟨s, hz⟩)
  have hother : ∀ t ≠ s, (closedBall (F.center t) (F.radius t)).indicator
      (fun _ => clipScalar (F.value t)) z = 0 := by
    intro t hts
    exact indicator_of_notMem (fun ht => disjoint_left.mp (F.disjoint hts) ht hz) _
  rw [filled, indicator_of_notMem hnot, zero_add, tsum_eq_single s hother, indicator_of_mem hz]

theorem filled_mem (z : ℂ) : F.filled z ∈ Icc 0 1 := by
  by_cases hz : (z : Sphere) ∈ (R.model.stages n).domain
  · rw [F.filled_on_domain hz]
    exact clipScalar_mem _
  · have hout : z ∈ ⋃ s, closedBall (F.center s) (F.radius s) := by
      by_contra h
      exact hz ((show z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain from
        F.complement.symm ▸ h))
    obtain ⟨s, hs⟩ := mem_iUnion.mp hout
    rw [F.filled_on_hole s hs]
    exact clipScalar_mem _

theorem filled_measurable : Measurable F.filled := by
  classical
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  have hc := clipScalar_lipschitz.continuous.comp_continuousOn (R.transferred_continuousOn i n)
  have hm : Measurable ((((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).indicator
      (clipScalar ∘ R.transferred i n)) := by
    have he : ((((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).indicator
        (clipScalar ∘ R.transferred i n)) =
        ((((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).piecewise
          (clipScalar ∘ R.transferred i n) (fun _ => 0)) := by
      funext z
      by_cases hz : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain <;> simp [hz]
    rw [he]
    exact hc.measurable_piecewise continuousOn_const hU.measurableSet
  exact hm.add (Measurable.tsum fun s => measurable_const.indicator measurableSet_closedBall)

theorem filled_memLp {p : ℝ≥0∞} {μ : Measure ℂ} [IsFiniteMeasure μ] : MemLp F.filled p μ := by
  apply MemLp.of_bound F.filled_measurable.aestronglyMeasurable 1
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (F.filled_mem z).1]
    exact (F.filled_mem z).2

end HoleFilling
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ClippedScalarEnergy
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipping the transferred scalar preserves its source values and does
not increase its actual differential energy, including on the clipping levels. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel.HoleFilling
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
  {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

local instance instBorelSpaceSphere_41_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem filled_gradient_le {z : ℂ} (hz : (z : Sphere) ∈ (R.model.stages n).domain) :
    euclideanGradientEnergy F.filled z ≤ euclideanGradientEnergy (R.transferred i n) z := by
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  have hz' : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain := hz
  have heq : F.filled =ᶠ[𝓝 z] clipScalar ∘ R.transferred i n := by
    filter_upwards [hU.mem_nhds hz'] with y hy
    exact F.filled_on_domain hy
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  have h := euclideanGradientEnergy_clipScalar_le
    ((R.transferred_continuousOn i n).continuousAt (hU.mem_nhds hz'))
  simpa only [euclideanGradientEnergy, ← hd] using h

end RetainedRealCircleModel.HoleFilling
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FilledScalarEnergy
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L² bounds for the clipped filled functions' differentials, extended by
zero inside the actual target holes. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_42_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem eventually_filled_energy (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      IntegrableOn (euclideanGradientEnergy F.filled)
        (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) ∧
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain),
        euclideanGradientEnergy F.filled z) <
      (∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + modelError n := by
  filter_upwards [R.eventually_energy i] with n hn F
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  have hm : Measurable (euclideanGradientEnergy F.filled) :=
    ((measurable_fderiv_apply_const ℝ F.filled (1 : ℂ)).pow_const 2).add
      ((measurable_fderiv_apply_const ℝ F.filled Complex.I).pow_const 2)
  have hle : ∀ᵐ z ∂volume.restrict (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain),
      euclideanGradientEnergy F.filled z ≤ euclideanGradientEnergy (R.transferred i n) z := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact F.filled_gradient_le hz
  have hi : IntegrableOn (euclideanGradientEnergy F.filled)
      (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
    apply hn.1.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanGradientEnergy_nonneg _ _)] using hz
  exact ⟨hi, (integral_mono_ae hi hn.1 hle).trans_lt hn.2⟩

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FilledScalarGlobalEnergy
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite holes contribute no ordinary gradient energy. Their circular
boundaries are null, including degenerate point circles. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace HoleFilling
variable {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

 local instance instBorelSpaceSphere_43_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem filled_fderiv_on_ball (s : (R.model.stages n).indices) {z : ℂ}
    (hz : z ∈ ball (F.center s) (F.radius s)) : fderiv ℝ F.filled z = 0 := by
  have he : F.filled =ᶠ[𝓝 z] fun _ => clipScalar (F.value s) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact F.filled_on_hole s (ball_subset_closedBall hw)
  rw [he.fderiv_eq, fderiv_const_apply]

 theorem filled_energy_eq_indicator_ae :
    euclideanGradientEnergy F.filled =ᵐ[volume]
      (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).indicator
        (euclideanGradientEnergy F.filled) := by
  classical
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  have hs : ∀ᵐ z ∂(volume : Measure ℂ), ∀ s, z ∉ sphere (F.center s) (F.radius s) := by
    apply ae_all_iff.mpr
    intro s
    exact compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (F.center s) (F.radius s))
  filter_upwards [hs] with z hz
  by_cases hU : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain
  · rw [indicator_of_mem hU]
  · rw [indicator_of_notMem hU]
    have hout : z ∈ ⋃ s, closedBall (F.center s) (F.radius s) := by
      rw [F.complement] at hU
      exact not_not.mp hU
    obtain ⟨s, hsz⟩ := mem_iUnion.mp hout
    have hball : z ∈ ball (F.center s) (F.radius s) :=
      lt_of_le_of_ne hsz (fun he => hz s he)
    simp only [euclideanGradientEnergy, F.filled_fderiv_on_ball s hball, zero_apply,
      zero_pow (by decide : 2 ≠ 0), zero_add]

 theorem filled_energy_integrable_iff :
    Integrable (euclideanGradientEnergy F.filled) ↔
      IntegrableOn (euclideanGradientEnergy F.filled)
        (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  rw [← integrable_indicator_iff hU.measurableSet]
  exact integrable_congr F.filled_energy_eq_indicator_ae

 theorem integral_filled_energy :
    (∫ z, euclideanGradientEnergy F.filled z) =
      ∫ z in (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain),
        euclideanGradientEnergy F.filled z := by
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  rw [integral_congr_ae F.filled_energy_eq_indicator_ae, integral_indicator hU.measurableSet]

end HoleFilling

 local instance instBorelSpaceSphere_43_r5345e3_2 : BorelSpace Sphere := ⟨rfl⟩
theorem eventually_filled_global_energy (R : RetainedRealCircleModel d π Q) (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      Integrable (euclideanGradientEnergy F.filled) ∧
      (∫ z, euclideanGradientEnergy F.filled z) <
      (∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + modelError n := by
  filter_upwards [R.eventually_filled_energy i] with n hn F
  rw [F.filled_energy_integrable_iff, F.integral_filled_energy]
  exact hn F

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FilledScalarL2
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two ordinary differential components of the finite filled scalar
are in planar L², with the source energy as their combined bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_44_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem eventually_filled_partials_memLp (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      MemLp (fun z => fderiv ℝ F.filled z 1) 2 volume ∧
        MemLp (fun z => fderiv ℝ F.filled z Complex.I) 2 volume := by
  filter_upwards [R.eventually_filled_global_energy i] with n hn F
  exact memLp_partials_of_integrable_euclidean_energy (hn F).1

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FilledScalarNormBounds
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform norm bounds for the actual bounded scalar fillings and their
two L² differential components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_45_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem HoleFilling.filled_norm_bound {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)
    {μ : Measure ℂ} [IsFiniteMeasure μ] :
    ‖(F.filled_memLp (p := 2) (μ := μ)).toLp F.filled‖ ≤
      (measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ := by
  have h := F.filled_memLp (p := 2) (μ := μ)
  have hb : ∀ᵐ z ∂μ, ‖h.toLp F.filled z‖ ≤ (1 : ℝ) := by
    filter_upwards [h.coeFn_toLp] with z hz
    rw [hz, Real.norm_eq_abs, abs_of_nonneg (F.filled_mem z).1]
    exact (F.filled_mem z).2
  simpa only [mul_one] using Lp.norm_le_of_ae_bound zero_le_one hb

 theorem eventually_filled_partial_norm_bounds (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      ∃ h₁ : MemLp (fun z => fderiv ℝ F.filled z 1) 2 volume,
      ∃ h₂ : MemLp (fun z => fderiv ℝ F.filled z Complex.I) 2 volume,
      ‖h₁.toLp (fun z => fderiv ℝ F.filled z 1)‖ ≤ Real.sqrt
        ((∫ x in realChartDomain d.physicalDomain,
          gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + 1) ∧
      ‖h₂.toLp (fun z => fderiv ℝ F.filled z Complex.I)‖ ≤ Real.sqrt
        ((∫ x in realChartDomain d.physicalDomain,
          gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + 1) := by
  filter_upwards [R.eventually_filled_global_energy i, R.eventually_filled_partials_memLp i]
    with n he hp F
  obtain ⟨h₁, h₂⟩ := hp F
  have heps : modelError n ≤ 1 := by
    rw [modelError]
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsq₁ : (∫ z, (fderiv ℝ F.filled z 1) ^ 2) ≤ ∫ z, euclideanGradientEnergy F.filled z :=
    integral_mono h₁.integrable_sq (he F).1 (fun z => le_add_of_nonneg_right (sq_nonneg _))
  have hsq₂ : (∫ z, (fderiv ℝ F.filled z Complex.I) ^ 2) ≤ ∫ z, euclideanGradientEnergy F.filled z :=
    integral_mono h₂.integrable_sq (he F).1 (fun z => le_add_of_nonneg_left (sq_nonneg _))
  refine ⟨h₁, h₂, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    rw [Lp.norm_toLp, ← integral_sq_eq_eLpNorm_toReal_sq h₁]
    exact hsq₁.trans ((he F).2.le.trans (add_le_add le_rfl heps))
  · apply Real.le_sqrt_of_sq_le
    rw [Lp.norm_toLp, ← integral_sq_eq_eLpNorm_toReal_sq h₂]
    exact hsq₂.trans ((he F).2.le.trans (add_le_add le_rfl heps))

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPlaneEnergyTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conformal energy identity in the Euclidean-plane
coordinates used by the Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

 theorem smooth_plane_energy_transport
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u : EuclideanPlane → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (physicalPlaneDomain U))
    (hgrad : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain U))) :
    ContDiffOn ℝ 1 (planeInverseTransport fi u) (physicalPlaneDomain V) ∧
    (∀ i : Fin 2, MemLp (fun x => fderiv ℝ (planeInverseTransport fi u) x
      (EuclideanSpace.single i 1)) 2 (volume.restrict (physicalPlaneDomain V))) ∧
    (∫ x in physicalPlaneDomain V,
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)) ^ 2) =
    ∫ x in physicalPlaneDomain U,
      (fderiv ℝ u x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ u x (EuclideanSpace.single 1 1)) ^ 2 := by
  let w := u ∘ euclideanPlaneCoordinates.symm
  let t : ℂ → ℝ := (sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)
  have hdom : euclideanPlaneCoordinates ⁻¹' realChartDomain U = physicalPlaneDomain U := by
    ext x
    rfl
  have hD := isOpen_realChartDomain hU
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) w (realChartDomain U) :=
    hu.comp euclideanPlaneCoordinates.symm.contDiff.contDiffOn (fun x hx => by
      change ((Complex.equivRealProdCLM.symm (euclideanPlaneCoordinates
        (euclideanPlaneCoordinates.symm x)) : ℂ) : Sphere) ∈ U
      change ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U at hx
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx)
  have hg : MemLp (planarGradient w) 2 (volume.restrict (realChartDomain U)) :=
    real_chart_gradient_memLp hD hu hgrad
  have ht := transported_real_energy heq hU hV hinf hfix w hw
    (fun p hp => (hf p hp).isMetricConformalAt_spherical)
    (fun x _ => Matrix.PosDef.one.smul (sphericalMetricFactor_pos x))
    (integrable_gradientEnergy_spherical_of_memLp hg)
  have htdef : planeInverseTransport fi u = t ∘ complexPlaneCoordinates := by
    funext x
    simp only [planeInverseTransport, t, w, comp_apply, sphereRealMap, sphereRealFunction,
      complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply]
  have hs : ContDiffOn ℝ 1 (planeInverseTransport fi u) (physicalPlaneDomain V) := by
    rw [htdef]
    exact ht.1.comp complexPlaneCoordinates.contDiff.contDiffOn (fun x hx => hx)
  have hP := isOpen_physicalPlaneDomain hV
  have hd (x : EuclideanPlane) (hx : x ∈ physicalPlaneDomain V) (i : Fin 2) :
      fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single i 1) =
        fderiv ℝ t (complexPlaneCoordinates x) (if i = 0 then 1 else Complex.I) := by
    rw [htdef, fderiv_comp x
      ((ht.1.contDiffAt ((hV.preimage OnePoint.continuous_coe).mem_nhds hx)).differentiableAt
        (by norm_num)) complexPlaneCoordinates.differentiableAt, complexPlaneCoordinates.fderiv]
    change fderiv ℝ t (complexPlaneCoordinates x)
      (complexPlaneCoordinates (EuclideanSpace.single i 1)) = _
    have haxis : complexPlaneCoordinates (EuclideanSpace.single i 1) =
        (if i = 0 then 1 else Complex.I) := by
      fin_cases i
      · exact complexPlaneCoordinates_zero
      · exact complexPlaneCoordinates_one
    rw [haxis]
  have he (x : EuclideanPlane) (hx : x ∈ physicalPlaneDomain V) :
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)) ^ 2 =
        euclideanGradientEnergy t (complexPlaneCoordinates x) := by
    rw [hd x hx 0, hd x hx 1]
    rfl
  have hmp := complexPlaneCoordinates_measurePreserving.restrict_preimage
    (hV.preimage OnePoint.continuous_coe).measurableSet
  have hi := (hmp.integrable_comp ht.2.1.aestronglyMeasurable).mpr ht.2.1
  have hie : IntegrableOn (fun x =>
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)) ^ 2)
      (physicalPlaneDomain V) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem hP.measurableSet] with x hx
    exact (he x hx).symm
  have hparts (i : Fin 2) : MemLp (fun x =>
      fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain V)) := by
    have hm : AEStronglyMeasurable (fun x => fderiv ℝ (planeInverseTransport fi u) x
        (EuclideanSpace.single i 1)) (volume.restrict (physicalPlaneDomain V)) :=
      ((hs.continuousOn_fderiv_of_isOpen hP le_rfl).clm_apply
        continuousOn_const).aestronglyMeasurable hP.measurableSet
    apply (memLp_two_iff_integrable_sq hm).mpr
    apply hie.mono' (hm.pow 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    fin_cases i
    · change (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)) ^ 2 ≤ _
      exact le_add_of_nonneg_right (sq_nonneg _)
    · change (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)) ^ 2 ≤ _
      exact le_add_of_nonneg_left (sq_nonneg _)
  refine ⟨hs, hparts, ?_⟩
  calc
    _ = ∫ x in physicalPlaneDomain V, euclideanGradientEnergy t (complexPlaneCoordinates x) :=
      setIntegral_congr_fun hP.measurableSet he
    _ = ∫ z in ((↑) : ℂ → Sphere) ⁻¹' V, euclideanGradientEnergy t z :=
      hmp.integral_comp complexPlaneCoordinates.toHomeomorph.measurableEmbedding _
    _ = ∫ x in realChartDomain U, gradientEnergy w (fun z => sphericalMetricFactor z • 1) x := ht.2.2
    _ = _ := by
      have hn₀ : eLpNorm (fun p => fderiv ℝ w p (1, 0)) 2
          (volume.restrict (realChartDomain U)) =
          eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single 0 1)) 2
            (volume.restrict (physicalPlaneDomain U)) := by
        simpa only [↓reduceIte, hdom] using real_chart_partial_eLpNorm hD hu 0 (hgrad 0)
      have hn₁ : eLpNorm (fun p => fderiv ℝ w p (0, 1)) 2
          (volume.restrict (realChartDomain U)) =
          eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single 1 1)) 2
            (volume.restrict (physicalPlaneDomain U)) := by
        simpa only [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), hdom] using real_chart_partial_eLpNorm hD hu 1 (hgrad 1)
      rw [spherical_gradient_energy_eq_norms hg, hn₀, hn₁,
        ← integral_sq_eq_eLpNorm_toReal_sq (hgrad 0),
        ← integral_sq_eq_eLpNorm_toReal_sq (hgrad 1),
        integral_add (hgrad 0).integrable_sq (hgrad 1).integrable_sq]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevConformalTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous compactly supported Sobolev functions can be transported
by the actual smooth conformal inverse. The local target witness has at
most the source energy; no smoothness of the original test is assumed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem sobolev_conformal_transport
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (H : DeGiorgi.MemW1pWitness 2 u univ)
    (hv : EqOn v (planeInverseTransport fi u) (physicalPlaneDomain V))
    (hL : MemLp v 2 (volume.restrict (physicalPlaneDomain V))) :
    ∃ K : DeGiorgi.MemW1pWitness 2 v (physicalPlaneDomain V),
      (∫ x in physicalPlaneDomain V, K.weakGrad x 0 ^ 2 + K.weakGrad x 1 ^ 2) ≤
      ∫ x in physicalPlaneDomain U, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2 := by
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using H.memLp
  let a (n : ℕ) := planarMollification u n
  let b (n : ℕ) := planeInverseTransport fi (a n)
  have ha (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (a n) :=
    planarMollification_smooth (huL.locallyIntegrable (by norm_num)) n
  have htransport (n : ℕ) := smooth_plane_energy_transport heq hU hV hinf hfix hf
    (ha n).contDiffOn (fun i => (planarMollification_partial_memLp H hs n i).restrict _)
  obtain ⟨C, hC⟩ := hu.bounded_above_of_compact_support hs
  have hunit (x : EuclideanPlane) : u x ∈ Icc (-C) C :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using hC x)
  have hb (n : ℕ) (x : EuclideanPlane) (_hx : x ∈ physicalPlaneDomain V) : ‖b n x‖ ≤ C := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (planarMollification_mem_Icc hu.aestronglyMeasurable hunit n _)
  have hp (x : EuclideanPlane) (hx : x ∈ physicalPlaneDomain V) :
      Tendsto (fun n => b n x) atTop (𝓝 (v x)) := by
    rw [hv hx]
    exact planarMollification_tendsto_of_continuous hu _
  apply smooth_energy_limit (isOpen_physicalPlaneDomain hV) hL b
    (fun n => (htransport n).1) (fun n => (htransport n).2.1) hb hp
  have he := planarMollification_energy_tendsto H hs (physicalPlaneDomain U)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact (htransport n).2.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ZeroTraceConformalTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A transported continuous zero-trace error extends to the whole target
plane, with no added complementary energy. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem zero_trace_conformal_transport
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (H : DeGiorgi.MemW1pWitness 2 u univ)
    (hv : EqOn v (planeInverseTransport fi u) (physicalPlaneDomain V))
    (hvc : Continuous v) (hvs : HasCompactSupport v)
    (hz : ∀ x ∉ physicalPlaneDomain V, v x = 0) :
    ∃ K : DeGiorgi.MemW1pWitness 2 v univ,
      (∀ i : Fin 2, ∀ x ∉ physicalPlaneDomain V, K.weakGrad x i = 0) ∧
      (∫ x, K.weakGrad x 0 ^ 2 + K.weakGrad x 1 ^ 2) ≤
        ∫ x in physicalPlaneDomain U, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2 := by
  obtain ⟨W, hW⟩ := sobolev_conformal_transport heq hU hV hinf hfix hf hu hs H hv
    ((hvc.memLp_of_hasCompactSupport hvs).restrict _)
  let K := zeroTraceWitness (isOpen_physicalPlaneDomain hV) hvc hvs hz W
  exact ⟨K, zeroTraceWitness_zero (isOpen_physicalPlaneDomain hV) hvc hvs hz W,
    (zeroTraceWitness_energy (isOpen_physicalPlaneDomain hV) hvc hvs hz W).trans_le hW⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarWeakLimits
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common subsequence of the actual finite scalar fillings and their
two differentials. The scalar is bounded in spherical L²; the differentials
are bounded in ordinary planar L². -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_46_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_filled_weak_limits (i : Fin m) (F : ∀ n, R.HoleFilling i n) :
    ∃ (V : Lp ℝ 2 planarSphericalArea) (G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ))
      (σ : ℕ → ℕ), StrictMono σ ∧
      (∃ τ : ℕ → ℕ, StrictMono τ ∧ σ = R.limit.subsequence ∘ τ) ∧
      (∀ w : Lp ℝ 2 planarSphericalArea,
        Tendsto (fun n => ∫ z, (F (σ n)).filled z * w z ∂planarSphericalArea)
          atTop (𝓝 (∫ z, V z * w z ∂planarSphericalArea))) ∧
      (∀ w : Lp ℝ 2 (volume : Measure ℂ),
        Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z 1 * w z)
          atTop (𝓝 (∫ z, G₁ z * w z))) ∧
      (∀ w : Lp ℝ 2 (volume : Measure ℂ),
        Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z Complex.I * w z)
          atTop (𝓝 (∫ z, G₂ z * w z))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (R.limit.strict.tendsto_atTop.eventually (R.eventually_filled_partial_norm_bounds i))
  choose h₁ h₂ hb₁ hb₂ using fun n => hN (N + n) (Nat.le_add_right N n) (F (R.limit.subsequence (N + n)))
  let u₀ : ℕ → ℂ → ℝ := fun n => (F (R.limit.subsequence (N + n))).filled
  let u₁ : ℕ → ℂ → ℝ := fun n z => fderiv ℝ (F (R.limit.subsequence (N + n))).filled z 1
  let u₂ : ℕ → ℂ → ℝ := fun n z => fderiv ℝ (F (R.limit.subsequence (N + n))).filled z Complex.I
  have h₀ (n : ℕ) : MemLp (u₀ n) 2 planarSphericalArea := (F (R.limit.subsequence (N + n))).filled_memLp
  obtain ⟨V, G₁, G₂, τ, hτ, hv, hg₁, hg₂⟩ :=
    exists_three_L2_weak_limits planarSphericalArea volume volume u₀ u₁ u₂ h₀ h₁ h₂
      _ _ _ (fun n => (F (R.limit.subsequence (N + n))).filled_norm_bound R) hb₁ hb₂
  refine ⟨V, G₁, G₂, fun n => R.limit.subsequence (N + τ n),
    R.limit.strict.comp (fun a b hab => Nat.add_lt_add_left (hτ hab) N),
    ⟨fun n => N + τ n, fun a b hab => Nat.add_lt_add_left (hτ hab) N, rfl⟩,
    hv, hg₁, hg₂⟩

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarWeakEnergy
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The combined energy of the weak derivative limit is bounded by the
original source energy, without the finite-stage error. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem filled_weak_energy_le (i : Fin m) (F : ∀ n, R.HoleFilling i n)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ))
    (h₁ : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
      Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z 1 * w z)
        atTop (𝓝 (∫ z, G₁ z * w z)))
    (h₂ : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
      Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z Complex.I * w z)
        atTop (𝓝 (∫ z, G₂ z * w z))) :
    (∫ z, G₁ z ^ 2 + G₂ z ^ 2) ≤
      ∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hσ.tendsto_atTop.eventually (R.eventually_filled_global_energy i))
  have ht : StrictMono (fun n : ℕ => N + n) :=
    fun a b hab => Nat.add_lt_add_left hab N
  let u₁ : ℕ → ℂ → ℝ := fun n z => fderiv ℝ (F (σ (N + n))).filled z 1
  let u₂ : ℕ → ℂ → ℝ := fun n z => fderiv ℝ (F (σ (N + n))).filled z Complex.I
  have hi (n : ℕ) := memLp_partials_of_integrable_euclidean_energy
    (hN (N + n) (Nat.le_add_right N n) (F (σ (N + n)))).1
  apply paired_L2_energy_le (u₁ := u₁) (u₂ := u₂)
    (fun n => (hi n).1) (fun n => (hi n).2) G₁ G₂
    (modelError_tendsto.comp (hσ.comp ht).tendsto_atTop)
  · exact Eventually.of_forall fun n =>
      (hN (N + n) (Nat.le_add_right N n) (F (σ (N + n)))).2.le
  · exact (h₁ G₁).comp ht.tendsto_atTop
  · exact (h₂ G₂).comp ht.tendsto_atTop

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FilledScalarTestIntegrals
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All test-function pairings for the finite scalar fillings are actual
integrable functions on the whole plane. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem eventually_filled_test_integrals (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n, ∀ φ : ℂ → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ →
      Integrable (fun z => F.filled z * fderiv ℝ φ z 1) ∧
      Integrable (fun z => fderiv ℝ F.filled z 1 * φ z) ∧
      Integrable (fun z => F.filled z * fderiv ℝ φ z Complex.I) ∧
      Integrable (fun z => fderiv ℝ F.filled z Complex.I * φ z) := by
  filter_upwards [R.eventually_filled_partials_memLp i] with n hn F φ hφ hs
  have hF : ∀ᵐ z ∂(volume : Measure ℂ), ‖F.filled z‖ ≤ (1 : ℝ) :=
    Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (F.filled_mem z).1]
      exact (F.filled_mem z).2
  have hc (v : ℂ) : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have ht (v : ℂ) : Integrable (fun z => F.filled z * fderiv ℝ φ z v) :=
    ((hc v).integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) v)).bdd_mul
      F.filled_measurable.aestronglyMeasurable hF
  have hφ₂ : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
  exact ⟨ht 1, (hn F).1.integrable_mul hφ₂, ht Complex.I, (hn F).2.integrable_mul hφ₂⟩

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FilledScalarSliceDerivative
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual line derivatives of the finite filling agree almost everywhere
with its ordinary planar partials. Circular boundaries are the only exclusions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem transferred_contDiffOn (i : Fin m) (n : ℕ) :
    ContDiffOn ℝ ∞ (R.transferred i n) (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
  rw [transferred, transported_sphereRealFunction_eq]
  exact ((R.model.stages n).transported_smooth (prefixIndex (R.index i) n)).comp
    Complex.equivRealProdCLM.contDiff.contDiffOn (fun z hz => by
      simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz)

namespace HoleFilling
variable {R} {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

 theorem horizontal_derivative_ae :
    ∀ᵐ z ∂(volume : Measure ℂ),
      deriv (F.filled ∘ horizontalLine z.im) z.re = fderiv ℝ F.filled z 1 := by
  classical
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  have hs : ∀ᵐ z ∂(volume : Measure ℂ), ∀ s, z ∉ sphere (F.center s) (F.radius s) := by
    apply ae_all_iff.mpr
    intro s
    exact compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (F.center s) (F.radius s))
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  filter_upwards [hs] with z hz
  have hez : horizontalLine z.im z.re = z := by apply Complex.ext <;> rfl
  by_cases hmem : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain
  · have he : F.filled =ᶠ[𝓝 z] clipScalar ∘ R.transferred i n := by
      filter_upwards [hU.mem_nhds hmem] with w hw
      exact F.filled_on_domain hw
    have hd := ((R.transferred_contDiffOn i n).contDiffAt (hU.mem_nhds hmem)).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    apply deriv_eq_fderiv_of_eventuallyEq_clip (by simpa only [hez] using he)
      (by simpa only [hez] using hd) (hasDerivAt_horizontalLine z.re z.im)
  · have hout : z ∈ ⋃ s, closedBall (F.center s) (F.radius s) := by
      rw [F.complement] at hmem
      exact not_not.mp hmem
    obtain ⟨s, hsz⟩ := mem_iUnion.mp hout
    have hball : z ∈ ball (F.center s) (F.radius s) :=
      lt_of_le_of_ne hsz (fun he => hz s he)
    have he : F.filled =ᶠ[𝓝 z] fun _ => clipScalar (F.value s) := by
      filter_upwards [isOpen_ball.mem_nhds hball] with w hw
      exact F.filled_on_hole s (ball_subset_closedBall hw)
    have hc : (F.filled ∘ horizontalLine z.im) =ᶠ[𝓝 z.re] fun _ => clipScalar (F.value s) := by
      simpa only [comp_def, hez] using he.comp_tendsto
        (show Tendsto (horizontalLine z.im) (𝓝 z.re) (𝓝 z) by
          have hh : Tendsto (horizontalLine z.im) (𝓝 z.re)
              (𝓝 (horizontalLine z.im z.re)) := (continuous_horizontalLine z.im).continuousAt.tendsto
          rw [hez] at hh
          exact hh)
    rw [hc.deriv_eq, deriv_const, F.filled_fderiv_on_ball s hball, zero_apply]

end HoleFilling
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ActualScalarJump
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal distributional jump bound for the actual retained scalar
models. All geometric, integrability and cluster hypotheses are constructed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem eventually_filled_horizontal_jump (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n, ∀ φ : ℂ → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ C : ℝ, 0 ≤ C → (∀ z, |φ z| ≤ C) →
      |(∫ z, F.filled z * fderiv ℝ φ z 1) + (∫ z, fderiv ℝ F.filled z 1 * φ z)| ≤
      4 * C * ∑' s, F.radius s * terminalOscillation ((R.model.stages n).terminals.H s)
        ((R.model.stages n).functions (prefixIndex (R.index i) n)) := by
  filter_upwards [R.eventually_energy i, R.eventually_filled_test_integrals i] with n hn htest
  intro F φ hφ hs C hC hbound
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  let U := (⋃ s, closedBall (F.center s) (F.radius s))ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite (fun _ => isClosed_closedBall)).isOpen_compl
  have he : IntegrableOn (euclideanGradientEnergy (R.transferred i n)) U := by
    simpa only [F.complement] using hn.1
  have hv : ContDiffOn ℝ 1 (R.transferred i n) U := by
    simpa only [F.complement] using (R.transferred_contDiffOn i n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc : IsCompact (tsupport φ ∪ ⋃ s, closedBall (F.center s) (F.radius s)) :=
    hs.union (isCompact_iUnion (fun _ => isCompact_closedBall _ _))
  obtain ⟨L, hL, hBL⟩ := hc.isBounded.exists_pos_norm_lt
  have hsub (s : (R.model.stages n).indices) : closedBall (F.center s) (F.radius s) ⊆ ball 0 L := by
    intro z hz
    exact mem_ball_zero_iff.mpr (hBL z (Or.inr (mem_iUnion.mpr ⟨s, hz⟩)))
  have hsL : tsupport φ ⊆ ball 0 L := fun z hz =>
    mem_ball_zero_iff.mpr (hBL z (Or.inl hz))
  obtain ⟨ρ, hρ, hmajor⟩ := exists_integrable_gradient_majorant_on_square hU he hL.le
  rw [tsum_fintype]
  apply planar_filled_horizontal_jump_of_density F.center F.radius F.value
    (fun s => terminalOscillation ((R.model.stages n).terminals.H s)
      ((R.model.stages n).functions (prefixIndex (R.index i) n)))
    F.radius_nonneg (fun _ => Metric.diam_nonneg) F.disjoint hL hsub hv hρ hmajor
  · intro z hz
    apply F.filled_on_domain
    change z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain
    rw [F.complement]
    exact hz
  · exact fun s z hz => F.filled_on_hole s hz
  · intro s z t hz ht
    apply F.cluster_error s t
    apply planar_mapClusterPt_mem_componentClusterValues
    · rw [F.component]
      exact mem_image_of_mem _ hz
    · simpa only [F.complement, RetainedRealCircleModel.transferred] using ht
  · exact F.horizontal_derivative_ae
  · exact hφ
  · exact hsL
  · exact (htest F φ hφ hs).1
  · exact (htest F φ hφ hs).2.1
  · exact hC
  · exact hbound

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ActualScalarJumpLimit
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed finite fillings have vanishing distributional errors.
Consequently every weak limit of their two pairings satisfies the horizontal
weak derivative identity. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_47_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem filled_horizontal_error_tendsto (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) (F : ∀ n, R.HoleFilling i n)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    Tendsto (fun n => (∫ z, (F n).filled z * fderiv ℝ φ z 1) +
      (∫ z, fderiv ℝ (F n).filled z 1 * φ z)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hs
  have hCpos : 0 ≤ C := (norm_nonneg (φ 0)).trans (hC 0)
  have hlim : Tendsto (fun n => 4 * C * (3 * R.model.radius * modelError n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (modelError_tendsto.const_mul (3 * R.model.radius)).const_mul (4 * C)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [R.eventually_filled_horizontal_jump i, R.eventually_hole_cost_bound harea i hQ]
    with n hn hcost
  rw [Real.norm_eq_abs]
  exact (hn (F n) φ hφ hs C hCpos (fun z => by simpa only [Real.norm_eq_abs] using hC z)).trans
    (mul_le_mul_of_nonneg_left (hcost (F n)).le (mul_nonneg (by norm_num) hCpos))

 theorem horizontal_weak_limit_identity (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) (F : ∀ n, R.HoleFilling i n)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {V G : ℂ → ℝ}
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hV : Tendsto (fun n => ∫ z, (F (σ n)).filled z * fderiv ℝ φ z 1)
      atTop (𝓝 (∫ z, V z * fderiv ℝ φ z 1)))
    (hG : Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z 1 * φ z)
      atTop (𝓝 (∫ z, G z * φ z))) :
    (∫ z, V z * fderiv ℝ φ z 1) = -(∫ z, G z * φ z) := by
  have hzero := (R.filled_horizontal_error_tendsto harea i hQ F hφ hs).comp hσ.tendsto_atTop
  have he := tendsto_nhds_unique (hV.add hG) hzero
  linarith

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_VerticalFilledDerivative
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second ordinary partial of the actual filled scalar is also its
line derivative almost everywhere, including the clipping levels. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel.HoleFilling
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
  {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

 theorem vertical_derivative_ae :
    ∀ᵐ z ∂(volume : Measure ℂ),
      deriv (F.filled ∘ verticalLine z.re) z.im = fderiv ℝ F.filled z Complex.I := by
  classical
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  have hs : ∀ᵐ z ∂(volume : Measure ℂ), ∀ s, z ∉ sphere (F.center s) (F.radius s) := by
    apply ae_all_iff.mpr
    intro s
    exact compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (F.center s) (F.radius s))
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  filter_upwards [hs] with z hz
  have hez : verticalLine z.re z.im = z := by apply Complex.ext <;> rfl
  by_cases hmem : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain
  · have he : F.filled =ᶠ[𝓝 z] clipScalar ∘ R.transferred i n := by
      filter_upwards [hU.mem_nhds hmem] with w hw
      exact F.filled_on_domain hw
    have hd := ((R.transferred_contDiffOn i n).contDiffAt (hU.mem_nhds hmem)).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    apply deriv_eq_fderiv_of_eventuallyEq_clip (by simpa only [hez] using he)
      (by simpa only [hez] using hd) (hasDerivAt_verticalLine z.re z.im)
  · have hout : z ∈ ⋃ s, closedBall (F.center s) (F.radius s) := by
      rw [F.complement] at hmem
      exact not_not.mp hmem
    obtain ⟨s, hsz⟩ := mem_iUnion.mp hout
    have hball : z ∈ ball (F.center s) (F.radius s) :=
      lt_of_le_of_ne hsz (fun he => hz s he)
    have he : F.filled =ᶠ[𝓝 z] fun _ => clipScalar (F.value s) := by
      filter_upwards [isOpen_ball.mem_nhds hball] with w hw
      exact F.filled_on_hole s (ball_subset_closedBall hw)
    have hc : (F.filled ∘ verticalLine z.re) =ᶠ[𝓝 z.im] fun _ => clipScalar (F.value s) := by
      exact he.comp_tendsto (by
        have hh : Tendsto (verticalLine z.re) (𝓝 z.im)
            (𝓝 (verticalLine z.re z.im)) := (continuous_verticalLine z.re).continuousAt.tendsto
        rw [hez] at hh
        exact hh)
    rw [hc.deriv_eq, deriv_const, F.filled_fderiv_on_ball s hball, zero_apply]

end RetainedRealCircleModel.HoleFilling
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ActualVerticalScalarJump
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vertical distributional jump bound for the actual retained scalar
models. All geometric, integrability and cluster hypotheses are constructed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem eventually_filled_vertical_jump (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n, ∀ φ : ℂ → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ C : ℝ, 0 ≤ C → (∀ z, |φ z| ≤ C) →
      |(∫ z, F.filled z * fderiv ℝ φ z Complex.I) + (∫ z, fderiv ℝ F.filled z Complex.I * φ z)| ≤
      4 * C * ∑' s, F.radius s * terminalOscillation ((R.model.stages n).terminals.H s)
        ((R.model.stages n).functions (prefixIndex (R.index i) n)) := by
  filter_upwards [R.eventually_energy i, R.eventually_filled_test_integrals i] with n hn htest
  intro F φ hφ hs C hC hbound
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  let U := (⋃ s, closedBall (F.center s) (F.radius s))ᶜ
  have he : IntegrableOn (euclideanGradientEnergy (R.transferred i n)) U := by
    simpa only [F.complement] using hn.1
  have hv : ContDiffOn ℝ 1 (R.transferred i n) U := by
    simpa only [F.complement] using (R.transferred_contDiffOn i n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc : IsCompact (tsupport φ ∪ ⋃ s, closedBall (F.center s) (F.radius s)) :=
    hs.union (isCompact_iUnion (fun _ => isCompact_closedBall _ _))
  obtain ⟨L, hL, hBL⟩ := hc.isBounded.exists_pos_norm_lt
  have hsub (s : (R.model.stages n).indices) : closedBall (F.center s) (F.radius s) ⊆ ball 0 L := by
    intro z hz
    exact mem_ball_zero_iff.mpr (hBL z (Or.inr (mem_iUnion.mpr ⟨s, hz⟩)))
  have hsL : tsupport φ ⊆ ball 0 L := fun z hz =>
    mem_ball_zero_iff.mpr (hBL z (Or.inl hz))
  rw [tsum_fintype]
  apply planar_filled_vertical_jump F.center F.radius F.value
    (fun s => terminalOscillation ((R.model.stages n).terminals.H s)
      ((R.model.stages n).functions (prefixIndex (R.index i) n)))
    F.radius_nonneg (fun _ => Metric.diam_nonneg) F.disjoint hL hsub hv he
  · intro z hz
    apply F.filled_on_domain
    change z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain
    rw [F.complement]
    exact hz
  · exact fun s z hz => F.filled_on_hole s hz
  · intro s z t hz ht
    apply F.cluster_error s t
    apply planar_mapClusterPt_mem_componentClusterValues
    · rw [F.component]
      exact mem_image_of_mem _ hz
    · simpa only [F.complement, RetainedRealCircleModel.transferred] using ht
  · exact F.vertical_derivative_ae
  · exact hφ
  · exact hsL
  · exact (htest F φ hφ hs).2.2.1
  · exact (htest F φ hφ hs).2.2.2
  · exact hC
  · exact hbound

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ActualVerticalJumpLimit
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed finite fillings have vanishing distributional errors.
Consequently every weak limit of their two pairings satisfies the vertical
weak derivative identity. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem filled_vertical_error_tendsto (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) (F : ∀ n, R.HoleFilling i n)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    Tendsto (fun n => (∫ z, (F n).filled z * fderiv ℝ φ z Complex.I) +
      (∫ z, fderiv ℝ (F n).filled z Complex.I * φ z)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hs
  have hCpos : 0 ≤ C := (norm_nonneg (φ 0)).trans (hC 0)
  have hlim : Tendsto (fun n => 4 * C * (3 * R.model.radius * modelError n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (modelError_tendsto.const_mul (3 * R.model.radius)).const_mul (4 * C)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [R.eventually_filled_vertical_jump i, R.eventually_hole_cost_bound harea i hQ]
    with n hn hcost
  rw [Real.norm_eq_abs]
  exact (hn (F n) φ hφ hs C hCpos (fun z => by simpa only [Real.norm_eq_abs] using hC z)).trans
    (mul_le_mul_of_nonneg_left (hcost (F n)).le (mul_nonneg (by norm_num) hCpos))

 theorem vertical_weak_limit_identity (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) (F : ∀ n, R.HoleFilling i n)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {V G : ℂ → ℝ}
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hV : Tendsto (fun n => ∫ z, (F (σ n)).filled z * fderiv ℝ φ z Complex.I)
      atTop (𝓝 (∫ z, V z * fderiv ℝ φ z Complex.I)))
    (hG : Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z Complex.I * φ z)
      atTop (𝓝 (∫ z, G z * φ z))) :
    (∫ z, V z * fderiv ℝ φ z Complex.I) = -(∫ z, G z * φ z) := by
  have hzero := (R.filled_vertical_error_tendsto harea i hQ F hφ hs).comp hσ.tendsto_atTop
  have he := tendsto_nhds_unique (hV.add hG) hzero
  linarith

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ScalarDistributionalLimit
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine distributional limit of the constructed scalar fillings.
The scalar and both L² derivative fields are obtained by weak compactness;
the derivative identities follow from the vanishing actual disk errors. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_48_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem distributional_identities_of_filled_weak_limits
    (harea : ExteriorCoefficientAreaTheorem) (i : Fin m) (hQ : Continuous (Q i).quotient)
    (F : ∀ n, R.HoleFilling i n) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (V : Lp ℝ 2 planarSphericalArea) (G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ))
    (hv : ∀ w : Lp ℝ 2 planarSphericalArea,
      Tendsto (fun n => ∫ z, (F (σ n)).filled z * w z ∂planarSphericalArea)
        atTop (𝓝 (∫ z, V z * w z ∂planarSphericalArea)))
    (hg₁ : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
      Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z 1 * w z)
        atTop (𝓝 (∫ z, G₁ z * w z)))
    (hg₂ : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
      Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z Complex.I * w z)
        atTop (𝓝 (∫ z, G₂ z * w z))) :
    ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ z, V z * fderiv ℝ φ z 1) = -(∫ z, G₁ z * φ z) ∧
      (∫ z, V z * fderiv ℝ φ z Complex.I) = -(∫ z, G₂ z * φ z) := by
  intro φ hφ hs
  have hφ₂ : MemLp φ 2 (volume : Measure ℂ) := hφ.continuous.memLp_of_hasCompactSupport hs
  have hc (v : ℂ) : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hV₁ := tendsto_planar_pairings_of_spherical hv
    (hc 1)
    (hs.fderiv_apply (𝕜 := ℝ) 1)
  have hV₂ := tendsto_planar_pairings_of_spherical hv
    (hc Complex.I)
    (hs.fderiv_apply (𝕜 := ℝ) Complex.I)
  exact ⟨R.horizontal_weak_limit_identity harea i hQ F hσ hφ hs hV₁
      (tendsto_pairings_with_memLp_test hg₁ hφ₂),
    R.vertical_weak_limit_identity harea i hQ F hσ hφ hs hV₂
      (tendsto_pairings_with_memLp_test hg₂ hφ₂)⟩


end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ScalarLimitWitness
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sequence and its conformal-subsequence factor are retained
alongside the scalar, its weak derivatives and the sharp energy bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

local instance instBorelSpaceSphere_49_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
structure ScalarWeakLimit (i : Fin m) where
  fillings : ∀ n, R.HoleFilling i n
  subsequence : ℕ → ℕ
  strict : StrictMono subsequence
  factor : ∃ τ : ℕ → ℕ, StrictMono τ ∧ subsequence = R.limit.subsequence ∘ τ
  scalar : Lp ℝ 2 planarSphericalArea
  horizontal : Lp ℝ 2 (volume : Measure ℂ)
  vertical : Lp ℝ 2 (volume : Measure ℂ)
  scalar_weak : ∀ w : Lp ℝ 2 planarSphericalArea,
    Tendsto (fun n => ∫ z, (fillings (subsequence n)).filled z * w z ∂planarSphericalArea)
      atTop (𝓝 (∫ z, scalar z * w z ∂planarSphericalArea))
  horizontal_weak : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
    Tendsto (fun n => ∫ z, fderiv ℝ (fillings (subsequence n)).filled z 1 * w z)
      atTop (𝓝 (∫ z, horizontal z * w z))
  vertical_weak : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
    Tendsto (fun n => ∫ z, fderiv ℝ (fillings (subsequence n)).filled z Complex.I * w z)
      atTop (𝓝 (∫ z, vertical z * w z))
  derivative : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∫ z, scalar z * fderiv ℝ φ z 1) = -(∫ z, horizontal z * φ z) ∧
    (∫ z, scalar z * fderiv ℝ φ z Complex.I) = -(∫ z, vertical z * φ z)
  energy : (∫ z, horizontal z ^ 2 + vertical z ^ 2) ≤
    ∫ x in realChartDomain d.physicalDomain,
      gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x

 theorem exists_scalar_weak_limit (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) : Nonempty (R.ScalarWeakLimit i) := by
  let F : ∀ n, R.HoleFilling i n := fun n => Classical.choice (R.exists_hole_filling i n)
  obtain ⟨V, G₁, G₂, σ, hσ, hfactor, hv, hg₁, hg₂⟩ := R.exists_filled_weak_limits i F
  exact ⟨⟨F, σ, hσ, hfactor, V, G₁, G₂, hv, hg₁, hg₂,
    R.distributional_identities_of_filled_weak_limits harea i hQ F hσ V G₁ G₂ hv hg₁ hg₂,
    R.filled_weak_energy_le i F hσ G₁ G₂ hg₁ hg₂⟩⟩

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ScalarPointwiseLimit
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual bounded scalar fillings converge at every point of the
limiting image to the retained source scalar. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

local instance instBorelSpaceSphere_50_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem filled_tendsto_on_image (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (i : Fin m) (F : ∀ n, R.HoleFilling i n) {x : ℂ} (hx : (x : Sphere) ∈ d.physicalDomain) :
    Tendsto (fun n => (F (R.limit.subsequence n)).filled (R.limit.function x))
      atTop (𝓝 ((Q i).physical (Complex.equivRealProdCLM x))) := by
  obtain ⟨r, hr, hrG⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hG.preimage OnePoint.continuous_coe).mem_nhds hx)
  let H := roundJordanAt x r hr
  have hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain := by
    simpa only [H, roundJordanAt_closure] using hrG
  have hxH : x ∈ jordanInterior H := by
    change x ∈ jordanInterior (roundJordanAt x r hr)
    rw [roundJordanAt_interior]
    exact mem_ball_self hr
  have hKG : ((↑) : ℂ → Sphere) '' closure (jordanInterior H) ⊆ d.physicalDomain := by
    rintro _ ⟨z, hz, rfl⟩
    exact hHG hz
  have hK := (isCompact_closure_jordanInterior H).image OnePoint.continuous_coe
  have hevent : ∀ᶠ n in atTop,
      (F (R.limit.subsequence n)).filled (R.limit.function x) =
        clipScalar ((Q i).physical (Complex.equivRealProdCLM
          (finiteCoord ((R.model.stages (R.limit.subsequence n)).inverse (R.limit.function x))))) := by
    filter_upwards [R.limit.eventually_compact_subset_anchor_image hsch hG H hHG
      isCompact_singleton (singleton_subset_iff.mpr (mem_image_of_mem _ hxH)),
      R.limit.strict.tendsto_atTop (R.model.eventually_model_contains hK hKG),
      R.limit.strict.tendsto_atTop (R.eventually_retained i hK hKG)] with n hn hM ht
    obtain ⟨y, hy, he⟩ := hn (mem_singleton (R.limit.function x))
    have hyK := mem_image_of_mem ((↑) : ℂ → Sphere) (subset_closure hy)
    have hyM := hM hyK
    have hyfinite := (R.model.stages (R.limit.subsequence n)).equivalence.finite_forward
      (R.model.stages (R.limit.subsequence n)).source_infty
      (R.model.stages (R.limit.subsequence n)).principal.1 hyM
    have he' : (R.model.stages (R.limit.subsequence n)).forward y =
        (R.limit.function x : Sphere) := by
      change finiteCoord ((R.model.stages (R.limit.subsequence n)).forward y) = R.limit.function x at he
      rw [← coe_finiteCoord hyfinite, he]
    have hi : (R.model.stages (R.limit.subsequence n)).inverse (R.limit.function x) = (y : Sphere) := by
      rw [← he', (R.model.stages (R.limit.subsequence n)).equivalence.left_inv _ hyM]
    rw [(F (R.limit.subsequence n)).filled_on_domain
      (he' ▸ (R.model.stages (R.limit.subsequence n)).equivalence.mapsTo hyM)]
    unfold transferred
    simp only [comp_apply, hi, finiteCoord_coe]
    congr 1
    change (R.model.stages (R.limit.subsequence n)).functions (prefixIndex (R.index i)
      (R.limit.subsequence n)) (Complex.equivRealProdCLM y) = _
    exact ht y hyK
  have hc : ContinuousAt (fun z : ℂ => (Q i).physical (Complex.equivRealProdCLM z)) x := by
    apply ((Q i).physical_smooth.continuousOn.continuousAt
      ((isOpen_realChartDomain hG).mem_nhds ?_)).comp
      Complex.equivRealProdCLM.continuous.continuousAt
    simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hx
  have hlim := (clipScalar_lipschitz.continuous.continuousAt.comp hc).tendsto.comp
    (R.limit.inverse_tendsto hsch hG hx)
  have hu : (Q i).physical (Complex.equivRealProdCLM x) ∈ Icc 0 1 := by
    rw [(Q i).pullback x hx]
    exact (Q i).quotient_unit _
  simp only [comp_def] at hlim
  rw [clipScalar_eq hu] at hlim
  apply hlim.congr'
  filter_upwards [hevent] with n hn
  exact hn.symm

theorem ScalarWeakLimit.pointwise_on_image {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    {x : ℂ} (hx : (x : Sphere) ∈ d.physicalDomain) :
    Tendsto (fun n => (W.fillings (W.subsequence n)).filled (R.limit.function x))
      atTop (𝓝 ((Q i).physical (Complex.equivRealProdCLM x))) := by
  obtain ⟨τ, hτ, he⟩ := W.factor
  rw [he]
  simpa only [comp_def] using
    (R.filled_tendsto_on_image hsch hG i W.fillings hx).comp hτ.tendsto_atTop

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ScalarImageIdentification
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the constructed weak scalar on the actual limiting
circle domain. Positive-area complementary dust is treated separately. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

local instance instBorelSpaceSphere_51_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
def imageScalar (i : Fin m) (z : ℂ) : ℝ :=
  (Q i).physical (Complex.equivRealProdCLM
    (invFunOn R.limit.function (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) z))

theorem imageScalar_apply (hG : IsOpen d.physicalDomain) (i : Fin m)
    {x : ℂ} (hx : (x : Sphere) ∈ d.physicalDomain) :
    R.imageScalar i (R.limit.function x) = (Q i).physical (Complex.equivRealProdCLM x) := by
  unfold imageScalar
  rw [(R.limit.plane_open_embedding hG).2.2.leftInvOn_invFunOn hx]

theorem ScalarWeakLimit.eq_source_ae {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      W.scalar z = R.imageScalar i z := by
  have hS := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  have h := ae_eq_on_of_bounded_weak_pointwise
    (μ := planarSphericalArea)
    (fun n => (W.fillings (W.subsequence n)).filled_measurable.aestronglyMeasurable)
    (fun n z => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((W.fillings (W.subsequence n)).filled_mem z).1]
      exact ((W.fillings (W.subsequence n)).filled_mem z).2)
    W.scalar W.scalar_weak hS.measurableSet
    (t := R.imageScalar i)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [R.imageScalar_apply hG i hx, (Q i).pullback x hx,
        Real.norm_eq_abs, abs_of_nonneg ((Q i).quotient_unit _).1]
      exact ((Q i).quotient_unit _).2)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [R.imageScalar_apply hG i hx]
      exact W.pointwise_on_image R hsch hG hx)
  have habs : (volume : Measure ℂ) ≪ planarSphericalArea :=
    withDensity_absolutelyContinuous'
      continuous_sphericalAreaDensity.measurable.ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun z => (ENNReal.ofReal_pos.mpr (sphericalAreaDensity_pos z)).ne')
  exact habs.ae_le h

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothImageScalar
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The identified scalar is the ordinary smooth inverse transport on
the open limiting domain. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

local instance instBorelSpaceSphere_52_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem imageScalar_contDiffOn (hG : IsOpen d.physicalDomain) (i : Fin m) :
    ContDiffOn ℝ ∞ (R.imageScalar i)
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) := by
  let f := extendAtInfinity R.limit.function
  let V := f '' d.physicalDomain
  have hV : IsOpen V := R.limit.conformal.1.isOpen_image hG hG (Subset.refl _)
  obtain ⟨fi, heq⟩ := R.limit.conformal.exists_smooth_inverse hG hV
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  have hfix : f OnePoint.infty = OnePoint.infty := rfl
  have htransport := (transported_real_coordinate heq hV hinf hfix
    (isOpen_realChartDomain hG) (Subset.refl _) (Q i).physical (Q i).physical_smooth).2.1
  have hc : ContDiffOn ℝ ∞ ((Q i).physical ∘ sphereRealMap fi ∘ Complex.equivRealProdCLM)
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) := by
    apply htransport.comp Complex.equivRealProdCLM.contDiff.contDiffOn
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Complex.equivRealProdCLM x, ?_, ?_⟩
    · simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hx
    · simp only [sphereRealMap, extendAtInfinity_coe, finiteCoord_coe,
        ContinuousLinearEquiv.symm_apply_apply]
  apply hc.congr
  rintro _ ⟨x, hx, rfl⟩
  rw [R.imageScalar_apply hG i hx]
  symm
  change (Q i).physical (Complex.equivRealProdCLM
    (finiteCoord (fi (R.limit.function x)))) = (Q i).physical (Complex.equivRealProdCLM x)
  have he : fi (R.limit.function x) = (x : Sphere) := heq.left_inv x hx
  rw [he, finiteCoord_coe]

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarImageEnergy
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conformal invariance gives the exact original energy on the open
image for the corresponding smooth scalar. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

local instance instBorelSpaceSphere_53_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem imageScalar_energy (hG : IsOpen d.physicalDomain) (i : Fin m) :
    IntegrableOn (euclideanGradientEnergy (R.imageScalar i))
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) ∧
    (∫ z in R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain),
      euclideanGradientEnergy (R.imageScalar i) z) =
      ∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
  let f := extendAtInfinity R.limit.function
  let V := f '' d.physicalDomain
  have hV : IsOpen V := R.limit.conformal.1.isOpen_image hG hG (Subset.refl _)
  obtain ⟨fi, heq⟩ := R.limit.conformal.exists_smooth_inverse hG hV
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  have hfix : f OnePoint.infty = OnePoint.infty := rfl
  have hdom : ((↑) : ℂ → Sphere) ⁻¹' V =
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) := by
    ext z
    constructor
    · rintro ⟨p, hp, he⟩
      cases p using OnePoint.rec with
      | infty => exact (OnePoint.coe_ne_infty z he.symm).elim
      | coe x => exact ⟨x, hp, OnePoint.coe_injective he⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : Sphere), hx, rfl⟩
  let u : ℂ → ℝ := (sphereRealFunction (Q i).physical ∘ fi) ∘ ((↑) : ℂ → Sphere)
  have he : EqOn (R.imageScalar i) u (((↑) : ℂ → Sphere) ⁻¹' V) := by
    rw [hdom]
    rintro _ ⟨x, hx, rfl⟩
    rw [R.imageScalar_apply hG i hx]
    have hi : fi (R.limit.function x) = (x : Sphere) := heq.left_inv x hx
    change (Q i).physical (Complex.equivRealProdCLM x) =
      sphereRealFunction (Q i).physical (fi (R.limit.function x))
    rw [hi]
    rfl
  have henergy := transported_real_energy heq hG hV hinf hfix (Q i).physical
    (Q i).physical_smooth
    (fun p hp => (R.limit.conformal.1 p hp).isMetricConformalAt_spherical)
    (fun x _ => Matrix.PosDef.one.smul (sphericalMetricFactor_pos x))
    (integrable_gradientEnergy_spherical_of_memLp (Q i).physical_energy)
  have hd : EqOn (euclideanGradientEnergy (R.imageScalar i)) (euclideanGradientEnergy u)
      (((↑) : ℂ → Sphere) ⁻¹' V) := by
    intro z hz
    have hl : R.imageScalar i =ᶠ[𝓝 z] u := by
      filter_upwards [(hV.preimage OnePoint.continuous_coe).mem_nhds hz] with y hy
      exact he hy
    simp only [euclideanGradientEnergy, hl.fderiv_eq]
  have hi : IntegrableOn (euclideanGradientEnergy (R.imageScalar i))
      (((↑) : ℂ → Sphere) ⁻¹' V) := by
    apply henergy.2.1.congr
    filter_upwards [ae_restrict_mem (hV.preimage OnePoint.continuous_coe).measurableSet] with z hz
    exact (hd hz).symm
  rw [hdom] at hi
  refine ⟨hi, ?_⟩
  rw [← hdom]
  exact (setIntegral_congr_fun (hV.preimage OnePoint.continuous_coe).measurableSet hd).trans henergy.2.2

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarImageGradient
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two weak fields of the actual limit are the ordinary smooth
partials on its open conformal image. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 theorem gradient_on_image (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      W.horizontal z = fderiv ℝ (R.imageScalar i) z 1 ∧
      W.vertical z = fderiv ℝ (R.imageScalar i) z Complex.I := by
  have hU := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  have hs : ContDiffOn ℝ 1 (R.imageScalar i)
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :=
    (R.imageScalar_contDiffOn hG i).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := W.eq_source_ae R hsch hG
  have hx := weak_field_eq_smooth_derivative hU 1 hs (Lp.memLp W.horizontal) he
    (fun φ hφ hφs => (W.derivative φ hφ hφs).1)
  have hy := weak_field_eq_smooth_derivative hU Complex.I hs (Lp.memLp W.vertical) he
    (fun φ hφ hφs => (W.derivative φ hφ hφs).2)
  filter_upwards [hx, hy] with z hzx hzy hz
  exact ⟨hzx hz, hzy hz⟩

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarEnergySaturation
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All limiting gradient energy is accounted for by the smooth
conformal image. Both weak fields therefore vanish on its complement. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 local instance instBorelSpaceSphere_54_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem zero_gradient_off_image (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∉ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      W.horizontal z = 0 ∧ W.vertical z = 0 := by
  let U := R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)
  let H : ℂ → ℝ := fun z => W.horizontal z ^ 2 + W.vertical z ^ 2
  have hU : IsOpen U := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  have hH : Integrable H := (Lp.memLp W.horizontal).integrable_sq.add
    (Lp.memLp W.vertical).integrable_sq
  have hn : ∀ z, 0 ≤ H z := fun z => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hE : (∫ z in U, H z) = ∫ x in realChartDomain d.physicalDomain,
      gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
    apply Eq.trans _ (R.imageScalar_energy hG i).2
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet,
      ae_restrict_of_ae (W.gradient_on_image hsch hG)] with z hz hg
    rcases hg hz with ⟨hx, hy⟩
    simp only [H, euclideanGradientEnergy, hx, hy]
  have hzero : (∫ z in Uᶜ, H z) = 0 := by
    have hsplit := integral_add_compl hU.measurableSet hH
    have hbound := W.energy
    have hpos : 0 ≤ ∫ z in Uᶜ, H z := integral_nonneg hn
    change (∫ z, H z) ≤ _ at hbound
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hn (hH.restrict (s := Uᶜ))).mp hzero
  change ∀ᵐ z ∂volume.restrict Uᶜ, H z = 0 at hae
  rw [ae_restrict_iff' hU.isClosed_compl.measurableSet] at hae
  filter_upwards [hae] with z hz hout
  have hh : W.horizontal z ^ 2 + W.vertical z ^ 2 = 0 := hz hout
  constructor
  · nlinarith [sq_nonneg (W.vertical z)]
  · nlinarith [sq_nonneg (W.horizontal z)]

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarLocalLp
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar weak limit is locally planar L², including on arbitrary
compact regions that meet limiting complementary components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 theorem scalar_unit_spherical : ∀ᵐ z ∂planarSphericalArea, W.scalar z ∈ Icc 0 1 :=
  ae_mem_unitInterval_of_weak_limit
    (fun n => (W.fillings (W.subsequence n)).filled_measurable.aestronglyMeasurable)
    (fun n z => (W.fillings (W.subsequence n)).filled_mem z) W.scalar W.scalar_weak

 theorem scalar_unit : ∀ᵐ z ∂(volume : Measure ℂ), W.scalar z ∈ Icc 0 1 :=
  planarVolume_absolutelyContinuous_sphericalArea.ae_le W.scalar_unit_spherical

 theorem scalar_aestronglyMeasurable : AEStronglyMeasurable W.scalar (volume : Measure ℂ) :=
  (Lp.aestronglyMeasurable W.scalar).mono_ac planarVolume_absolutelyContinuous_sphericalArea

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScalarBoundedRepresentative
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A pointwise unit-bounded representative of the actual weak scalar,
with the same global planar weak gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 local instance instBorelSpaceSphere_55_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
def boundedRepresentative (x : EuclideanPlane) : ℝ :=
  clipScalar (W.scalar (complexPlaneCoordinates x))

 def planarWeakGradient (x : EuclideanPlane) : EuclideanPlane :=
  WithLp.toLp 2 (fun j => if j = 0 then W.horizontal (complexPlaneCoordinates x)
    else W.vertical (complexPlaneCoordinates x))

 theorem boundedRepresentative_unit (x : EuclideanPlane) :
    W.boundedRepresentative x ∈ Icc 0 1 := clipScalar_mem _

 theorem boundedRepresentative_ae : W.boundedRepresentative =ᵐ[volume]
    W.scalar ∘ complexPlaneCoordinates := by
  filter_upwards [complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae W.scalar_unit]
    with x hx
  exact clipScalar_eq hx

 theorem boundedRepresentative_measurable : AEStronglyMeasurable W.boundedRepresentative volume :=
  clipScalar_lipschitz.continuous.comp_aestronglyMeasurable
    (W.scalar_aestronglyMeasurable.comp_quasiMeasurePreserving
      complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving)

 theorem planarWeakGradient_memLp (j : Fin 2) :
    MemLp (fun x => W.planarWeakGradient x j) 2 volume := by
  fin_cases j
  · change MemLp (W.horizontal ∘ complexPlaneCoordinates) 2 volume
    exact (Lp.memLp W.horizontal).comp_measurePreserving complexPlaneCoordinates_measurePreserving
  · change MemLp (W.vertical ∘ complexPlaneCoordinates) 2 volume
    exact (Lp.memLp W.vertical).comp_measurePreserving complexPlaneCoordinates_measurePreserving

 theorem boundedRepresentative_weak :
    DeGiorgi.HasWeakGrad W.planarWeakGradient W.boundedRepresentative univ := by
  have hsame (j : Fin 2) (g : EuclideanPlane → ℝ)
      (hw : DeGiorgi.HasWeakPartialDeriv j g (W.scalar ∘ complexPlaneCoordinates) univ) :
      DeGiorgi.HasWeakPartialDeriv j g W.boundedRepresentative univ := by
    intro φ hφ hs hsub
    have ht := hw φ hφ hs hsub
    simp only [Measure.restrict_univ] at ht ⊢
    rw [← ht]
    apply integral_congr_ae
    filter_upwards [W.boundedRepresentative_ae] with x hx
    rw [hx]
  intro j
  fin_cases j
  · change DeGiorgi.HasWeakPartialDeriv 0 (W.horizontal ∘ complexPlaneCoordinates)
      W.boundedRepresentative univ
    apply hsame
    simpa only [preimage_univ] using weakPartial_of_complex_identity 0 1 complexPlaneCoordinates_zero
      (fun φ hφ hs => (W.derivative φ hφ hs).1) univ
  · change DeGiorgi.HasWeakPartialDeriv 1 (W.vertical ∘ complexPlaneCoordinates)
      W.boundedRepresentative univ
    apply hsame
    simpa only [preimage_univ] using weakPartial_of_complex_identity 1 Complex.I complexPlaneCoordinates_one
      (fun φ hφ hs => (W.derivative φ hφ hs).2) univ

 theorem planarWeakGradient_zero_off_image (hsch : PlanarSchoenflies)
    (hG : IsOpen d.physicalDomain) (j : Fin 2) :
    ∀ᵐ x ∂volume, complexPlaneCoordinates x ∉
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
        W.planarWeakGradient x j = 0 := by
  filter_upwards [complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae
    (W.zero_gradient_off_image hsch hG)] with x hx hout
  fin_cases j
  · exact (hx hout).1
  · exact (hx hout).2

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScalarLocalizedRange
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local range principle applied to the actual scalar weak limit. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 local instance instBorelSpaceSphere_56_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem le_on_cutoff_plateau (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (hunit : ∀ x, η x ∈ Icc 0 1)
    (hηd : ∀ x, complexPlaneCoordinates x ∉
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) → fderiv ℝ η x = 0)
    {b : ℝ} (hb : 0 ≤ b)
    (hrange : ∀ x, complexPlaneCoordinates x ∈
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      η x ≠ 0 → R.imageScalar i (complexPlaneCoordinates x) ≤ b) :
    ∀ᵐ x ∂volume, η x = 1 → W.scalar (complexPlaneCoordinates x) ≤ b := by
  have he := complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae
    (W.eq_source_ae R hsch hG)
  have h := localized_sobolev_range W.boundedRepresentative_measurable
    W.boundedRepresentative_unit W.planarWeakGradient_memLp W.boundedRepresentative_weak
    (D := complexPlaneCoordinates ⁻¹'
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)))
    (W.planarWeakGradient_zero_off_image hsch hG) hη hs hunit hηd hb (by
      filter_upwards [he, W.boundedRepresentative_ae] with x hx hrep hxin hηx
      rw [hrep]
      change W.scalar (complexPlaneCoordinates x) ≤ b
      rw [hx hxin]
      exact hrange x hxin hηx)
  filter_upwards [h, W.boundedRepresentative_ae] with x hx hrep hηx
  have ht := hx hηx
  rwa [hrep] at ht

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScalarRegionRange
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A strict bound on the scalar's smooth image inside a bounded Jordan
region also bounds its weak representative on the whole closed region. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 local instance instBorelSpaceSphere_57_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem le_on_closed_region (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    {O : Set ℂ} (hO : IsOpen O) (hK : IsCompact (closure O))
    (hfront : frontier O ⊆ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain))
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ z ∈ closure O,
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      R.imageScalar i z < b) :
    ∀ᵐ z ∂volume, z ∈ closure O → W.scalar z ≤ b := by
  have hD := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  obtain ⟨η, hη, hs, hu, hone, hd, hr⟩ := exists_range_preserving_cutoff hD hO hK hfront
    (R.imageScalar_contDiffOn hG i).continuousOn hbound
  let e := complexPlaneCoordinates
  have hηE : ContDiff ℝ (⊤ : ℕ∞) (η ∘ e) := hη.comp e.contDiff
  have hdE (x : EuclideanPlane)
      (hx : e x ∉ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :
      fderiv ℝ (η ∘ e) x = 0 := by
    rw [fderiv_comp x (hη.differentiable (by simp) _ ) e.differentiableAt, hd _ hx]
    simp
  have he := W.le_on_cutoff_plateau hsch hG hηE (hs.comp_homeomorph e.toHomeomorph)
    (fun x => hu (e x)) hdE hb (fun x hx hne => hr (e x) hx hne)
  have hm := complexPlaneCoordinates_measurePreserving.symm e.toHomeomorph.toMeasurableEquiv
  filter_upwards [hm.quasiMeasurePreserving.ae he] with z hz hzO
  have honez : η z = 1 := hone.self_of_nhdsSet z hzO
  change η (e (e.symm z)) = 1 → W.scalar (e (e.symm z)) ≤ b at hz
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using honez)

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScalarRegionLowerRange
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower range propagation for the same actual weak scalar. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 local instance instBorelSpaceSphere_58_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem ge_on_closed_region (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    {O : Set ℂ} (hO : IsOpen O) (hK : IsCompact (closure O))
    (hfront : frontier O ⊆ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain))
    {a : ℝ} (ha : a ≤ 1)
    (hbound : ∀ z ∈ closure O,
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      a < R.imageScalar i z) :
    ∀ᵐ z ∂volume, z ∈ closure O → a ≤ W.scalar z := by
  have hD := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  have hc : ContinuousOn (fun z => 1 - R.imageScalar i z)
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :=
    continuousOn_const.sub (R.imageScalar_contDiffOn hG i).continuousOn
  obtain ⟨η, hη, hs, hu, hone, hd, hr⟩ := exists_range_preserving_cutoff hD hO hK hfront hc
    (b := 1 - a) (fun z hz hzi => sub_lt_sub_left (hbound z hz hzi) 1)
  let e := complexPlaneCoordinates
  have hdE (x : EuclideanPlane)
      (hx : e x ∉ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :
      fderiv ℝ (η ∘ e) x = 0 := by
    rw [fderiv_comp x (hη.differentiable (by simp) _) e.differentiableAt, hd _ hx]
    simp
  have hsource := complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae
    (W.eq_source_ae R hsch hG)
  have hcomp := localized_sobolev_range
    (aestronglyMeasurable_const.sub W.boundedRepresentative_measurable)
    (f := fun x => 1 - W.boundedRepresentative x)
    (G := fun x => -W.planarWeakGradient x)
    (fun x => ⟨sub_nonneg.mpr (W.boundedRepresentative_unit x).2,
      sub_le_self 1 (W.boundedRepresentative_unit x).1⟩)
    (fun j => (W.planarWeakGradient_memLp j).neg)
    (complement_weak_gradient W.boundedRepresentative_measurable W.boundedRepresentative_unit
      W.boundedRepresentative_weak)
    (D := e ⁻¹' (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)))
    (fun j => by
      filter_upwards [W.planarWeakGradient_zero_off_image hsch hG j] with x hx hout
      change -W.planarWeakGradient x j = 0
      rw [hx hout, neg_zero])
    (hη.comp e.contDiff) (hs.comp_homeomorph e.toHomeomorph) (fun x => hu (e x)) hdE
    (sub_nonneg.mpr ha) (by
      filter_upwards [hsource, W.boundedRepresentative_ae] with x hx hrep hxin hηx
      rw [hrep]
      change 1 - W.scalar (e x) ≤ 1 - a
      rw [hx hxin]
      exact hr (e x) hxin hηx)
  have hE : ∀ᵐ x ∂volume, (η ∘ e) x = 1 → a ≤ W.scalar (e x) := by
    filter_upwards [hcomp, W.boundedRepresentative_ae] with x hx hrep hηx
    have h := hx hηx
    rw [hrep] at h
    change 1 - W.scalar (e x) ≤ 1 - a at h
    linarith
  have hm := complexPlaneCoordinates_measurePreserving.symm e.toHomeomorph.toMeasurableEquiv
  filter_upwards [hm.quasiMeasurePreserving.ae hE] with z hz hzO
  have honez : η z = 1 := hone.self_of_nhdsSet z hzO
  change η (e (e.symm z)) = 1 → a ≤ W.scalar (e (e.symm z)) at hz
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using honez)

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScalarTerminalRange
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matched terminal contours propagate source scalar ranges
to their entire closed target disks, including all complementary dust. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_59_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem imageScalar_lt_on_terminal (hG : IsOpen d.physicalDomain) (i : Fin m)
    (n : ℕ) (j : Fin (R.limit.cores n).count) {b : ℝ}
    (hb : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
      (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b) :
    ∀ z ∈ closure (jordanInterior (R.limit.contours n j)),
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      R.imageScalar i z < b := by
  have hcap := target_closed_collar_subset_image
    ((R.limit.cores n).disk j) (R.limit.contours n j)
    ((R.limit.cores n).boundary_subset_domain j)
    (R.limit.boundary n j) (R.limit.side n j) (Subset.refl _)
  intro z hz himg
  have hzV : (z : Sphere) ∈ extendAtInfinity R.limit.function '' d.physicalDomain := by
    obtain ⟨x, hx, rfl⟩ := himg
    exact ⟨(x : Sphere), hx, by simp⟩
  obtain ⟨p, ⟨hpG, hpcap⟩, he⟩ := hcap ⟨hzV, z, hz, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hpcap
  have hxz : R.limit.function x = z := OnePoint.coe_injective (by simpa using he)
  rw [← hxz, R.imageScalar_apply hG i hpG]
  exact hb x hx hpG

 theorem terminal_frontier_subset_image (n : ℕ) (j : Fin (R.limit.cores n).count) :
    frontier (jordanInterior (R.limit.contours n j)) ⊆
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) := by
  intro z hz
  obtain ⟨p, hp, he⟩ := (R.limit.boundary n j).symm ▸
    (show (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (R.limit.contours n j)) from
      ⟨z, hz, rfl⟩)
  obtain ⟨x, hx, rfl⟩ := hp
  refine ⟨x, (R.limit.cores n).boundary_subset_domain j ⟨x, hx, rfl⟩, ?_⟩
  exact OnePoint.coe_injective (by simpa using he)

 theorem ScalarWeakLimit.le_on_terminal {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (n : ℕ) (j : Fin (R.limit.cores n).count) {b : ℝ} (hb : 0 ≤ b)
    (hsource : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
      (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b) :
    ∀ᵐ z ∂volume, z ∈ closure (jordanInterior (R.limit.contours n j)) → W.scalar z ≤ b :=
  W.le_on_closed_region hsch hG (jordanInterior_isOpen _)
    (isCompact_closure_jordanInterior _) (R.terminal_frontier_subset_image n j) hb
    (R.imageScalar_lt_on_terminal hG i n j hsource)

 theorem ScalarWeakLimit.ge_on_terminal {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (n : ℕ) (j : Fin (R.limit.cores n).count) {a : ℝ} (ha : a ≤ 1)
    (hsource : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
      (x : Sphere) ∈ d.physicalDomain → a < (Q i).physical (Complex.equivRealProdCLM x)) :
    ∀ᵐ z ∂volume, z ∈ closure (jordanInterior (R.limit.contours n j)) → a ≤ W.scalar z := by
  apply W.ge_on_closed_region hsch hG (jordanInterior_isOpen _)
    (isCompact_closure_jordanInterior _) (R.terminal_frontier_subset_image n j) ha
  have hcap := target_closed_collar_subset_image
    ((R.limit.cores n).disk j) (R.limit.contours n j)
    ((R.limit.cores n).boundary_subset_domain j)
    (R.limit.boundary n j) (R.limit.side n j) (Subset.refl _)
  intro z hz himg
  have hzV : (z : Sphere) ∈ extendAtInfinity R.limit.function '' d.physicalDomain := by
    obtain ⟨x, hx, rfl⟩ := himg
    exact ⟨(x : Sphere), hx, by simp⟩
  obtain ⟨p, ⟨hpG, hpcap⟩, he⟩ := hcap ⟨hzV, z, hz, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hpcap
  have hxz : R.limit.function x = z := OnePoint.coe_injective (by simpa using he)
  rw [← hxz, R.imageScalar_apply hG i hpG]
  exact hsource x hx hpG

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScalarEndIdentification
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single full-measure set satisfies all rational terminal bounds.
Shrinking the actual source caps then identifies the scalar on every
matched target end, even when those ends have positive total area. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 local instance instBorelSpaceSphere_60_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_rational_terminal_bounds (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain) :
    ∀ᵐ z ∂volume,
      (∀ n (j : Fin (R.limit.cores n).count) (b : ℚ), 0 ≤ (b : ℝ) →
        (∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
          (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b) →
        z ∈ closure (jordanInterior (R.limit.contours n j)) → W.scalar z ≤ b) ∧
      (∀ n (j : Fin (R.limit.cores n).count) (a : ℚ), (a : ℝ) ≤ 1 →
        (∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
          (x : Sphere) ∈ d.physicalDomain → (a : ℝ) < (Q i).physical (Complex.equivRealProdCLM x)) →
        z ∈ closure (jordanInterior (R.limit.contours n j)) → (a : ℝ) ≤ W.scalar z) := by
  apply Filter.Eventually.and
  · apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro j
    apply ae_all_iff.2
    intro b
    by_cases hb : 0 ≤ (b : ℝ)
    · by_cases hs : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
          (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b
      · filter_upwards [W.le_on_terminal R hsch hG n j hb hs] with z hz
        exact fun _ _ => hz
      · exact Eventually.of_forall fun _ _ h => (hs h).elim
    · exact Eventually.of_forall fun _ h => (hb h).elim
  · apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro j
    apply ae_all_iff.2
    intro a
    by_cases ha : (a : ℝ) ≤ 1
    · by_cases hs : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
          (x : Sphere) ∈ d.physicalDomain → (a : ℝ) < (Q i).physical (Complex.equivRealProdCLM x)
      · filter_upwards [W.ge_on_terminal R hsch hG n j ha hs] with z hz
        exact fun _ _ => hz
      · exact Eventually.of_forall fun _ _ h => (hs h).elim
    · exact Eventually.of_forall fun _ h => (ha h).elim

 theorem eq_on_all_matched_ends (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    ∀ᵐ z ∂volume, ∀ q : Sphere, ∀ E : RealTargetEnd R.limit q,
      z ∈ E.plane → W.scalar z = (Q i).quotient (π q) := by
  filter_upwards [W.ae_rational_terminal_bounds hsch hG] with z hz q E hzin
  let u : Sphere → ℝ := (Q i).quotient ∘ π
  have huc : Continuous u := hQ.comp hπ
  have huq : u q ∈ Icc 0 1 := (Q i).quotient_unit _
  have hucmp : ∀ p ∈ connectedComponentIn d.physicalDomainᶜ q, u p = u q := by
    intro p hp
    exact congrArg (Q i).quotient (hc q p hp)
  apply le_antisymm
  · by_contra hle
    have hlt : u q < W.scalar z := lt_of_not_ge hle
    obtain ⟨b, hbq, hbz⟩ := exists_rat_btwn hlt
    have hb0 : 0 ≤ (b : ℝ) := huq.1.trans hbq.le
    obtain ⟨n, hn⟩ := (E.eventually_source_values huc hucmp
      (a := -1) (by linarith [huq.1]) hbq).exists
    have hsrc : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk (E.address n))),
        (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b := by
      intro x hx hxG
      rw [(Q i).pullback x hxG]
      exact (hn (x : Sphere) ⟨x, hx, rfl⟩).2
    have hle := hz.1 n (E.address n) b hb0 hsrc (subset_closure (E.plane_inside n hzin))
    exact (not_lt_of_ge hle) hbz
  · by_contra hle
    have hlt : W.scalar z < u q := lt_of_not_ge hle
    obtain ⟨a, hza, haq⟩ := exists_rat_btwn hlt
    have ha1 : (a : ℝ) ≤ 1 := haq.le.trans huq.2
    obtain ⟨n, hn⟩ := (E.eventually_source_values huc hucmp haq
      (b := 2) (by linarith [huq.2])).exists
    have hsrc : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk (E.address n))),
        (x : Sphere) ∈ d.physicalDomain → (a : ℝ) < (Q i).physical (Complex.equivRealProdCLM x) := by
      intro x hx hxG
      rw [(Q i).pullback x hxG]
      exact (hn (x : Sphere) ⟨x, hx, rfl⟩).1
    have hle := hz.2 n (E.address n) a ha1 hsrc (subset_closure (E.plane_inside n hzin))
    exact (not_lt_of_ge hle) hza

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ContinuousScalarRepresentative
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual weak scalar has a continuous representative on the sphere.
The representative uses the source quotient on every matched end. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_61_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
def continuedScalar (hG : IsOpen d.physicalDomain) (i : Fin m) : Sphere → ℝ :=
  (Q i).quotient ∘ R.limit.sourceProjection hG π

 theorem continuedScalar_continuous (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (i : Fin m) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    Continuous (R.continuedScalar hG i) :=
  hQ.comp (R.limit.sourceProjection_continuous hG π hπ hc)

 theorem continuedScalar_on_image (hG : IsOpen d.physicalDomain) (i : Fin m)
    {x : Sphere} (hx : x ∈ d.physicalDomain) :
    R.continuedScalar hG i (extendAtInfinity R.limit.function x) = (Q i).quotient (π x) := by
  unfold continuedScalar
  simp only [comp_apply, R.limit.sourceProjection_on_image hG π hx]

 theorem continuedScalar_eq_imageScalar (hG : IsOpen d.physicalDomain) (i : Fin m)
    {z : ℂ} (hz : z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :
    R.continuedScalar hG i z = R.imageScalar i z := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [R.imageScalar_apply hG i hx, (Q i).pullback x hx]
  exact R.continuedScalar_on_image hG i hx

 theorem ScalarWeakLimit.eq_continuedScalar_ae {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    ∀ᵐ z ∂(volume : Measure ℂ), W.scalar z = R.continuedScalar hG i z := by
  filter_upwards [W.eq_source_ae R hsch hG,
    W.eq_on_all_matched_ends hsch hG hπ hQ hc] with z hz hends
  by_cases him : z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)
  · exact (hz him).trans (R.continuedScalar_eq_imageScalar hG i him).symm
  · have hout : (z : Sphere) ∉ extendAtInfinity R.limit.function '' d.physicalDomain := by
      rintro ⟨p, hp, he⟩
      cases p using OnePoint.rec with
      | infty => exact OnePoint.coe_ne_infty z (by simpa using he.symm)
      | coe x =>
        exact him ⟨x, hp, OnePoint.coe_injective (by simpa only [extendAtInfinity_coe] using he)⟩
    let A := R.limit.chosenSourceEnd hG (z : Sphere) hout
    have hzin : z ∈ A.matching.plane := by
      change (z : Sphere) ∈ connectedComponentIn
        (extendAtInfinity R.limit.function '' d.physicalDomain)ᶜ A.matching.point
      exact (congrArg (fun p : Sphere => p ∈ connectedComponentIn
        (extendAtInfinity R.limit.function '' d.physicalDomain)ᶜ A.matching.point)
        A.point_eq).mp (mem_connectedComponentIn A.matching.outside)
    rw [hends A.source A.matching hzin]
    unfold continuedScalar
    simp only [comp_apply, R.limit.sourceProjection_off_image hG π hout]
    rfl

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ContinuousScalarSobolev
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous representative has the constructed planar weak gradient,
and is Sobolev on every finite-area region. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 local instance instBorelSpaceSphere_62_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem eq_continuedScalar_planar_ae (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    (W.scalar ∘ complexPlaneCoordinates) =ᵐ[volume]
      (fun x => R.continuedScalar hG i (complexPlaneCoordinates x)) :=
  complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae
    (W.eq_continuedScalar_ae R hsch hG hπ hQ hc)

 theorem continuedScalar_weak (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    DeGiorgi.HasWeakGrad W.planarWeakGradient
      (fun x => R.continuedScalar hG i (complexPlaneCoordinates x)) univ := by
  intro j
  apply (W.boundedRepresentative_weak j).congr_ae
  · apply ae_restrict_of_ae
    exact W.boundedRepresentative_ae.trans (W.eq_continuedScalar_planar_ae hsch hG hπ hQ hc)
  · exact Filter.EventuallyEq.rfl

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactScalarContinuation
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar tests vanishing near the source end at infinity continue with
compact planar support. Their global planar Sobolev witness has the actual
weak fields, which vanish off the limiting domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 local instance instBorelSpaceSphere_63_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem continuedScalar_zero_near_infty (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (i : Fin m)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), R.continuedScalar hG i p = 0 := by
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  have hp : R.limit.sourceProjection hG π OnePoint.infty = π OnePoint.infty :=
    R.limit.sourceProjection_on_image hG π hinf
  have ht := (R.limit.sourceProjection_continuous hG π hπ hc).tendsto OnePoint.infty
  rw [hp] at ht
  exact ht.eventually hz

 theorem continuedScalar_hasCompactSupport (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (i : Fin m)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    HasCompactSupport (fun z : ℂ => R.continuedScalar hG i z) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have ht : Tendsto ((↑) : ℂ → Sphere) (coclosedCompact ℂ) (𝓝 OnePoint.infty) :=
    OnePoint.tendsto_coe_infty
  exact ht.eventually (R.continuedScalar_zero_near_infty hG hπ i hc hz)

 def ScalarWeakLimit.continuedScalar_witness {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    DeGiorgi.MemW1pWitness 2
      (fun x => R.continuedScalar hG i (complexPlaneCoordinates x)) univ where
  memLp := by
    rw [Measure.restrict_univ]
    exact ((R.continuedScalar_continuous hG hπ i hQ hc).comp
      (OnePoint.continuous_coe.comp complexPlaneCoordinates.continuous)).memLp_of_hasCompactSupport
        ((R.continuedScalar_hasCompactSupport hG hπ i hc hz).comp_homeomorph
          complexPlaneCoordinates.toHomeomorph)
  weakGrad := W.planarWeakGradient
  weakGrad_component_memLp j := by
    simpa only [Measure.restrict_univ] using W.planarWeakGradient_memLp j
  isWeakGrad := W.continuedScalar_weak hsch hG hπ hQ hc

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ProjectedPlaneFunction
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continue any compact planar test through the actual matched-end
projection. This construction does not require the test to be smooth. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d id} (R : RetainedRealCircleModel d id Q)

 local instance instBorelSpaceSphere_64_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
def projectedPlaneFunction (hG : IsOpen d.physicalDomain) (u : EuclideanPlane → ℝ) :
    Sphere → ℝ := sphereFromPlaneFunction u ∘ R.limit.sourceProjection hG id

 theorem projectedPlaneFunction_continuous (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u) :
    Continuous (R.projectedPlaneFunction hG u) := by
  have huc : Continuous (sphereFromPlaneFunction u) := continuousOn_univ.mp
    (sphereFromPlaneFunction_continuousOn isOpen_univ hu.continuousOn hs.isCompact
      (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  exact huc.comp (R.limit.sourceProjection_continuous hG id continuous_id hc)

 theorem projectedPlaneFunction_hasCompactSupport (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {u : EuclideanPlane → ℝ} (hs : HasCompactSupport u) :
    HasCompactSupport (fun x => R.projectedPlaneFunction hG u (planeSphere x)) := by
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  have hS := (R.limit.sourceProjection_continuous hG id continuous_id hc).tendsto OnePoint.infty
  have hSinf : R.limit.sourceProjection hG id OnePoint.infty = OnePoint.infty :=
    R.limit.sourceProjection_on_image hG id hinf
  rw [hSinf] at hS
  have hzero := hS.eventually (sphereFromPlaneFunction_zero_near_infty hs)
  have ht : Tendsto ((↑) : ℂ → Sphere) (coclosedCompact ℂ) (𝓝 OnePoint.infty) :=
    OnePoint.tendsto_coe_infty
  have hh : HasCompactSupport (fun z : ℂ => R.projectedPlaneFunction hG u z) := by
    rw [hasCompactSupport_iff_eventuallyEq]
    exact ht.eventually hzero
  exact hh.comp_homeomorph complexPlaneCoordinates.toHomeomorph

 theorem projectedPlaneFunction_zero_off_image (hG : IsOpen d.physicalDomain)
    {u : EuclideanPlane → ℝ} (hz : ∀ x ∉ physicalPlaneDomain d.physicalDomain, u x = 0)
    {p : Sphere} (hp : p ∉ extendAtInfinity R.limit.function '' d.physicalDomain) :
    R.projectedPlaneFunction hG u p = 0 := by
  rw [projectedPlaneFunction, comp_apply, R.limit.sourceProjection_off_image hG id hp]
  let A := R.limit.chosenSourceEnd hG p hp
  change sphereFromPlaneFunction u A.source = 0
  have hA : A.source ∉ d.physicalDomain := A.outside
  cases hq : A.source using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    rw [sphereFromPlaneFunction_coe]
    apply hz
    change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∉ d.physicalDomain
    simpa only [ContinuousLinearEquiv.apply_symm_apply, hq] using hA

 theorem projectedPlaneFunction_on_image (hG : IsOpen d.physicalDomain)
    (u : EuclideanPlane → ℝ) {p : Sphere} (hp : p ∈ d.physicalDomain) :
    R.projectedPlaneFunction hG u (extendAtInfinity R.limit.function p) =
      sphereFromPlaneFunction u p := by
  rw [projectedPlaneFunction, comp_apply, R.limit.sourceProjection_on_image hG id hp]
  rfl

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ProjectedZeroTrace
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-trace error for a retained circle model has an actual global
Sobolev continuation with zero complementary gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d id} (R : RetainedRealCircleModel d id Q)

 local instance instBorelSpaceSphere_65_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem projectedPlaneFunction_zero_trace_witness
    (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ physicalPlaneDomain d.physicalDomain, u x = 0)
    (H : DeGiorgi.MemW1pWitness 2 u univ) :
    ∃ K : DeGiorgi.MemW1pWitness 2
      (fun x => R.projectedPlaneFunction hG u (planeSphere x)) univ,
      (∀ i : Fin 2, ∀ x ∉ physicalPlaneDomain
        (extendAtInfinity R.limit.function '' d.physicalDomain), K.weakGrad x i = 0) ∧
      (∫ x, K.weakGrad x 0 ^ 2 + K.weakGrad x 1 ^ 2) ≤
        ∫ x in physicalPlaneDomain d.physicalDomain, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2 := by
  let f := extendAtInfinity R.limit.function
  let V := f '' d.physicalDomain
  have hV : IsOpen V := R.limit.conformal.1.isOpen_image hG hG (Subset.refl _)
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  obtain ⟨fi, heq⟩ := R.limit.conformal.exists_smooth_inverse hG hV
  change IsSmoothSphereEquivalence f fi d.physicalDomain V at heq
  have hv : EqOn (fun x => R.projectedPlaneFunction hG u (planeSphere x))
      (planeInverseTransport fi u) (physicalPlaneDomain V) := by
    intro x hx
    have hr := R.projectedPlaneFunction_on_image hG u (heq.mapsTo_inv hx)
    change R.projectedPlaneFunction hG u (f (fi (planeSphere x))) = _ at hr
    rw [heq.right_inv _ hx] at hr
    refine hr.trans ?_
    change sphereFromPlaneFunction u (fi (planeSphere x)) =
      u (complexPlaneCoordinates.symm (finiteCoord (fi (planeSphere x))))
    have hfinite : fi (planeSphere x) ≠ OnePoint.infty := heq.finite_inv hinf rfl hx
    rw [sphereFromPlaneFunction, ite_eq_right hfinite]
  exact zero_trace_conformal_transport heq hG hV hinf rfl R.limit.conformal.1 hu hs H hv
    ((R.projectedPlaneFunction_continuous hG hc hu hs).comp continuous_planeSphere)
    (R.projectedPlaneFunction_hasCompactSupport hG hc hs)
    (fun x hx => R.projectedPlaneFunction_zero_off_image hG hz hx)

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarContinuationEnergy
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact continuous continuation retains the sharp source energy
and the zero gradient on the actual complementary set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 theorem planarWeakGradient_energy :
    (∫ x, W.planarWeakGradient x 0 ^ 2 + W.planarWeakGradient x 1 ^ 2) ≤
      ∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
  change (∫ x, W.horizontal (complexPlaneCoordinates x) ^ 2 +
    W.vertical (complexPlaneCoordinates x) ^ 2) ≤ _
  rw [complexPlaneCoordinates_measurePreserving.integral_comp
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding
    (fun z => W.horizontal z ^ 2 + W.vertical z ^ 2)]
  exact W.energy

 theorem planarWeakGradient_energy_integrable :
    Integrable (fun x => W.planarWeakGradient x 0 ^ 2 + W.planarWeakGradient x 1 ^ 2) :=
  (W.planarWeakGradient_memLp 0).integrable_sq.add
    (W.planarWeakGradient_memLp 1).integrable_sq

 theorem continuedScalar_gradient_zero (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) (j : Fin 2) :
    ∀ᵐ x ∂volume, complexPlaneCoordinates x ∉
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      (W.continuedScalar_witness R hsch hG hπ hQ hc hz).weakGrad x j = 0 :=
  W.planarWeakGradient_zero_off_image hsch hG j

 theorem continuedScalar_energy (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    (∫ x, (W.continuedScalar_witness R hsch hG hπ hQ hc hz).weakGrad x 0 ^ 2 +
      (W.continuedScalar_witness R hsch hG hπ hQ hc hz).weakGrad x 1 ^ 2) ≤
      ∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x :=
  W.planarWeakGradient_energy

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RetainedSobolevContinuations
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Sobolev continuations of the retained smooth scalar tests.
The exterior coefficient area theorem controls the weak limits. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem exists_continuation_witness (harea : ExteriorCoefficientAreaTheorem)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (i : Fin m) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    ∃ H : DeGiorgi.MemW1pWitness 2
      (fun x => R.continuedScalar hG i (complexPlaneCoordinates x)) univ,
      (∀ j : Fin 2, ∀ᵐ x ∂volume, complexPlaneCoordinates x ∉
        R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) → H.weakGrad x j = 0) ∧
      Integrable (fun x => H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2) ∧
      (∫ x, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2) ≤
        ∫ x in realChartDomain d.physicalDomain,
          gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
  obtain ⟨W⟩ := R.exists_scalar_weak_limit harea i hQ
  exact ⟨W.continuedScalar_witness R hsch hG hπ hQ hc hz,
    W.continuedScalar_gradient_zero hsch hG hπ hQ hc hz,
    W.planarWeakGradient_energy_integrable, W.continuedScalar_energy hsch hG hπ hQ hc hz⟩

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedOriginalTest
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Add the constructed zero-trace error back to a retained smooth test.
The result is the continuation of the original test on the same model. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

local instance instBorelSpaceSphere_66_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem sphereFromPlaneFunction_sub (u v : EuclideanPlane → ℝ) (p : Sphere) :
    sphereFromPlaneFunction (fun x => u x - v x) p =
      sphereFromPlaneFunction u p - sphereFromPlaneFunction v p := by
  classical
  by_cases hp : p = OnePoint.infty <;> simp [sphereFromPlaneFunction, hp]

namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d id} (R : RetainedRealCircleModel d id Q)

 local instance instBorelSpaceSphere_66_r5345e3_2 : BorelSpace Sphere := ⟨rfl⟩
theorem original_test_witness
    (harea : ExteriorCoefficientAreaTheorem) (hsch : PlanarSchoenflies)
    (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    (i : Fin m) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hus : HasCompactSupport u)
    (hv : Continuous v) (hvs : HasCompactSupport v)
    (hQ : (Q i).quotient = sphereFromPlaneFunction v)
    (htrace : EqOn v u (physicalPlaneDomain d.physicalDomain)ᶜ)
    (D : DeGiorgi.MemW1pWitness 2 (fun x => u x - v x) univ) :
    ∃ H : DeGiorgi.MemW1pWitness 2
      (fun x => R.projectedPlaneFunction hG u (planeSphere x)) univ,
      ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ physicalPlaneDomain
        (extendAtInfinity R.limit.function '' d.physicalDomain) → H.weakGrad x j = 0 := by
  have hQc : Continuous (Q i).quotient := by
    rw [hQ]
    exact continuousOn_univ.mp (sphereFromPlaneFunction_continuousOn isOpen_univ
      hv.continuousOn hvs.isCompact (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  have hQzero : ∀ᶠ p in 𝓝 (id (OnePoint.infty : Sphere)), (Q i).quotient p = 0 := by
    rw [hQ]
    exact sphereFromPlaneFunction_zero_near_infty hvs
  obtain ⟨S, hS, _⟩ := R.exists_continuation_witness harea hsch hG continuous_id i hQc hc hQzero
  have hz : ∀ x ∉ physicalPlaneDomain d.physicalDomain, u x - v x = 0 := by
    intro x hx
    rw [htrace hx, sub_self]
  obtain ⟨K, hK, _⟩ := R.projectedPlaneFunction_zero_trace_witness hG hc
    (hu.sub hv) (hus.sub hvs) hz D
  have hsum : (fun x => R.projectedPlaneFunction hG (fun y => u y - v y) (planeSphere x) +
      R.continuedScalar hG i (planeSphere x)) =
      (fun x => R.projectedPlaneFunction hG u (planeSphere x)) := by
    funext x
    simp only [projectedPlaneFunction, continuedScalar, comp_apply, hQ,
      sphereFromPlaneFunction_sub, sub_add_cancel]
  let H := (K.add S).congr_ae (Eventually.of_forall fun x => congrFun hsum x)
  refine ⟨H, ?_⟩
  intro j
  filter_upwards [hS j] with x hx hxV
  have hnot : complexPlaneCoordinates x ∉
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) := by
    rintro ⟨z, hz, he⟩
    apply hxV
    exact ⟨(z : Sphere), hz, congrArg ((↑) : ℂ → Sphere) he⟩
  change K.weakGrad x j + S.weakGrad x j = 0
  rw [hK j x hxV, hx hnot, add_zero]

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ExactTraceFamily
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A whole finite list has simultaneous exact-trace replacements. The
original pair-null condition passes unchanged to these actual coordinates,
and a retained model of them is a Sobolev model of every original test. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace RetainedRealCircleModel

 local instance instBorelSpaceSphere_67_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem exactTraceTest_original_witness
    (harea : ExteriorCoefficientAreaTheorem) (hsch : PlanarSchoenflies)
    {d : PathCodeData Sphere Sphere} (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {m : ℕ} {u : Fin m → EuclideanPlane → ℝ} (T : ∀ i, ExactTraceTest d (u i))
    (R : RetainedRealCircleModel d id (fun i => (T i).coordinate))
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i)) (i : Fin m) :
    ∃ H : DeGiorgi.MemW1pWitness 2
      (fun x => R.projectedPlaneFunction hG (u i) (planeSphere x)) univ,
      ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ physicalPlaneDomain
        (extendAtInfinity R.limit.function '' d.physicalDomain) →
          H.weakGrad x j = 0 :=
  R.original_test_witness harea hsch hG hc i (hu i) (hs i) (T i).continuous (T i).compact
    (T i).coordinate_eq (T i).trace (T i).error

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedComponentCorrespondence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed correspondence on the full spheres. On the domain it is
the conformal map; over a complementary component its fiber is the
whole matching component. This includes disk-to-point and point-to-disk
matches, where a continuous single-valued extension need not exist. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem componentRelation_source_fiber (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q : Sphere} (hq : q ∈ Gᶜ) :
    ∃ p ∈ (f '' G)ᶜ, {p' | D.componentRelation q p'} = connectedComponentIn (f '' G)ᶜ p := by
  obtain ⟨b,p,hp,hs,ht,_⟩ := corresponding_target_end_of_source hG hf.1 hf.bijOn.injOn
    D.cores D.disks D.strict D.cover D.disjoint D.complement D.boundary D.side hq
  refine ⟨p,hp,?_⟩
  ext p'
  constructor
  · intro h
    rw [ht]
    apply mem_iInter.mpr
    intro n
    rcases (D.relationStage_iff n q p').mp (mem_iInter.mp h n) with hg | ⟨i,hqi,hpi⟩
    · exact (hq ((D.cores n).subset hg.1)).elim
    · have hqb : q ∈ closedTerminalCap ((D.cores n).disk (b n)) :=
        mem_iInter.mp (hs ▸ mem_connectedComponentIn hq) n
      have hi : i = b n := by
        by_contra hne
        exact Set.disjoint_left.mp (disjoint_closedTerminalCaps _ (D.cores n).disjoint hne) hqi hqb
      simpa only [hi] using hpi
  · intro h
    apply mem_iInter.mpr
    intro n
    apply (D.relationStage_iff n q p').mpr
    exact Or.inr ⟨b n,mem_iInter.mp (hs ▸ mem_connectedComponentIn hq) n,
      mem_iInter.mp (ht ▸ h) n⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentRelationSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual selections from the matched component correspondence. They
agree with the conformal map on the domain, are constant on each omitted
component, and are continuous at every singleton target fiber. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem targetFiber_nonempty (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (q : Sphere) : (D.targetFiber q).Nonempty := by
  by_cases hq : q ∈ G
  · exact ⟨f q,D.componentRelation_graph hf hq⟩
  · obtain ⟨p,hp,he⟩ := D.componentRelation_source_fiber hG hf hq
    refine ⟨p,?_⟩
    change p ∈ {p' | D.componentRelation q p'}
    rw [he]
    exact mem_connectedComponentIn hp

 def selectedTarget (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (q : Sphere) : Sphere := (D.targetFiber_nonempty hG hf q).some

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedScalarIntervals
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual intervals for the matched disks. Their lengths are square
summable and their centers represent values of the closed correspondence.
Unused natural codes are harmless shrinking intervals at one fixed fiber. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}

variable [Encodable D.IndexedMatchedPair]

 def MatchedRoundDisks.traceScalarCenter (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ) : ℕ → ℝ :=
  traceEnumeration (fun j => φ (E.targetCenter j : Sphere))
    (φ (D.selectedTarget hG hf (0 : ℂ)))

 def MatchedRoundDisks.traceInterval (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ)
    (L : ℝ≥0) (n : ℕ) : Set ℝ :=
  Ioo (E.traceScalarCenter hG hf φ n-E.traceWidth L n)
      (E.traceScalarCenter hG hf φ n+E.traceWidth L n)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedRealMaskData
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Data of the actual scalar masks used in the axial trace argument.
All fields are constructed from the matched disks and the planar maximal input. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 def realSelectedScalar (D : MatchedConformalEnds G f) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ) (p : ℝ × ℝ) : ℝ :=
  φ (D.selectedTarget hG hf (Complex.equivRealProdCLM.symm p : Sphere))

 def realMaskValue (D : MatchedConformalEnds G f) [Encodable D.IndexedMatchedPair] (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (φ : Sphere → ℝ) (L : ℝ≥0) (cutoff : ℕ → (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : ℝ :=
  infiniteTracePrimitive cutoff (E.traceInterval hG hf φ L) 0 p (D.realSelectedScalar hG hf φ p)

 structure MatchedRealMask (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ) (L : ℝ≥0) (m : ℕ) where
  cutoff : ℕ → (ℝ × ℝ) → ℝ
  smooth : ∀ n, ContDiff ℝ 1 (cutoff n)
  unit : ∀ n p, cutoff n p ∈ Icc (0:ℝ) 1
  zero : ∀ n p, ‖Complex.equivRealProdCLM.symm p-E.traceCenter n‖ ≤
    traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n → cutoff n p = 0
  outer : ∀ n p, traceBalloonRadius E.traceRadius m n ≤
    ‖Complex.equivRealProdCLM.symm p-E.traceCenter n‖ → cutoff n p = 1
  density : (ℝ × ℝ) → ℝ
  density_measurable : Measurable density
  density_nonneg : ∀ p, 0 ≤ density p
  density_memLp : MemLp density 2 volume
  pays : ∀ᵐ p ∂volume, ∀ n, ∑ j ∈ Finset.range n,
    volume.real (E.traceInterval hG hf φ L j)*‖fderiv ℝ (cutoff j) p‖ ≤ density p
  neighborhood : D.IndexedMatchedPair → Set ℂ
  neighborhood_open : ∀ j, IsOpen (neighborhood j)
  neighborhood_contains : ∀ j, closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ neighborhood j
  neighborhood_zero : ∀ j z, z ∈ neighborhood j → cutoff (Encodable.encode j) (Complex.equivRealProdCLM z) = 0 ∧
    φ (D.selectedTarget hG hf (z : Sphere)) ∈ E.traceInterval hG hf φ L (Encodable.encode j)
  continuous : Continuous (D.realMaskValue E hG hf φ L cutoff)
  compact : HasCompactSupport (D.realMaskValue E hG hf φ L cutoff)
  domain_open : IsOpen (maskDomain G neighborhood)
  domain_connected : IsConnected (maskDomain G neighborhood)
  domain_dust : IsTotallyDisconnected (maskDomain G neighborhood)ᶜ
  domain_removable : IsConformallyRemovable (maskDomain G neighborhood)ᶜ

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_PointDustModels
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source data and a common exterior zero anchor for a finite family of
compact tests on a point-complement sphere domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

local instance instBorelSpaceSphere_68_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
def pointDustPathData (G A : Set Sphere) : PathCodeData Sphere Sphere where
  physicalDomain := G
  quotientDomain := G
  domainEquiv := Homeomorph.refl G
  basePoint := OnePoint.infty
  dust := Gᶜ
  levels := fun _ => ∅
  priorLaws := fun _ => 0
  priorDeletions := fun _ _ => ∅
  flagDeletions := fun _ => ∅
  levelWeights := fun _ _ => 0
  anchor := A
  target := OnePoint.infty
  gateContours := fun _ => ∅
  gateSets := fun _ => ∅

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactScalarCircleModel
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A circle model of the original compact scalar list, with its actual
continuous collapse map and global Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace RetainedRealCircleModel

 local instance instBorelSpaceSphere_69_r5345e3_1 : BorelSpace Sphere := ⟨rfl⟩
def compactScalarCircleModel
    (harea : ExteriorCoefficientAreaTheorem) (hsch : PlanarSchoenflies)
    {d : PathCodeData Sphere Sphere} (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {m : ℕ} {u : Fin m → EuclideanPlane → ℝ} (T : ∀ i, ExactTraceTest d (u i))
    (R : RetainedRealCircleModel d id (fun i => (T i).coordinate))
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i)) :
    CompactScalarCircleModel d.physicalDomain u := by
  classical
  choose H hH using fun i => R.exactTraceTest_original_witness harea hsch hG hc T hu hs i
  refine {
    function := R.limit.function
    normalized := R.limit.normalized
    conformal := R.limit.conformal
    circle := R.circle
    projection := R.limit.sourceProjection hG id
    projection_continuous := R.limit.sourceProjection_continuous hG id continuous_id hc
    projection_inverse := fun p hp => R.limit.sourceProjection_on_image hG id hp
    projection_outside := ?_
    projection_component := ?_
    witness := H
    gradient_zero := hH }
  · intro p hp
    rw [R.limit.sourceProjection_off_image hG id hp]
    exact (R.limit.chosenSourceEnd hG p hp).outside
  · intro p hp q hq
    let A := R.limit.chosenSourceEnd hG p hp
    have hq' : q ∈ connectedComponentIn
        (extendAtInfinity R.limit.function '' d.physicalDomain)ᶜ A.matching.point := by
      rwa [A.point_eq]
    calc
      R.limit.sourceProjection hG id q = A.source :=
        A.matching.sourceProjection_eq hG id hc hq'
      _ = R.limit.sourceProjection hG id p := (R.limit.sourceProjection_off_image hG id hp).symm

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_FiniteMatchedField
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selected matched field is finite, measurable, and bounded
on every compact part of the source plane. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_73
def selectedPlane (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (z : ℂ) : ℂ :=
    finiteCoord (D.selectedTarget hG hf (z : Sphere))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrescribedScalarSeed
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed finite scalar list with null trace pairs gives actual
selectable real seed coordinates, with unchanged functions and zero bands. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 def PhysicalRealCoordinate.continuousTest
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    (Q : PhysicalRealCoordinate d π) (hQ : Continuous Q.quotient)
    (hz : ∀ x ∈ EStar, Q.quotient x = 0) (hdense : Dense d.quotientDomain) :
    UngatedRealTest d π EStar where
  coordinate := Q
  region := ∅
  region_open := isOpen_empty
  zero := hz
  one := fun _ hx => hx.1.elim
  exclusions := ∅
  exclusions_countable := countable_empty
  weight := fun _ => 0
  weight_finite := by simp
  weight_support := by simp
  band_bound := by
    intro x _
    let : NeBot (𝓝[d.quotientDomain] x) := mem_closure_iff_nhdsWithin_neBot.mp (hdense x)
    have ht := hQ.continuousAt.continuousWithinAt.tendsto (s := d.quotientDomain) (x := x)
    rw [ht.limsup_eq, ht.liminf_eq, sub_self, ENNReal.ofReal_zero]

 def finiteScalarSeedTests
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (Q : Fin m → UngatedRealTest d π EStar) : ℕ → UngatedRealTest d π EStar
  | 0 => UngatedRealTest.zeroTest d π EStar
  | n + 1 => if h : n < m then Q ⟨n, h⟩ else UngatedRealTest.zeroTest d π EStar

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ScalarCircleModel
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The null trace-pair hypothesis gives a circle-domain model retaining
exactly the prescribed continuous smooth scalar tests. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 def RetainedRealCircleModel.select
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m k : ℕ}
    {Q : Fin m → PhysicalRealCoordinate d π} (M : RetainedRealCircleModel d π Q)
    (f : Fin k → Fin m) : RetainedRealCircleModel d π (Q ∘ f) where
  marks := M.marks
  marks_countable := M.marks_countable
  coordinates := M.coordinates
  source := M.source
  model := M.model
  limit := M.limit
  circle := M.circle
  index := M.index ∘ f
  physical := fun i => M.physical (f i)
  quotient := fun i => M.quotient (f i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.GeneratedStructure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.overlayGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Generated matched cell structures

The spine of Part II. `def:generated-structure` says that every cell structure the Schönflies
construction ever meets is obtained from the initial two-face structure of
`prop:initial-pair` by a finite sequence of two elementary operations — *edge subdivision* and
*2-cell splitting by an ear* — performed simultaneously in the two realizations. This module
builds the two operations as `def`s on `Schoenflies.CellStructure`, closes them into the
inductive `Schoenflies.GeneratedStructure`, and proves the assertions of
`lem:cellulation-invariants` that are within reach.

## Blueprint

* `Schoenflies.CellStructure.SubdivData`, `Schoenflies.CellStructure.subdivideEdge` — the first
  elementary operation of `def:generated-structure` (tex, operation 1).
* `Schoenflies.CellStructure.SplitData`, `Schoenflies.CellStructure.splitFace` — the second
  (tex, operation 2).
* `Schoenflies.GeneratedStructure` — `def:generated-structure`, as the inductive closure of a
  base structure under the two operations.
* `Schoenflies.CellStructure.SubdivData.parent`,
  `Schoenflies.CellStructure.SplitData.parent`,
  `Schoenflies.CellStructure.SubdivData.sub_parent`,
  `Schoenflies.CellStructure.SplitData.sub_parent` — assertion (iv) of
  `lem:cellulation-invariants`, the parent map of one elementary refinement and the
  compatibility `σ ≼ τ → par σ ≼ par τ`.
* `Schoenflies.CellStructure.CombInvariants`, its two preservation theorems
  `Schoenflies.CellStructure.SubdivData.combInvariants` and
  `Schoenflies.CellStructure.SplitData.combInvariants`, and
  `Schoenflies.GeneratedStructure.combInvariants`, which closes the induction — assertions
  (iii), (v), (vi), together with the abstract form of (viii) and the bookkeeping facts about
  `≼_abs` that the blueprint uses silently.
* `Schoenflies.GeneratedStructure.trans` — refinement sequences compose.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition` — assertion (i) for one
  realization, and from it, with no further geometry:
  `.frontier_property` (assertion (ii)), `.sub_iff_subset_closure` and
  `Schoenflies.CellStructure.subset_closure_congr` (assertion (ix)), and `.face_eq`
  (assertion (viii)).
* `Schoenflies.CellStructure.SubdivData.IsRefinement` and
  `Schoenflies.CellStructure.SubdivData.IsRefinement.isCellDecomposition` — the induction step
  of assertion (i) over the *first* constructor: a realization of the subdivided structure that
  refines a realization of the old one inherits (i).
* `Schoenflies.crosscut_cell_partition` — the geometric content of one 2-cell split, from
  `Schoenflies.general_crosscut`, in the shape assertion (i) consumes.

**Not here.** The induction step of (i) over the *second* constructor, and assertion (vii) in
either. `crosscut_cell_partition` is the geometric input the split step needs; what is missing
is the `SplitData` analogue of `IsRefinement` — a relation between a realization of
`S.splitFace d` and one of `S`, saying that the ear is drawn as a crosscut of the realized open
2-cell — and the identification of the abstract boundary walk of a 2-cell with the Jordan curve
of assertion (vii). Assertions (ii), (viii) and (ix) are stated here against `(i)` as a
hypothesis, so later constructors can use the resulting theorem directly.

Two general graph facts are proved here for want of a home: `Schoenflies.subdivGraph` (with
`Schoenflies.subdivGraph_mono` and `Schoenflies.subdivGraph_eq_self`) and
`Schoenflies.isLink_of_le_of_mem_edgeSet`. The second belongs in `Schoenflies/Graph/`; nothing
on `main` states it.

## Design

**The base case is a parameter.** `prop:initial-pair` is being built elsewhere, so
`GeneratedStructure S₀ S` is relative to an arbitrary base `S₀`, and every invariant theorem
reads "the invariants of `S₀` propagate to `S`". That is both cleaner and independent of the
initial pair's schedule: the consumer supplies `S₀` and the base case, and gets the invariant
at every stage.

**`rem:intermediate-disconnection` is honoured by omission.** Nothing in this module mentions
`Realization.nonboundary`, let alone its connectedness: an intermediate stage really can have
disconnected open nonboundary part, and every statement here is proved without that hypothesis.

**`≼_abs` stays a raw datum.** `CellStructure.sub` is not made a preorder. The reflexivity and
transitivity facts that the blueprint uses are fields of `CombInvariants`, established for the
base and propagated, never assumed of an arbitrary `CellStructure`.

**Fidelity note on reflexivity.** The blueprint's two update lists (tex, operations 1 and 2)
do not mention the reflexive pairs of the *new* cells, while the base relation is declared to
contain "the reflexive pairs". Assertion (i) forces them: the closure of a new open cell
contains that cell, and (i) says a closed cell is the union of its open subcells. Both `subRel`
definitions below therefore declare `σ ≼ σ` for every new cell; that is the only place where
this module adds a pair the blueprint's prose does not list.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Schoenflies

variable {γ : Type*}

/-! ### Subdividing an edge of a graph

The graph-theoretic half of the first elementary operation, stated for an arbitrary graph so
that one definition serves both the skeleton and the outer cycle: when `H` does not carry `e`
from `x` to `y` — which is the case for the outer cycle whenever the subdivided edge is not an
outer edge — the construction leaves `H` alone (`subdivGraph_eq_self`). Without that, the
definition of `CellStructure.subdivideEdge` would need a case split on whether the subdivided
edge is outer, and every lemma about it would inherit the split. -/

variable {H K : Graph γ γ} {e x y v e₁ e₂ : γ}

/-! ### The cells of an abstract structure -/

/-! ### Generated matched cell structures -/

namespace CellStructure

/-! ### The combinatorial invariants

Assertions (iii), (v) and (vi) of `lem:cellulation-invariants`, together with the abstract form
of (viii) and the bookkeeping facts about `≼_abs` that the blueprint's proof uses without
comment (the relation relates cells to cells, it is reflexive, and a vertex is below each edge
it bounds). They are bundled because the induction propagates them together: the preservation
proof of each one reads the others at the previous stage. -/

/-! ### Edge subdivision preserves the combinatorial invariants -/

/-! ### A 2-cell split preserves the combinatorial invariants -/

/-! ### The invariants at every stage -/

/-! ### The geometric assertions

Assertion (i) is the only geometric input the rest need: (ii), (viii) and (ix) follow from it
formally, with no further topology beyond "a nonempty open set contained in a closure meets the
set". That is why they are stated here for an arbitrary realization satisfying (i), rather than
by induction: the induction is entirely in (i) and (vii), and those are the standing gap of this
module. -/

namespace Realization

namespace IsCellDecomposition

variable {S : CellStructure γ} {R : S.Realization} {D : Set Plane} {σ τ ρ : γ}

/-- …and transitive, for the same reason. -/
theorem sub_trans (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) (hτ : τ ∈ S.cells)
    (hρ : ρ ∈ S.cells) (h₁ : S.sub σ τ) (h₂ : S.sub τ ρ) : S.sub σ ρ := by
  refine h.sub_of_subset_closure hσ hρ ((h.subset_closure hσ hτ h₁).trans ?_)
  simpa using closure_mono (h.subset_closure hτ hρ h₂)

end IsCellDecomposition

end Realization

/-! ### Assertion (i) is preserved by an edge subdivision

The induction step of (i) over the first constructor. It relates two realizations of two
different structures, so it needs a name for "`R'` refines `R` along `d`": that is
`SubdivData.IsRefinement`, whose fields are exactly the blueprint's sentence "the corresponding
point is inserted into the corresponding edge using the edge parametrization", read as a
statement about the resulting open cells and their closures. -/

end CellStructure

/-! ### The geometric content of one 2-cell split

`thm:general-crosscut` is what the induction step of assertions (i) and (vii) applies at each
split. The two hypotheses it still carries on `main` — `thm:jordan` and `HasArcCollars` — are
threaded through verbatim; both are being discharged elsewhere. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialPairFixed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.relabelDrawing_apply _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The complete construction of `prop:initial-pair`

`Schoenflies/InitialPair.lean` builds the initial matched pair but leaves three things that
`def:matched-pair` and `prop:initial-pair` actually assert:

1. **the anchor clause.** The blueprint chooses `a, b ∈ 𝒜`, the fixed countable dense set of
   *strongly accessible* points of `prop:countable-strong-access` (tex 1403–1418). `InitialData`
   records neither the anchor set nor the strong accessibility of `a` and `b`, so nothing
   downstream can build a further crosscut ending at them, and `lem:anchor-density` — which
   needs the anchors of every stage to be points of `𝒜` — has nothing to attach to.
   `Schoenflies.AnchorSet` is `𝒜` as data, `Schoenflies.AnchoredInitialData` is the initial pair
   with the clause recorded, and `Schoenflies.AnchoredInitialData.stronglyAccessible_a` /
   `.exists_access_segment_a` turn it back into the straight access segment `lem:tangent-cone`
   supplies.
2. **the matched labelling.** `InitialData.source_closure_cell_inter` labels the two source
   2-cells by the two boundary arcs `A₁, A₂` of `C`, and `.target_closure_cell_inter` labels the
   two target 2-cells by the two boundary arcs of `S` — independently. Nothing said the two
   labellings correspond, which is the whole content of a *matched* pair.
   `Schoenflies.InitialData.tgt_arcOf_eq_image` (`tgt.arcOf k = u '' src.arcOf k`),
   `.skeletonHomeo_image_arcOf` and `.closure_cell_face_link` supply the link.
3. **`def:admissible-graph` for the target**: "all its edges are polygonal".
   `Schoenflies.InitialData.isPolygonal_tgt_edgeArc` and
   `.isPolygonal_targetRealization_skeletonSet`.

It also carried two hypotheses, `harc` (`thm:arc-complement`) and `hcollars`
(`lem:crosscut-collars`), both of which are now theorems on `main`
(`Schoenflies.arc_complement`, `Schoenflies.IsCrosscut.hasArcCollars`). Every headline result is
restated here after supplying them; the primed names distinguish these strengthened statements.

Finally, `initBoundary` is a raw datum in `CellStructure`, and nothing checked that the two
lists it holds are closed walks of `initSkel` whose cells are exactly `faceCells`. They are:
`Schoenflies.isWalk_initBoundary_false`, `.._true`, and `Schoenflies.mem_faceCells_iff`.

## Blueprint

* `Schoenflies.AnchorSet`, `Schoenflies.nonempty_anchorSet`, `Schoenflies.anchorSet` —
  `prop:countable-strong-access` as the *fixed* set `𝒜` of tex 1418.
* `Schoenflies.AnchoredInitialData`, `Schoenflies.exists_anchoredInitialData`,
  `Schoenflies.anchoredInitialData`, `Schoenflies.initialData` — `prop:initial-pair` including
  the dropped clause "two further points `a, b ∈ 𝒜`", the last one with the canonical anchor
  set supplied.
* `Schoenflies.stronglyAccessible_initialData_a`, `.._b` — the strong accessibility of the two
  chosen points of the canonical pair, which is what the dropped clause was *for*.
* `Schoenflies.AnchoredInitialData.stronglyAccessible_a`, `.stronglyAccessible_b`,
  `.exists_access_segment_a`, `.exists_access_segment_b` — `lem:tangent-cone` at the two
  anchors, the form `lem:accessible-endpoints` consumes at every later stage.
* `Schoenflies.isWalk_initBoundary_false`, `Schoenflies.isWalk_initBoundary_true`,
  `Schoenflies.mem_faceCells_iff`, `Schoenflies.boundaryCycles_initialStructure` — the boundary
  datum of `def:matched-cellulation` really is the simple boundary cycle of each 2-cell and
  carries exactly its strict subcells.
* `Schoenflies.HexData.isPolygonal_arcOf`, `.isPolygonal_outerArcs`,
  `Schoenflies.isPolygonal_modelCurve`, `Schoenflies.InitialData.isPolygonal_tgt_edgeArc`,
  `.isPolygonal_targetRealization_skeletonSet` — the clause "all its edges are polygonal" of
  `def:admissible-graph` for the target realization.
* `Schoenflies.InitialData.src_arcOf_eq_image`, `.tgt_arcOf_eq_image`,
  `.skeletonHomeo_image_arcOf`, `.closure_cell_face_link`, `.closure_cell_face_link_homeo` —
  clause 1 of `def:matched-pair` ("the two distinguished outer cycles correspond") at the level
  of the two boundary arcs, and the correspondence of the two 2-cell labellings.
* `Schoenflies.InitialData.u_src_pos`, `.tgt_pos_corners`, `.u_a_mem_openTop`,
  `.u_b_mem_openBottom` — the geometric content of the `prop:initial-pair` sentence: `C` is
  subdivided at the `u`-preimages of the four corners, and `a, b` lie in two nonadjacent
  corner arcs.
* `Schoenflies.InitialData.source_cells_cover'`, `.source_cell_isComponent'`,
  `.source_closure_cell_inter'`, `.source_cells_ne'`, `.target_cells_cover'`,
  `.target_closure_cell_inter'`, `.target_cell_isComponent`, `.target_cells_ne` —
  `thm:general-crosscut` on both sides, with its hypotheses supplied.
* `Schoenflies.exists_initialData'`, `Schoenflies.initial_pair'` — `prop:initial-pair`, with the
  anchor clause and the matched labelling in the statement.
-/

open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

/-! ### Two missing `HexData` facts

The two boundary arcs are part of the outer cycle, and both are polygonal as soon as the six
outer edges are. The second is the clause of `def:admissible-graph` that the target realization
has to satisfy and the source one does not. -/

/-! ### `initBoundary` really is the boundary walk

`CellStructure.boundary` is documented as a raw datum: nothing in the record forces it to walk
anywhere. For `initialStructure` it does. Both lists are *closed* walks of `initSkel`, and the
cells they run through are exactly the `faceCells` that `initSub` declares to be subcells of the
corresponding 2-cell — so the base value of `≼_abs` is not an independent choice. -/

/-! ### The initial face-boundary cycles

The closed-walk facts above are strengthened here to the maintained data needed by
`thm:finite-transfer`: each boundary is a simple cycle of length at least three, and its cells
are exactly the strict subcells of the corresponding face. -/

/-! ### The anchor set `𝒜`

`prop:countable-strong-access` produces a countable dense set of strongly accessible points of
`C`; the blueprint then *fixes* it for the whole construction (tex 1418) and every later stage
draws its new boundary vertices from it. Fixing it means it is data, so it is a structure, and
`prop:initial-pair` takes it as an argument rather than producing its own. -/

variable {C : Set Plane}

/-- **`prop:countable-strong-access`, as the fixed set `𝒜`.** This uses the proved Jordan
curve theorem. -/
theorem nonempty_anchorSet (hC : IsJordanCurve C) : Nonempty (AnchorSet C) := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  -- `inside C` swallows the component in `Cᶜ` of each of its points, being a union of them
  have hDmax : ∀ q ∈ inside C, connectedComponentIn Cᶜ q ⊆ inside C := by
    intro q hq z hz
    refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
    rw [← connectedComponentIn_eq hz]
    exact hq.2
  have hCD : C ⊆ closure (inside C) := by
    intro x hx
    have hxf : x ∈ frontier (inside C) := by rw [hsep.frontier_inside]; exact hx
    exact hxf.1
  obtain ⟨A, hAC, hAcount, hAacc, hCA⟩ := exists_countable_dense_stronglyAccessible hC.isCompact
    hC.nonempty hsep.isOpen_inside inside_subset_compl hDmax hCD
  exact ⟨⟨A, hAC, hAcount, hAacc, hCA⟩⟩

open Classical in
/-- The fixed anchor set of a Jordan curve, as data. -/
noncomputable def anchorSet (hC : IsJordanCurve C) : AnchorSet C := (nonempty_anchorSet hC).some

/-! ### The initial matched pair, anchored

The clause of `prop:initial-pair` that `InitialData` drops. It is recorded as an extension
rather than as a side theorem so that a consumer holding an initial pair holds the anchoring
too; the integrator merging this file into `InitialPair.lean` should move the two fields into
`InitialData` itself. -/

/-- **`prop:initial-pair` including the anchor clause.** The two chosen points
are points of the *given* anchor set `𝒜`; the blueprint fixes `𝒜` once and reuses it at every
later stage, so it must be an input, not an output.

The proof is that of `Schoenflies.exists_initialData` with the anchor set supplied rather than
manufactured: the two open corner arcs are relatively open and nonempty in `C`, `𝒜` is dense in
`C`, so `𝒜` meets both; `lem:tangent-cone` (through `StronglyAccessible.polyAccessible`) and
`lem:accessible-endpoints` then supply the polygonal crosscut. -/
theorem exists_anchoredInitialData_of_homeo (hC : IsJordanCurve C) (A : AnchorSet C)
    (u w : Plane → Plane) (hhom : IsSetHomeoOn u w C modelCurve) :
    ∃ D : AnchoredInitialData C A,
      D.toInitialData.u = u ∧ D.toInitialData.w = w := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  -- the two open corner arcs, relatively open in `C` and nonempty
  obtain ⟨W₁, hW₁, hW₁eq⟩ := hhom.symm.image_isRelOpen isOpen_topBand (U := openTop) rfl
  obtain ⟨W₂, hW₂, hW₂eq⟩ := hhom.symm.image_isRelOpen isOpen_bottomBand (U := openBottom) rfl
  obtain ⟨a₀, ha₀A, ha₀⟩ := exists_mem_inter_of_dense A.subset_curve A.dense hW₁ hW₁eq
    (openTop_nonempty.image w)
  obtain ⟨b₀, hb₀A, hb₀⟩ := exists_mem_inter_of_dense A.subset_curve A.dense hW₂ hW₂eq
    (openBottom_nonempty.image w)
  obtain ⟨q₁, hq₁, rfl⟩ := ha₀
  obtain ⟨q₂, hq₂, rfl⟩ := hb₀
  have hq₁m : q₁ ∈ modelCurve := hq₁.2
  have hq₂m : q₂ ∈ modelCurve := hq₂.2
  obtain ⟨hq₁1, hq₁0⟩ := mem_openTop.1 hq₁
  obtain ⟨hq₂1, hq₂0⟩ := mem_openBottom.1 hq₂
  set xa : ℝ := q₁ 0 with hxa
  set xb : ℝ := q₂ 0 with hxb
  have hq₁eq : q₁ = tgtPos xa xb 1 := Plane.eq_mk rfl hq₁1
  have hq₂eq : q₂ = tgtPos xa xb 4 := Plane.eq_mk rfl hq₂1
  have haC : w q₁ ∈ C := hhom.mapsTo_inv hq₁m
  have hbC : w q₂ ∈ C := hhom.mapsTo_inv hq₂m
  have hab : w q₁ ≠ w q₂ := by
    intro h
    have hr := hhom.rightInvOn hq₁m
    rw [h, hhom.rightInvOn hq₂m] at hr
    rw [← hr] at hq₁1
    rw [hq₂1] at hq₁1
    norm_num at hq₁1
  -- the polygonal crosscut, from the two access cones
  obtain ⟨ws, -, -, -, hwsin, hwsarc, -⟩ := exists_crosscut_of_polyAccessible
    hsep.isOpen_inside hsep.isConnected_inside.isPreconnected
    (Set.disjoint_left.2 fun x hx => inside_subset_compl hx) hab haC hbC
    (A.polyAccessible ha₀A) (A.polyAccessible hb₀A)
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hwsarc
  refine ⟨{ toInitialData :=
              { u := u, w := w, homeo := hhom, curve := hC, xa := xa, xb := xb
                abs_xa := hq₁0, abs_xb := hq₂0
                cross := f
                continuousOn_cross := hfc, injOn_cross := hfi
                cross_zero := by rw [hf0, hq₁eq]
                cross_one := by rw [hf1, hq₂eq]
                cross_inside := ?_
                polygonal_cross := ?_ }
            a_mem_anchors := ?_
            b_mem_anchors := ?_ }, rfl, rfl⟩
  · rw [hfim, ← hq₁eq, ← hq₂eq]
    intro z hz
    exact hwsin ⟨hz.1, by simpa [hf0, hf1] using hz.2⟩
  · rw [hfim]
    exact ⟨ws, rfl⟩
  · change w (tgtPos xa xb 1) ∈ A.carrier
    rw [← hq₁eq]
    exact ha₀A
  · change w (tgtPos xa xb 4) ∈ A.carrier
    rw [← hq₂eq]
    exact hb₀A

/-! #### The canonical initial pair

`AnchorSet` is an input because the blueprint fixes `𝒜` once and every later stage draws from
the *same* set. A consumer that has no other constraint on `𝒜` can take `anchorSet hC`: it is a
function of `C` alone (`Nonempty (AnchorSet C)` is a `Prop`, so proof irrelevance makes the
choice independent of the proof supplied), so all its uses agree. -/

/-! ### The two crosscut theorems on the initial pair

`InitialPair.lean` carries `harc` (`thm:arc-complement`) and, on the source side, `hcollars`
(`lem:crosscut-collars`). Both are theorems on `main`: `Schoenflies.arc_complement` and
`Schoenflies.IsCrosscut.hasArcCollars`. Every consumer in Part II should use the primed forms
below and thread nothing. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.RefinementStars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.overlayGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Carriers, refinement compatibility, and the star lemmas

The interface between the *construction* of the nested cellulations and the *abstraction* the
limit homeomorphism uses. The blueprint says at the head of that section (tex, "The limit
homeomorphism of the interiors") that it "forgets how the decompositions were constructed and
uses only their nesting, matching, and shrinking properties"; everything below is therefore
stated for an abstract refinement relation `Realization.Refines` between two realizations of two
generated structures, and *not* for either elementary constructor. The two constructors enter
only at the very end, as the two theorems that produce a `Refines` from them.

## The carrier is a function

`Realization.carrier` is `car_Γ(x)` of the blueprint, exported as a total function `Plane → γ`
rather than as an existential: `σ_n(x)` is used on every line of the limit argument. Outside the
closed domain it is junk (whence the `[Nonempty γ]`), and every lemma about it carries the
hypothesis `x ∈ D` that makes it meaningful. Its characterising property is
`IsCellDecomposition.carrier_eq`: *any* cell whose open part contains `x` is the carrier.

## What `Refines` is, and why it is the right shape

`R'.Refines R par` says: `par` maps cells of the finer structure to cells of the coarser one and
2-cells to 2-cells, it is compatible with `≼_abs` (assertion (iv) of `lem:cellulation-invariants`),
and each *open* cell of the finer realization sits inside the open cell of its parent. The last
clause is the geometric content of the blueprint's proof of
`lem:refinement-compatibility`(a) — "a point in either new subedge or at the new vertex
had the old open edge as its old carrier" — and it implies the weaker
`closure (R'.cell σ) ⊆ closure (R.cell (par σ))` that part (b) needs.

`Refines` is a relation between two realizations of two *different* abstract structures over the
same name type `γ`, parametrised by the composite parent map. `Refines.trans` composes them, so
"a finite sequence of elementary refinements" needs no separate treatment: a consumer that builds
its stages one operation at a time gets the composite by iterating `trans`.

Part (c) of `lem:refinement-compatibility` — "corresponding cells have corresponding parents" —
is, under the representation of `CombinatorialInvariance.lean`, the statement that *one and the
same* `par : γ → γ` serves both realizations: cells are abstract names, and two `Refines`
instances sharing a `par` is exactly a compatible matched refinement. There is nothing to
transport, and the substance of (c) is its consequence, `Refines.carrier_congr`.

## Blueprint

* `Schoenflies.CellStructure.Realization.carrier` — `car_Γ(x)`, with
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.carrier_eq` its characterisation.
* `Schoenflies.CellStructure.Realization.Refines` — a refinement of one generated matched cell
  structure by another, with `Refines.trans` for a finite sequence of them.
* `lem:refinement-compatibility`:
  * (a) `Schoenflies.CellStructure.Realization.Refines.parent_carrier`;
  * (b) `Schoenflies.CellStructure.Realization.Refines.star_subset` (cells) and
    `Schoenflies.CellStructure.Realization.Refines.star_carrier_subset` (points);
  * (c) `Schoenflies.CellStructure.SkeletonHomeo.carrier_congr` (corresponding *skeleton points*
    have corresponding carriers, via
    `Schoenflies.CellStructure.SkeletonHomeo.image_cell`),
    `Schoenflies.CellStructure.Realization.Refines.carrier_congr` (and then at every earlier
    stage), and the form the limit argument actually cites,
    `Schoenflies.CellStructure.Realization.Refines.target_star_subset` (`T_{n+1}(x) ⊆ T_n(x)`).
* `lem:star-intersection` — `Schoenflies.CellStructure.Realization.star_inter_nonempty_congr`.
* `lem:star-face-mesh` — `Schoenflies.CellStructure.Realization.IsCellDecomposition.star_eq_faces`,
  with (a) `…diam_star_le`, `…diam_star_lt`, `…diam_star_carrier_lt` and (b)
  `Schoenflies.CellStructure.Realization.Refines.diam_cell_le`,
  `Schoenflies.CellStructure.Realization.Refines.diam_cell_le_of_forall`.
* `lem:cell-neighborhood` — `Schoenflies.CellStructure.Realization.cellNbhd` and
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.cell_neighborhood`.
* `rem:inductive-invariants` — honoured: nothing here is proved by a case check on the
  constructors. The inductive content lives in `GeneratedStructure.lean`; the two bridge theorems
  `Schoenflies.CellStructure.SubdivData.IsRefinement.refines` and
  `Schoenflies.CellStructure.SplitData.refines` are the only declarations that mention a
  constructor at all.

`Schoenflies.CellStructure.refines_of_elementary` is the shared bridge: both elementary
operations replace a single cell `c` by a set `N` of fresh cells and send `N` to `c`, so one
lemma serves both.
-/

open Set Metric Bornology
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

namespace Realization

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

/-! ### Elementary facts about the closed star

`Realization.star` is the `St` of the blueprint and is defined in `CombinatorialInvariance.lean`;
these are the membership and containment lemmas its consumers need. -/

/-! ### The carrier of a point

`car_Γ(x)`, the unique open cell containing `x`. It is a total function; off the closed domain
its value is junk, and every lemma below supplies `x ∈ D`. -/

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

theorem mem_cells_carrier [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    R.carrier x ∈ S.cells := (R.carrier_spec x (h.exists_cell hx)).1

theorem mem_cell_carrier [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    x ∈ R.cell (R.carrier x) := (R.carrier_spec x (h.exists_cell hx)).2

/-- **The characterising property of the carrier**: any cell whose open part contains `x` *is*
the carrier of `x`. This is the uniqueness half of assertion (i), and it is the lemma every
computation of a carrier goes through. -/
theorem carrier_eq [Nonempty γ] (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells)
    (hx : x ∈ R.cell σ) : R.carrier x = σ := by
  have hxD : x ∈ D := h.cell_subset_domain hσ hx
  by_contra hne
  exact Set.disjoint_left.1 (h.disjoint (h.mem_cells_carrier hxD) hσ hne)
    (h.mem_cell_carrier hxD) hx

/-- A point lies in the star of its own carrier. -/
theorem mem_star_carrier [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    x ∈ R.star (R.carrier x) :=
  closure_cell_subset_star (h.sub_refl (h.mem_cells_carrier hx))
    (_root_.subset_closure (h.mem_cell_carrier hx))

theorem star_nonempty (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) : (R.star σ).Nonempty := by
  obtain ⟨z, hz⟩ := h.nonempty hσ
  exact ⟨z, closure_cell_subset_star (h.sub_refl hσ) (_root_.subset_closure hz)⟩

/-- Stars are antitone in the subcell relation. The transitivity this needs is not assumed of a
`CellStructure`; it is read off assertion (i) by `IsCellDecomposition.sub_trans`. -/
theorem star_anti_of_sub (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hσ : σ ∈ S.cells) (hρ : ρ ∈ S.cells) (hsub : S.sub σ ρ) : R.star ρ ⊆ R.star σ := by
  intro y hy
  obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
  exact mem_star_iff.2 ⟨τ, h.sub_trans hσ hρ (hS.sub_mem_right hτ) hsub hτ, hyτ⟩

end IsCellDecomposition

/-! ### Refinement

The abstract relation "`R'` refines `R` with parent map `par`". It is deliberately not tied to
either elementary operation: the limit argument uses only these three clauses. -/

namespace Refines

variable {S' S'' : CellStructure γ} {R : S.Realization} {R' : S'.Realization}
  {R'' : S''.Realization} {par par' : γ → γ}

/-- **`lem:refinement-compatibility`(a)**: the parent of the carrier of `x` at the finer stage is
its carrier at the coarser stage. -/
theorem parent_carrier [Nonempty γ] (href : R'.Refines R par) (h : R.IsCellDecomposition D)
    (h' : R'.IsCellDecomposition D') {x : Plane} (hx : x ∈ D') :
    par (R'.carrier x) = R.carrier x :=
  (h.carrier_eq (href.parent_mem_cells (h'.mem_cells_carrier hx))
    (href.cell_subset (h'.mem_cells_carrier hx) (h'.mem_cell_carrier hx))).symm

/-- **`lem:refinement-compatibility`(b)**, pointwise: closed stars of a fixed point are monotone
under refinement. -/
theorem star_carrier_subset [Nonempty γ] (href : R'.Refines R par) (hS' : S'.CombInvariants)
    (h : R.IsCellDecomposition D) (h' : R'.IsCellDecomposition D') {x : Plane} (hx : x ∈ D') :
    R'.star (R'.carrier x) ⊆ R.star (R.carrier x) := by
  rw [← href.parent_carrier h h' hx]
  exact href.star_subset hS'

end Refines

/-! ### Matched refinements: part (c)

Two realizations of one abstract structure are matched; a *compatible matched refinement* is a
pair of `Refines` instances sharing one parent map. That sharing **is** the blueprint's
"corresponding cells have corresponding parents": the parent map is a map of abstract names, so
there is only ever one of it. The substance is the consequence recorded here. -/

namespace Refines

variable {S' : CellStructure γ} {R₁ R₂ : S.Realization} {R₁' R₂' : S'.Realization} {par : γ → γ}
  {D₁ D₂ D₁' D₂' : Set Plane}

/-- **The nesting the limit map runs on.** With `R₁` the source realization and `R₂` the target
one, `T_n(x) = R₂.star (R₁.carrier x)` is the closed target star of the cell corresponding to
`σ_n(x)`, and this says `T_{n+1}(x) ⊆ T_n(x)`.

Only the *source* decompositions are needed: the parent map is abstract, so the target stage
inherits the inclusion from the source carrier. -/
theorem target_star_subset [Nonempty γ] (h₁ : R₁'.Refines R₁ par) (h₂ : R₂'.Refines R₂ par)
    (hS' : S'.CombInvariants) (hd₁ : R₁.IsCellDecomposition D₁)
    (hd₁' : R₁'.IsCellDecomposition D₁') {x : Plane} (hx : x ∈ D₁') :
    R₂'.star (R₁'.carrier x) ⊆ R₂.star (R₁.carrier x) := by
  rw [← h₁.parent_carrier hd₁ hd₁' hx]
  exact h₂.star_subset hS'

end Refines

/-! ### Intersection of corresponding stars -/

/-- One direction of `lem:star-intersection`. The two realizations are realizations of the *same*
abstract structure, so "the corresponding cells" are literally `σ` and `τ` again. -/
theorem star_inter_nonempty_of_star_inter_nonempty {R₁ R₂ : S.Realization} {D₁ D₂ : Set Plane}
    (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂) (hS : S.CombInvariants)
    {σ τ : γ} (hne : (R₁.star σ ∩ R₁.star τ).Nonempty) : (R₂.star σ ∩ R₂.star τ).Nonempty := by
  obtain ⟨p, hpσ, hpτ⟩ := hne
  obtain ⟨α, hσα, hpα⟩ := mem_star_iff.1 hpσ
  obtain ⟨β, hτβ, hpβ⟩ := mem_star_iff.1 hpτ
  have hα : α ∈ S.cells := hS.sub_mem_right hσα
  have hβ : β ∈ S.cells := hS.sub_mem_right hτβ
  -- the carrier `ρ` of `p` in the first realization is a subcell of both `α` and `β`
  rw [h₁.closure_eq hα] at hpα
  obtain ⟨ρ, ⟨hρ, hρα⟩, hpρ⟩ := Set.mem_iUnion₂.1 hpα
  have hρβ : S.sub ρ β := h₁.sub_of_mem hρ hβ hpρ hpβ
  -- both relations are relations of the common abstract structure, so they hold on the other side
  obtain ⟨w, hw⟩ := h₂.nonempty hρ
  exact ⟨w, closure_cell_subset_star hσα (h₂.subset_closure hρ hα hρα hw),
    closure_cell_subset_star hτβ (h₂.subset_closure hρ hβ hρβ hw)⟩

/-- **`lem:star-intersection`**: corresponding stars meet on one side exactly when they meet on
the other. This is what makes the limit map injective. -/
theorem star_inter_nonempty_congr {R₁ R₂ : S.Realization} {D₁ D₂ : Set Plane}
    (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂) (hS : S.CombInvariants)
    {σ τ : γ} : (R₁.star σ ∩ R₁.star τ).Nonempty ↔ (R₂.star σ ∩ R₂.star τ).Nonempty :=
  ⟨star_inter_nonempty_of_star_inter_nonempty h₁ h₂ hS,
    star_inter_nonempty_of_star_inter_nonempty h₂ h₁ hS⟩

/-! ### Stars and the face mesh -/

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ : γ} {x y : Plane} {η : ℝ}

/-- **`lem:star-face-mesh`**, the displayed equality: a closed star is the union of the closed
2-cells incident with the cell. Every supercell is a subcell of some 2-cell by assertion (v), and
its closure is then inside that closed 2-cell. -/
theorem star_eq_faces (h : R.IsCellDecomposition D) (hS : S.CombInvariants) (hσ : σ ∈ S.cells) :
    R.star σ = ⋃ F ∈ {F | F ∈ S.faces ∧ S.sub σ F}, closure (R.cell F) := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
    have hτc : τ ∈ S.cells := hS.sub_mem_right hτ
    obtain ⟨F, hF, hτF⟩ := hS.mem_face hτc
    have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
    refine Set.mem_iUnion₂.2 ⟨F, ⟨hF, h.sub_trans hσ hτc hFc hτ hτF⟩, ?_⟩
    exact closure_minimal (h.subset_closure hτc hFc hτF) isClosed_closure hyτ
  · exact Set.iUnion₂_subset fun _ hF => closure_cell_subset_star hF.2

/-- Every point of the star of `σ` is within `η` of every point of the open cell `σ`, when the
closed 2-cells incident with `σ` all have diameter at most `η`. -/
theorem dist_le_of_mem_star (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) (hσ : σ ∈ S.cells)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub σ F → diam (closure (R.cell F)) ≤ η)
    (hx : x ∈ R.cell σ) (hy : y ∈ R.star σ) : dist x y ≤ η := by
  rw [h.star_eq_faces hS hσ] at hy
  obtain ⟨F, ⟨hF, hsub⟩, hyF⟩ := Set.mem_iUnion₂.1 hy
  have hbdd : IsBounded (closure (R.cell F)) :=
    (hD.subset (h.cell_subset_domain (S.mem_cells_of_mem_faces hF))).closure
  exact le_trans (dist_le_diam_of_mem hbdd (h.mem_closure_face hσ hF hsub hx) hyF) (hdiam hF hsub)

/-- **`lem:star-face-mesh`(a)**, in its non-strict form: a mesh bound on the closed 2-cells
incident with a cell doubles to a bound on the diameter of its star. -/
theorem diam_star_le (h : R.IsCellDecomposition D) (hS : S.CombInvariants) (hD : IsBounded D)
    (hσ : σ ∈ S.cells)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub σ F → diam (closure (R.cell F)) ≤ η) :
    diam (R.star σ) ≤ 2 * η := by
  obtain ⟨x, hx⟩ := h.nonempty hσ
  obtain ⟨F, hF, hσF⟩ := hS.mem_face hσ
  have hη : 0 ≤ η := le_trans diam_nonneg (hdiam hF hσF)
  refine diam_le_of_forall_dist_le (by linarith) fun y hy z hz => ?_
  have hxy : dist x y ≤ η := h.dist_le_of_mem_star hS hD hσ hdiam hx hy
  have hxz : dist x z ≤ η := h.dist_le_of_mem_star hS hD hσ hdiam hx hz
  calc dist y z ≤ dist y x + dist x z := dist_triangle y x z
    _ = dist x y + dist x z := by rw [dist_comm y x]
    _ ≤ 2 * η := by linarith

/-- **`lem:star-face-mesh`(a)**: if every closed 2-cell incident with `σ` has diameter *strictly*
less than `η`, the star has diameter strictly less than `2η`.

Strictness costs the finiteness of the set of incident 2-cells: the bound is realised at the
largest of them, and there are finitely many. -/
theorem diam_star_lt (h : R.IsCellDecomposition D) (hS : S.CombInvariants) (hD : IsBounded D)
    (hσ : σ ∈ S.cells)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub σ F → diam (closure (R.cell F)) < η) :
    diam (R.star σ) < 2 * η := by
  classical
  have hfin : {F | F ∈ S.faces ∧ S.sub σ F}.Finite := S.finite_faces.subset fun _ hF => hF.1
  have hne : {F | F ∈ S.faces ∧ S.sub σ F}.Nonempty := by
    obtain ⟨F, hF, hσF⟩ := hS.mem_face hσ
    exact ⟨F, hF, hσF⟩
  obtain ⟨F₀, hF₀, hmax⟩ := Finset.exists_max_image hfin.toFinset
    (fun F => diam (closure (R.cell F))) (hfin.toFinset_nonempty.2 hne)
  rw [Set.Finite.mem_toFinset] at hF₀
  have hle : diam (R.star σ) ≤ 2 * diam (closure (R.cell F₀)) :=
    h.diam_star_le hS hD hσ fun F hF hsub =>
      hmax F (Set.Finite.mem_toFinset hfin |>.2 ⟨hF, hsub⟩)
  exact lt_of_le_of_lt hle (by have := hdiam hF₀.1 hF₀.2; linarith)

end IsCellDecomposition

/-! ### Finite cell neighborhoods -/

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {x z : Plane}

/-- **`lem:cell-neighborhood`**, the carrier half: for `z` in the neighbourhood, the carrier of
`x` is a subcell of the carrier of `z`. -/
theorem sub_carrier_of_mem_cellNbhd [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D)
    (hz : z ∈ R.cellNbhd x) (hzD : z ∈ D) : S.sub (R.carrier x) (R.carrier z) := by
  have hxclos : x ∈ closure (R.cell (R.carrier z)) :=
    mem_closure_of_mem_cellNbhd (h.mem_cells_carrier hzD) hz
      (_root_.subset_closure (h.mem_cell_carrier hzD))
  exact h.sub_of_mem (h.mem_cells_carrier hx) (h.mem_cells_carrier hzD)
    (h.mem_cell_carrier hx) hxclos

end IsCellDecomposition

/-! ### Corresponding skeleton points

The second sentence of `lem:refinement-compatibility`(c). A point of the realized skeleton lies
in an open 0-cell or an open 1-cell, and the skeleton homeomorphism carries each of those onto
the open cell of the *same abstract name*; so corresponding skeleton points have carriers that
correspond, with nothing to transport. -/

end Realization

/-! ### The two elementary operations produce refinements

Both operations have the same shape: a single cell `c` is replaced by a set `N` of fresh cells,
and the parent map sends `N` to `c` and fixes everything else. `refines_of_elementary` proves the
geometric clause of `Refines` from that shape alone — the fresh cells must land inside `c`,
because any other cell of the old stage survives and is unmoved, and open cells of one stage are
disjoint. -/

/-! ### The interface, exercised

The limit homeomorphism opens with: "the sets `T_n(x)` are nonempty and compact … the cell-star
inclusion gives `T_{n+1}(x) ⊆ T_n(x)` … their diameters tend to zero … by
`lem:nested-compact` their intersection is one point". This anonymous example is a machine-checked
statement that the four facts that sentence needs come out of this module for an *abstract*
nested sequence: nothing below mentions how the stages were built, and the mesh hypothesis is
read in the target realization while the carrier is read in the source one. -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.LimitMap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The limit homeomorphism of the interiors

The blueprint opens this section with a sentence that is an instruction to the formalizer: "We
now forget how the decompositions were constructed and use only their nesting, matching, and
shrinking properties." This module takes it literally. `LimitTower` is a structure recording
exactly those properties — a sequence of matched cell structures with two realizations each, a
`Realization.Refines` instance between consecutive stages on each side sharing one parent map,
nested skeleton homeomorphisms, and the two shrinking hypotheses of `prop:shrinking-stars` — and
everything from the definition of `F` to `prop:interior-homeomorphism` is proved against it.
Nothing below mentions a mesh, a grid, or a constructor. The still-open construction has to
produce one `LimitTower`; none of the analysis waits for it.

## What is *not* a field

Three things the task list expected to appear as hypotheses turned out to be derivable and are
therefore proved here rather than assumed.

* **`lem:outer-incidence`.** `docs/ROADMAP.md` records it as done in `CombinatorialInvariance.lean`
  under `outerEdge_face_corresponds`; that is a different statement (assertion (vi) of
  `lem:cellulation-invariants`, transported). The real `lem:outer-incidence` — `closure σ` meets
  `C` iff some outer cell is a subcell of `σ` iff `closure σ'` meets `S` — is proved below as
  `Realization.IsCellDecomposition.closure_cell_meets_outer_iff` and, for stars,
  `LimitTower.star_meets_bdry_iff`. The one geometric input it needs is
  `Realization.outerSet_eq_iUnion_cell`: the realized outer cycle is exactly the union of the
  open cells of the outer cells, which is a consequence of the two `Realization` clauses
  `cell_vertex` and `cell_edge` and holds for any subcomplex.
* **Assertion (vii) of `lem:cellulation-invariants`** (every 2-cell boundary a Jordan curve with
  the open cell its bounded region). The limit argument was expected to need it, through
  assertion (viii). It does not: the only use is "a 2-cell is not a proper subcell of a 2-cell",
  and that is `CombInvariants.face_maximal`, which is already an inductive invariant on `main`.
  There is therefore no field for (vii) and no dependency on it.
* **`prop:target-skeleton-dense`.** The blueprint's surjectivity proof goes through the density
  of the target skeleton and a compactness argument in `C ∪ D`. That is not needed: the sets
  `⋂ₙ St_{Γₙ}(car_{Γ'ₙ}(y))` — the *source* stars of the *target* carriers of `y` — are a nested
  sequence of nonempty compacts, and any point of their intersection is already a preimage of
  `y`. `prop:target-skeleton-dense` is proved anyway, because the boundary-continuity module
  cites it, but it is not on the critical path to `prop:F-surjective`.

## The two shrinking hypotheses are not symmetric

`prop:shrinking-stars` gives *pointwise* convergence of the source star diameters and *uniform*
convergence of the target ones. The asymmetry is real and is used: `F` is defined, and continuous,
on the whole closed domain (only the uniform bound enters), whereas injectivity and the continuity
of the inverse hold on the open region (they need the pointwise bound at a point of `D`).

One hypothesis that the blueprint does not state is carried throughout: the closed domains are
bounded. It is not optional — `Metric.diam` is `0` on an unbounded set, so without it the star
diameter bounds are false rather than weak — and it is trivially true for a closed Jordan domain.

## Blueprint

All of the following live in `Schoenflies.CellStructure`.

* `LimitTower` — the abstraction of the head of the section: "we now forget how the
  decompositions were constructed and use only their nesting, matching, and shrinking
  properties".
* The definition of `F` (tex "The limit homeomorphism of the interiors") —
  `LimitTower.F`, with `LimitTower.iInter_tgtStar_eq` its characterisation
  (`lem:nested-compact` applied to the nested stars `LimitTower.tgtStar`),
  `LimitTower.F_mem_tgtStar` and `LimitTower.eq_F_of_mem_iInter`.
* `lem:outer-incidence` — `Realization.IsCellDecomposition.closure_cell_meets_outer_iff` and
  `Realization.IsCellDecomposition.star_meets_outer_iff`, with the matched form the limit
  argument cites, `LimitTower.star_meets_bdry_iff`. Their geometric input is
  `Realization.outerSet_eq_iUnion_cell`.
* `prop:skeleton-agreement` — `LimitTower.F_eq_skelHomeo`.
* `prop:F-continuous` — `LimitTower.continuousOn_F`, on the *closed* domain.
* `prop:image-interior` — `LimitTower.F_mem_region'`.
* `prop:F-injective` — `LimitTower.injOn_F`.
* `prop:target-skeleton-dense` — `LimitTower.exists_mem_tgt_skeletonSet`.
* `prop:F-surjective` — `LimitTower.exists_mem_region_F_eq`, through `LimitTower.preStar` and
  `LimitTower.F_eq_of_mem_iInter_preStar`.
* `lem:exact-cell-correspondence` — `LimitTower.image_cell`, with the corollary the inverse
  argument actually uses, `LimitTower.tgt_carrier_F`.
* `prop:inverse-continuous` — `LimitTower.continuousOn_inv`, on the explicit inverse
  `LimitTower.inv`.
* `prop:interior-homeomorphism` — `LimitTower.isHomeoOn_F` and, with the skeleton clause,
  `LimitTower.interior_homeomorphism`; in the `Schoenflies.IsHomeoOn` shape that `Endgame.lean`
  and the boundary-continuity module consume.
* `lem:cell-neighborhood` is used, not restated: it is
  `Realization.IsCellDecomposition.sub_carrier_of_mem_cellNbhd` in `RefinementStars.lean`, and
  the cross-realization form the limit map needs is
  `LimitTower.tgtStar_subset_of_mem_cellNbhd`.
-/

open Set Metric Bornology Filter
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-! ### The realized skeleton and outer cycle, cell by cell

`Realization.skeletonSet` and `Realization.outerSet` are defined as point sets of drawn graphs.
The limit argument needs them as unions of *open cells*, because that is the form in which they
interact with `IsCellDecomposition`: "the carrier of any point of `C` is an outer cell" is the
first sentence of the blueprint's proof of `lem:outer-incidence`, and it is exactly this
rewriting. -/

namespace Realization

variable (R : S.Realization)

variable {R}

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ : γ} {x : Plane}

/-- **The closed star of a 2-cell is its own closed cell.** By `lem:star-face-mesh` a closed star
is the union of the closed 2-cells above the cell, and `CombInvariants.face_maximal` says the
only 2-cell above a 2-cell is itself. This is the step the blueprint attributes to assertion
(viii) of `lem:cellulation-invariants`, and it needs neither (vii) nor openness of the open
2-cell. -/
theorem star_face_eq_closure (h : R.IsCellDecomposition D) (hS : S.CombInvariants) {F : γ}
    (hF : F ∈ S.faces) : R.star F = closure (R.cell F) := by
  rw [h.star_eq_faces hS (S.mem_cells_of_mem_faces hF)]
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun T hT => ?_)
    (Set.subset_biUnion_of_mem (u := fun T => closure (R.cell T))
      (show F ∈ {T | T ∈ S.faces ∧ S.sub F T} from
        ⟨hF, h.sub_refl (S.mem_cells_of_mem_faces hF)⟩))
  exact (congrArg (fun c => closure (R.cell c)) (hS.face_maximal hF hT.2)).le

/-- **`lem:outer-incidence`**, the closed-cell form: a closed cell meets the realized outer cycle
exactly when some outer cell is one of its subcells. The middle condition is a statement of the
abstract structure alone, which is what makes the equivalence transfer between the two
realizations with nothing to transport. -/
theorem closure_cell_meets_outer_iff (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    (closure (R.cell τ) ∩ R.outerSet).Nonempty ↔ ∃ κ ∈ S.outerCells, S.sub κ τ := by
  constructor
  · rintro ⟨p, hpτ, hpout⟩
    rw [R.outerSet_eq_iUnion_cell] at hpout
    obtain ⟨κ, hκ, hpκ⟩ := Set.mem_iUnion₂.1 hpout
    exact ⟨κ, hκ, h.sub_of_mem (outerCells_subset_cells hκ) hτ hpκ hpτ⟩
  · rintro ⟨κ, hκ, hsub⟩
    obtain ⟨z, hz⟩ := h.nonempty (outerCells_subset_cells hκ)
    exact ⟨z, h.subset_closure (outerCells_subset_cells hκ) hτ hsub hz, cell_subset_outerSet hκ hz⟩

/-- **`lem:outer-incidence`**, the star form: a closed star meets the realized outer cycle
exactly when some supercell of the cell has an outer subcell. -/
theorem star_meets_outer_iff (h : R.IsCellDecomposition D)
    (hS : S.CombInvariants) (σ : γ) :
    (R.star σ ∩ R.outerSet).Nonempty ↔ ∃ τ, S.sub σ τ ∧ ∃ κ ∈ S.outerCells, S.sub κ τ := by
  constructor
  · rintro ⟨p, hpstar, hpout⟩
    obtain ⟨τ, hτ, hpτ⟩ := mem_star_iff.1 hpstar
    exact ⟨τ, hτ, (h.closure_cell_meets_outer_iff (hS.sub_mem_right hτ)).1 ⟨p, hpτ, hpout⟩⟩
  · rintro ⟨τ, hτ, hex⟩
    obtain ⟨p, hpτ, hpout⟩ := (h.closure_cell_meets_outer_iff (hS.sub_mem_right hτ)).2 hex
    exact ⟨p, closure_cell_subset_star hτ hpτ, hpout⟩

end IsCellDecomposition

end Realization

/-! ### The tower of matched cellulations

Every field below is an obligation on whoever eventually constructs the sequence of
decompositions, and there is nothing here that the limit argument does not use. -/

namespace LimitTower

variable [Nonempty γ] (L : LimitTower γ) {x y z : Plane} {m n : ℕ} {σ : γ}

variable {L}

/-! #### Stars of the tower -/

theorem mem_srcStar_self (hx : x ∈ L.dom) (n : ℕ) : x ∈ L.srcStar n x :=
  (L.srcDecomp n).mem_star_carrier hx

/-- **`lem:refinement-compatibility`(b)** at a point: `T_{n+1}(x) ⊆ T_n(x)`. -/
theorem tgtStar_succ_subset (hx : x ∈ L.dom) (n : ℕ) : L.tgtStar (n + 1) x ⊆ L.tgtStar n x :=
  (L.srcRefines n).target_star_subset (L.tgtRefines n) (L.comb (n + 1)) (L.srcDecomp n)
    (L.srcDecomp (n + 1)) hx

theorem tgtStar_antitone (hx : x ∈ L.dom) : Antitone (fun n => L.tgtStar n x) :=
  antitone_nat_of_succ_le (L.tgtStar_succ_subset hx)

theorem tgtStar_nonempty (hx : x ∈ L.dom) (n : ℕ) : (L.tgtStar n x).Nonempty :=
  (L.tgtDecomp n).star_nonempty ((L.srcDecomp n).mem_cells_carrier hx)

theorem diam_tgtStar (hx : x ∈ L.dom) (n : ℕ) : diam (L.tgtStar n x) ≤ L.eps n :=
  L.diam_tgtStar_le n ((L.srcDecomp n).mem_cells_carrier hx)

theorem tendsto_diam_tgtStar (hx : x ∈ L.dom) :
    Tendsto (fun n => diam (L.tgtStar n x)) atTop (nhds 0) :=
  squeeze_zero (fun _ => diam_nonneg) (L.diam_tgtStar hx) L.tendsto_eps

/-! #### The limit map -/

theorem exists_eq_singleton_iInter_tgtStar (hx : x ∈ L.dom) :
    ∃ p, ⋂ n, L.tgtStar n x = {p} :=
  Plane.eq_singleton_iInter_of_diam_tendsto_zero (L.tgtStar_nonempty hx)
    (fun n => L.isCompact_tgtStar n x) (L.tgtStar_antitone hx) (L.tendsto_diam_tgtStar hx)

/-- **The characterising property of `F`.** -/
theorem iInter_tgtStar_eq (hx : x ∈ L.dom) : ⋂ n, L.tgtStar n x = {L.F x} := by
  rw [F, dif_pos (L.exists_eq_singleton_iInter_tgtStar hx)]
  exact (L.exists_eq_singleton_iInter_tgtStar hx).choose_spec

theorem F_mem_iInter (hx : x ∈ L.dom) : L.F x ∈ ⋂ n, L.tgtStar n x := by
  rw [L.iInter_tgtStar_eq hx]
  exact rfl

theorem F_mem_tgtStar (hx : x ∈ L.dom) (n : ℕ) : L.F x ∈ L.tgtStar n x :=
  Set.mem_iInter.1 (L.F_mem_iInter hx) n

/-- Uniqueness: anything in every `T_n(x)` is `F x`. -/
theorem eq_F_of_mem_iInter (hx : x ∈ L.dom) (hz : ∀ n, z ∈ L.tgtStar n x) : z = L.F x := by
  have : z ∈ ⋂ n, L.tgtStar n x := Set.mem_iInter.2 hz
  rwa [L.iInter_tgtStar_eq hx, Set.mem_singleton_iff] at this

theorem F_mem_dom' (hx : x ∈ L.dom) : L.F x ∈ L.dom' :=
  tgtStar_subset_dom' 0 _ (L.F_mem_tgtStar hx 0)

/-- `F x` is within `eps n` of anything in the stage-`n` target star of `x`. -/
theorem dist_F_le_of_mem_tgtStar (hx : x ∈ L.dom) (hz : z ∈ L.tgtStar n x) :
    dist (L.F x) z ≤ L.eps n :=
  le_trans (dist_le_diam_of_mem (isBounded_tgt_star n _) (L.F_mem_tgtStar hx n) hz)
    (L.diam_tgtStar hx n)

/-! #### Agreement with the finite skeleton maps

The skeleton maps are nested, so `g_n = g_N` on `G_N` for every `n ≥ N`; at each such stage the
skeleton map carries the carrier of `x` onto the corresponding target cell, which sits inside
`T_n(x)`. The intersection of the `T_n(x)` is the single point `F x`. -/

/-- At a stage-`n` skeleton point the skeleton map lands in the stage-`n` target star: the
carrier of `x` is a 0- or 1-cell, and `g_n` carries its open cell onto the target open cell of
the same abstract name. -/
theorem skelHomeo_mem_tgtStar (hx : x ∈ (L.src n).skeletonSet) :
    (L.skelHomeo n).toFun x ∈ L.tgtStar n x := by
  rw [(L.src n).skeletonSet_eq_iUnion_cell] at hx
  obtain ⟨κ, hκ, hxκ⟩ := Set.mem_iUnion₂.1 hx
  have hcells : κ ∈ (L.str n).cells := by
    rcases hκ with hv | he
    exacts [(L.str n).mem_cells_of_mem_vertexSet hv, (L.str n).mem_cells_of_mem_edgeSet he]
  have hgx : (L.skelHomeo n).toFun x ∈ (L.tgt n).cell κ := by
    rw [← (L.skelHomeo n).image_cell hκ]
    exact Set.mem_image_of_mem _ hxκ
  rw [tgtStar_eq, (L.srcDecomp n).carrier_eq hcells hxκ]
  exact Realization.closure_cell_subset_star ((L.tgtDecomp n).sub_refl hcells)
    (_root_.subset_closure hgx)

/-- **`prop:skeleton-agreement`**: `F` agrees with the stage-`N` skeleton map on `G_N ∩ (C ∪ D)`.
Since the skeleton maps are nested, this is the blueprint's `F = g_∞` on `⋃ₙ Gₙ ∩ D` as well. -/
theorem F_eq_skelHomeo (hx : x ∈ (L.src n).skeletonSet) (hxD : x ∈ L.dom) :
    L.F x = (L.skelHomeo n).toFun x := by
  refine (eq_F_of_mem_iInter hxD fun m => ?_).symm
  rcases le_or_gt n m with hnm | hmn
  · rw [← skelHomeo_eqOn hnm hx]
    exact skelHomeo_mem_tgtStar (skeletonSet_mono_le hnm hx)
  · exact tgtStar_antitone hxD hmn.le (skelHomeo_mem_tgtStar hx)

/-! #### Continuity -/

/-- The cross-realization form of `lem:cell-neighborhood` the limit map needs: for `z` in the
stage-`n` source cell neighbourhood of `x`, `T_n(z) ⊆ T_n(x)`. The subcell relation is read in
the source realization and used in the target one; it is a relation of the common abstract
structure, so nothing is transported. -/
theorem tgtStar_subset_of_mem_cellNbhd (hx : x ∈ L.dom) (hzD : z ∈ L.dom)
    (hz : z ∈ (L.src n).cellNbhd x) : L.tgtStar n z ⊆ L.tgtStar n x :=
  (L.tgtDecomp n).star_anti_of_sub (L.comb n) ((L.srcDecomp n).mem_cells_carrier hx)
    ((L.srcDecomp n).mem_cells_carrier hzD)
    ((L.srcDecomp n).sub_carrier_of_mem_cellNbhd hx hz hzD)

/-- **`prop:F-continuous`**, on the whole *closed* domain. Only the uniform half of
`prop:shrinking-stars` enters, so nothing here restricts `x` to the open region. -/
theorem continuousOn_F (L : LimitTower γ) : ContinuousOn L.F L.dom := by
  rw [Metric.continuousOn_iff]
  intro x hx η hη
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero L.tendsto_eps hη
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.1 ((L.src n).isOpen_cellNbhd x) x ((L.src n).mem_cellNbhd_self x)
  refine ⟨δ, hδ, fun a ha hadist => ?_⟩
  rw [dist_comm]
  exact lt_of_le_of_lt (dist_F_le_of_mem_tgtStar hx
    (tgtStar_subset_of_mem_cellNbhd hx ha (hball (Metric.mem_ball.2 hadist))
      (L.F_mem_tgtStar ha n))) hn

/-! #### The image lies in the interior -/

/-- **`lem:outer-incidence`, matched form**: a stage-`n` source star meets `C` exactly when the
target star of the *same abstract cell* meets `S`. Both sides reduce to the middle condition of
the blueprint's statement, which mentions only the abstract structure and its outer cycle. -/
theorem star_meets_bdry_iff (L : LimitTower γ) (n : ℕ) (σ : γ) :
    ((L.src n).star σ ∩ L.bdry).Nonempty ↔ ((L.tgt n).star σ ∩ L.bdry').Nonempty := by
  rw [← L.srcOuterSet n, ← L.tgtOuterSet n, (L.srcDecomp n).star_meets_outer_iff (L.comb n) σ,
    (L.tgtDecomp n).star_meets_outer_iff (L.comb n) σ]

/-- At a point of the open region the source star is eventually contained in the region: the
point lies in its own star, and the star diameters tend to zero. -/
theorem exists_srcStar_subset_region (hx : x ∈ L.region) : ∃ n, L.srcStar n x ⊆ L.region := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 L.isOpen_region x hx
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero (L.tendsto_diam_srcStar hx) hr
  refine ⟨n, fun w hw => hball (Metric.mem_ball.2 (lt_of_le_of_lt ?_ hn))⟩
  exact dist_le_diam_of_mem (isBounded_srcStar n x) hw
    (mem_srcStar_self (region_subset_dom hx) n)

/-- **`prop:image-interior`**: `F(D) ⊆ Q°`. -/
theorem F_mem_region' (hx : x ∈ L.region) : L.F x ∈ L.region' := by
  obtain ⟨n, hn⟩ := exists_srcStar_subset_region hx
  refine ⟨F_mem_dom' (region_subset_dom hx), fun hcon => ?_⟩
  obtain ⟨w, hw, hwb⟩ := (L.star_meets_bdry_iff n ((L.src n).carrier x)).2
    ⟨L.F x, L.F_mem_tgtStar (region_subset_dom hx) n, hcon⟩
  exact (hn hw).2 hwb

/-! #### Injectivity -/

/-- **`prop:F-injective`**. This is where the pointwise half of `prop:shrinking-stars` is needed,
and it is why injectivity is asserted on the open region rather than on the closed domain. -/
theorem injOn_F (L : LimitTower γ) : Set.InjOn L.F L.region := by
  intro x hx y hy hxy
  -- the target stars meet at every stage, so `lem:star-intersection` makes the source stars meet
  have hmeet : ∀ n, (L.srcStar n x ∩ L.srcStar n y).Nonempty := fun n =>
    (Realization.star_inter_nonempty_congr (L.tgtDecomp n) (L.srcDecomp n) (L.comb n)).1
      ⟨L.F x, L.F_mem_tgtStar (region_subset_dom hx) n,
        hxy ▸ L.F_mem_tgtStar (region_subset_dom hy) n⟩
  have hbound : ∀ n, dist x y ≤ diam (L.srcStar n x) + diam (L.srcStar n y) := by
    intro n
    obtain ⟨w, hwx, hwy⟩ := hmeet n
    refine le_trans (dist_triangle x w y) (add_le_add ?_ ?_)
    · exact dist_le_diam_of_mem (isBounded_srcStar n x)
        (mem_srcStar_self (region_subset_dom hx) n) hwx
    · exact dist_le_diam_of_mem (isBounded_srcStar n y) hwy
        (mem_srcStar_self (region_subset_dom hy) n)
  have hzero : dist x y ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds
      (by simpa using (tendsto_diam_srcStar_point hx).add (tendsto_diam_srcStar_point hy)) hbound
  exact dist_le_zero.1 hzero

/-! #### Density of the target skeleton -/

/-! #### Surjectivity

The blueprint reaches `y` through the density of the target skeleton and a compactness argument
in `C ∪ D`. The route taken here is shorter and needs neither: the *source* stars of the
*target* carriers of `y` are themselves a nested sequence of nonempty compacts, and every point
of their intersection is already a preimage of `y`. -/

theorem preStar_succ_subset (hy : y ∈ L.dom') (n : ℕ) :
    L.preStar (n + 1) y ⊆ L.preStar n y :=
  (L.tgtRefines n).target_star_subset (L.srcRefines n) (L.comb (n + 1)) (L.tgtDecomp n)
    (L.tgtDecomp (n + 1)) hy

theorem preStar_nonempty (hy : y ∈ L.dom') (n : ℕ) : (L.preStar n y).Nonempty :=
  (L.srcDecomp n).star_nonempty ((L.tgtDecomp n).mem_cells_carrier hy)

theorem nonempty_iInter_preStar (hy : y ∈ L.dom') : (⋂ n, L.preStar n y).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (fun n => preStar_succ_subset hy n) (preStar_nonempty hy) (isCompact_preStar 0 y)
    fun n => (isCompact_preStar n y).isClosed

/-- **The heart of surjectivity**: a point lying in every `preStar n y` is carried to `y`. At
each stage the source carrier of `x` and the target carrier of `y` share a supercell `τ`, so the
two target stars meet, and both have diameter at most `eps n`. -/
theorem F_eq_of_mem_iInter_preStar (hy : y ∈ L.dom') (hxD : x ∈ L.dom)
    (hx : ∀ n, x ∈ L.preStar n y) : L.F x = y := by
  have hbound : ∀ n, dist (L.F x) y ≤ 2 * L.eps n := by
    intro n
    obtain ⟨τ, hτ, hxτ⟩ := Realization.mem_star_iff.1 (hx n)
    have hτc : τ ∈ (L.str n).cells := (L.comb n).sub_mem_right hτ
    -- `τ` is a supercell of the source carrier of `x` as well
    have hsub : (L.str n).sub ((L.src n).carrier x) τ :=
      (L.srcDecomp n).sub_of_mem ((L.srcDecomp n).mem_cells_carrier hxD) hτc
        ((L.srcDecomp n).mem_cell_carrier hxD) hxτ
    obtain ⟨w, hw⟩ := (L.tgtDecomp n).nonempty hτc
    have hwx : w ∈ L.tgtStar n x :=
      Realization.closure_cell_subset_star hsub (_root_.subset_closure hw)
    have hwy : w ∈ (L.tgt n).star ((L.tgt n).carrier y) :=
      Realization.closure_cell_subset_star hτ (_root_.subset_closure hw)
    have h₁ : dist (L.F x) w ≤ L.eps n := dist_F_le_of_mem_tgtStar hxD hwx
    have h₂ : dist w y ≤ L.eps n :=
      le_trans (dist_le_diam_of_mem (isBounded_tgt_star n _) hwy
        ((L.tgtDecomp n).mem_star_carrier hy))
        (L.diam_tgtStar_le n ((L.tgtDecomp n).mem_cells_carrier hy))
    calc dist (L.F x) y ≤ dist (L.F x) w + dist w y := dist_triangle _ _ _
      _ ≤ 2 * L.eps n := by linarith
  have hzero : dist (L.F x) y ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds
      (by simpa using L.tendsto_eps.const_mul 2) hbound
  exact dist_le_zero.1 hzero

/-- At a point of `Q°` the target star is eventually inside `Q°`. Here the *uniform* half of
`prop:shrinking-stars` is what is available, and it suffices. -/
theorem exists_tgt_star_subset_region' (hy : y ∈ L.region') :
    ∃ n, (L.tgt n).star ((L.tgt n).carrier y) ⊆ L.region' := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 L.isOpen_region' y hy
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero L.tendsto_eps hr
  refine ⟨n, fun w hw => hball (Metric.mem_ball.2 ?_)⟩
  have h₁ : dist w y ≤ diam ((L.tgt n).star ((L.tgt n).carrier y)) :=
    dist_le_diam_of_mem (isBounded_tgt_star n _) hw
      ((L.tgtDecomp n).mem_star_carrier (region'_subset_dom' hy))
  have h₂ := L.diam_tgtStar_le n ((L.tgtDecomp n).mem_cells_carrier (region'_subset_dom' hy))
  linarith

/-- **`prop:F-surjective`**: every point of `Q°` is `F` of a point of `D`. -/
theorem exists_mem_region_F_eq (hy : y ∈ L.region') : ∃ x, x ∈ L.region ∧ L.F x = y := by
  obtain ⟨n, hn⟩ := exists_tgt_star_subset_region' hy
  obtain ⟨x, hx⟩ := nonempty_iInter_preStar (region'_subset_dom' hy)
  have hmem : ∀ m, x ∈ L.preStar m y := Set.mem_iInter.1 hx
  have hxD : x ∈ L.dom := srcStar_subset_dom 0 _ (hmem 0)
  refine ⟨x, ⟨hxD, fun hb => ?_⟩, F_eq_of_mem_iInter_preStar (region'_subset_dom' hy) hxD hmem⟩
  -- the stage-`n` source star of the target carrier of `y` misses `C`, by `lem:outer-incidence`
  obtain ⟨w, hw, hwb⟩ := (L.star_meets_bdry_iff n ((L.tgt n).carrier y)).1 ⟨x, hmem n, hb⟩
  exact (hn hw).2 hwb

/-! #### Exact cell correspondence -/

/-- A point of the open region has a nonboundary carrier: an outer cell's open cell lies on the
outer cycle. -/
theorem src_carrier_notMem_outerCells (hx : x ∈ L.region) (n : ℕ) :
    (L.src n).carrier x ∉ (L.str n).outerCells := fun hc =>
  hx.2 (by
    rw [← L.srcOuterSet n]
    exact Realization.cell_subset_outerSet hc ((L.srcDecomp n).mem_cell_carrier hx.1))

/-- The half of `lem:exact-cell-correspondence` that carries the argument: an open source 2-cell
is mapped **into** the corresponding open target 2-cell.

The closed star of a 2-cell is its own closed cell, so `F x` lies in `closure σ'`; if it lay on
the frontier it would be a stage-`n` target skeleton point, and its skeleton preimage `w` would
be a second point of `D` with `F w = F x`, contradicting injectivity — while `x` itself, lying in
an open 2-cell, is not a skeleton point. -/
theorem F_mem_cell_of_mem_cell_face (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).faces)
    (hx : x ∈ (L.src n).cell σ) : L.F x ∈ (L.tgt n).cell σ := by
  have hσc : σ ∈ (L.str n).cells := (L.str n).mem_cells_of_mem_faces hσ
  have hxr : x ∈ L.region :=
    src_cell_subset_region n hσc (notMem_outerCells_of_mem_faces hσ) hx
  have hcar : (L.src n).carrier x = σ := (L.srcDecomp n).carrier_eq hσc hx
  -- `T_n(x)` is exactly the closed target 2-cell
  have hclos : L.F x ∈ closure ((L.tgt n).cell σ) := by
    have := L.F_mem_tgtStar hxr.1 n
    rwa [tgtStar_eq, hcar, (L.tgtDecomp n).star_face_eq_closure (L.comb n) hσ] at this
  rw [(L.tgtDecomp n).closure_eq hσc] at hclos
  obtain ⟨ρ, ⟨hρ, hρsub⟩, hFρ⟩ := Set.mem_iUnion₂.1 hclos
  by_cases hρσ : ρ = σ
  · exact hρσ ▸ hFρ
  -- otherwise `F x` is a stage-`n` target skeleton point; its preimage contradicts injectivity
  exfalso
  have hFskel : L.F x ∈ (L.tgt n).skeletonSet :=
    Realization.cell_subset_skeletonSet (mem_skel_of_sub_face (L.comb n) hρ hρsub hρσ) hFρ
  obtain ⟨w, hwskel, hwF⟩ : ∃ w ∈ (L.src n).skeletonSet, (L.skelHomeo n).toFun w = L.F x := by
    rw [← (L.skelHomeo n).image_skeletonSet] at hFskel
    exact hFskel
  have hFr : L.F x ∈ L.region' := F_mem_region' hxr
  have hwr : w ∈ L.region := by
    refine ⟨(L.srcDecomp n).skeletonSet_subset_domain hwskel, fun hb => hFr.2 ?_⟩
    rw [← L.tgtOuterSet n, ← hwF, ← (L.skelHomeo n).image_outerSet]
    exact Set.mem_image_of_mem _ (by rwa [L.srcOuterSet n])
  have hwx : w = x := L.injOn_F hwr hxr (by
    rw [F_eq_skelHomeo hwskel hwr.1, hwF])
  exact Set.disjoint_left.1 ((L.srcDecomp n).cell_disjoint_skeletonSet hσ) hx (hwx ▸ hwskel)

/-- **`lem:exact-cell-correspondence`**: `F` carries each nonboundary open cell of the stage-`n`
source decomposition **onto** the corresponding open cell of the target decomposition. For a 0- or
1-cell this is `prop:skeleton-agreement` together with the skeleton homeomorphism; for a 2-cell it
is the previous lemma plus surjectivity. -/
theorem image_cell (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).cells)
    (hout : σ ∉ (L.str n).outerCells) : L.F '' ((L.src n).cell σ) = (L.tgt n).cell σ := by
  by_cases hskel : σ ∈ V((L.str n).skel) ∪ E((L.str n).skel)
  · -- on the skeleton `F` *is* `g_n`
    rw [Set.image_congr (fun w hw => F_eq_skelHomeo
      (Realization.cell_subset_skeletonSet hskel hw)
      ((L.srcDecomp n).cell_subset_domain hσ hw))]
    exact (L.skelHomeo n).image_cell hskel
  have hface : σ ∈ (L.str n).faces := mem_faces_of_notMem_skel hσ hskel
  refine Set.Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact F_mem_cell_of_mem_cell_face n hface hw
  -- surjectivity produces a preimage; its carrier is a 2-cell, and open 2-cells are disjoint
  obtain ⟨w, hwr, rfl⟩ := exists_mem_region_F_eq (tgt_cell_subset_region' n hσ hout hy)
  refine Set.mem_image_of_mem _ ?_
  set ρ := (L.src n).carrier w with hρdef
  have hρc : ρ ∈ (L.str n).cells := (L.srcDecomp n).mem_cells_carrier hwr.1
  have hρface : ρ ∈ (L.str n).faces := by
    refine mem_faces_of_notMem_skel hρc fun hmem => ?_
    -- a skeleton carrier would put `F w` on the target skeleton, which misses the open 2-cell
    refine Set.disjoint_left.1 ((L.tgtDecomp n).cell_disjoint_skeletonSet hface) hy ?_
    rw [F_eq_skelHomeo (Realization.cell_subset_skeletonSet hmem
      ((L.srcDecomp n).mem_cell_carrier hwr.1)) hwr.1]
    refine Realization.cell_subset_skeletonSet hmem ?_
    rw [← (L.skelHomeo n).image_cell hmem]
    exact Set.mem_image_of_mem _ ((L.srcDecomp n).mem_cell_carrier hwr.1)
  have hin : L.F w ∈ (L.tgt n).cell ρ :=
    F_mem_cell_of_mem_cell_face n hρface ((L.srcDecomp n).mem_cell_carrier hwr.1)
  have : ρ = σ := by
    by_contra hne
    exact Set.disjoint_left.1 ((L.tgtDecomp n).disjoint hρc hσ hne) hin hy
  rw [← this]
  exact (L.srcDecomp n).mem_cell_carrier hwr.1

/-- **The corollary the inverse argument runs on**: `F` matches carriers. -/
theorem tgt_carrier_F (hx : x ∈ L.region) (n : ℕ) :
    (L.tgt n).carrier (L.F x) = (L.src n).carrier x := by
  refine (L.tgtDecomp n).carrier_eq ((L.srcDecomp n).mem_cells_carrier hx.1) ?_
  rw [← image_cell n ((L.srcDecomp n).mem_cells_carrier hx.1)
    (src_carrier_notMem_outerCells hx n)]
  exact Set.mem_image_of_mem _ ((L.srcDecomp n).mem_cell_carrier hx.1)

/-! #### The inverse, and the interior homeomorphism -/

theorem inv_mem_region (hy : y ∈ L.region') : L.inv y ∈ L.region :=
  (inv_spec (exists_mem_region_F_eq hy)).1

theorem F_inv (hy : y ∈ L.region') : L.F (L.inv y) = y :=
  (inv_spec (exists_mem_region_F_eq hy)).2

theorem inv_F (hx : x ∈ L.region) : L.inv (L.F x) = x :=
  L.injOn_F (inv_spec ⟨x, hx, rfl⟩).1 hx (inv_spec ⟨x, hx, rfl⟩).2

/-- `tgt_carrier_F` read at `inv y`. -/
theorem src_carrier_inv (hy : y ∈ L.region') (n : ℕ) :
    (L.src n).carrier (L.inv y) = (L.tgt n).carrier y := by
  have h := tgt_carrier_F (inv_mem_region hy) n
  rw [F_inv hy] at h
  exact h.symm

/-- **`prop:inverse-continuous`**: `F⁻¹ : Q° → D` is continuous. `lem:cell-neighborhood` is
applied on the *target* side; `lem:exact-cell-correspondence`, in the form `src_carrier_inv`,
transports the resulting subcell relation to the source, where the source star of `x` is small. -/
theorem continuousOn_inv (L : LimitTower γ) : ContinuousOn L.inv L.region' := by
  rw [Metric.continuousOn_iff]
  intro y hy η hη
  have hxr : L.inv y ∈ L.region := inv_mem_region hy
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero (tendsto_diam_srcStar_point hxr) hη
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.1 ((L.tgt n).isOpen_cellNbhd y) y ((L.tgt n).mem_cellNbhd_self y)
  refine ⟨δ, hδ, fun z hz hzdist => ?_⟩
  have hsub : (L.str n).sub ((L.tgt n).carrier y) ((L.tgt n).carrier z) :=
    (L.tgtDecomp n).sub_carrier_of_mem_cellNbhd (region'_subset_dom' hy)
      (hball (Metric.mem_ball.2 hzdist)) (region'_subset_dom' hz)
  rw [← src_carrier_inv hy n, ← src_carrier_inv hz n] at hsub
  have hmem : L.inv z ∈ L.srcStar n (L.inv y) :=
    (L.srcDecomp n).star_anti_of_sub (L.comb n) ((L.srcDecomp n).mem_cells_carrier hxr.1)
      ((L.srcDecomp n).mem_cells_carrier (inv_mem_region hz).1) hsub
      ((L.srcDecomp n).mem_star_carrier (inv_mem_region hz).1)
  exact lt_of_le_of_lt
    (dist_le_diam_of_mem (isBounded_srcStar n _) hmem (mem_srcStar_self hxr.1 n)) hn

/-- **`prop:interior-homeomorphism`**: `F : Int(C) → Q°` is a homeomorphism, in the
`Schoenflies.IsHomeoOn` shape — the map, its explicit inverse, and the four laws on the two
sets — that `Endgame.lean` and the boundary-continuity module consume. -/
theorem isHomeoOn_F (L : LimitTower γ) : IsHomeoOn L.F L.inv L.region L.region' where
  mapsTo := fun _ hx => F_mem_region' hx
  mapsTo_inv := fun _ hy => inv_mem_region hy
  continuousOn := L.continuousOn_F.mono region_subset_dom
  continuousOn_inv := L.continuousOn_inv
  invOn := ⟨fun _ hx => inv_F hx, fun _ hy => F_inv hy⟩

end LimitTower

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMesh
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The anchored square mesh

The geometric core of Proposition `prop:anchored-square-mesh`, in vocabulary that exists today:
Part II's cellulations, `V_boundary` and fresh points `u(𝒜)` are not built here, so the mesh is
stated as a **finite plane graph with a straight-line drawing**, with the clauses of the
proposition as separate theorems about it.

## The construction

`squareMesh δ fresh anchors` is `meshCount δ` concentric ring frames of radii
`1/N, 2/N, …, 1` inside `Q = [-1,1]²`, together with one full-length radial spoke
`[z, N⁻¹ • z]` at each fresh boundary point `z`. The list of segments is handed to
`overlayGraph` (Lemma 3.7), which subdivides at every crossing; the anchors are added to the
cut points, which is what makes each of them a vertex.

**This is not literally the blueprint's construction, and the difference is deliberate.** The
blueprint has one collar `λ ≤ ‖x‖∞ ≤ 1` plus a rectangular grid filling `λQ`. Here the collar
is repeated `N` times and there is no grid at all: the innermost square `N⁻¹ Q` is a *single*
cell, of diameter `2√2/N < δ`. That removes the "choose fine enough horizontal and vertical
coordinates, including the four corners and all the points `λ z_i`" step entirely, and makes
the whole mesh radial, so that one estimate — `‖tz - sw‖ ≤ t‖z - w‖ + |t - s|‖w‖`, the
blueprint's own — covers every cell. Nothing downstream can tell the difference: the clauses
are the interface.

The blueprint's cyclic ordering of the fresh points is likewise gone. Where it says "choose
`z_0, …, z_{m-1}` in cyclic order so that each boundary arc between consecutive ones has
diameter `< δ/4`", this module takes the order-free consequence as a hypothesis,
`FreshDense fresh δ`: *every connected subset of `S` avoiding all the fresh points has diameter
at most `δ/2`*. A set-level statement needs no ordering, and it is exactly what the blueprint's
own argument (parametrize `S` by a circle, cut it into small arcs, put one fresh point inside
each) produces.

## What is proved, and what is not

The clauses about faces, anchors, edges reaching `S` and connectedness of `|T| ∖ S` are proved
in full. Two gaps, both stated plainly:

* **The outer cycle is proved only as a point set.** `squareMesh_cover_outerEdges` says the
  edges whose segments lie on `S` occupy exactly `S`. That these edges form a **cycle** of the
  graph is *not* proved: it needs the fresh points, the anchors and the four corners put in
  cyclic order along `S`, which is precisely the ordering this construction was designed to
  avoid. A later module wanting the outer cycle must build it.
* **2-connectivity is not proved at all.** It is not present as a hypothesis either — a
  hypothesis restating the goal would be worthless. The route is the blueprint's: the innermost
  ring is a cycle, and each annulus between consecutive rings is added one rectangle at a time
  by `Graph.IsTwoConnected.union`, each added cycle sharing at least two vertices with what is
  already there. Nothing in this module obstructs it.

Connectedness of `|T| ∖ S` needs at least one fresh point (`hz₀ : z₀ ∈ fresh`): with no spokes
the rings are disjoint frames.

## Blueprint

* `ringSet`, `ringPieces`, `spokePiece`, `meshSegments` — the mesh as a list of segments.
* `meshGraph`, `squareMesh` — Proposition "Anchored square mesh", the construction itself.
* `FreshDense` — the order-free form of "consecutive fresh points bound an arc of diameter
  `< δ/4`".
* `squareMesh_face_small` — clause 1: every bounded 2-cell has diameter `< δ`, and lies in `Q`.
* `squareMesh_anchor_mem_vertexSet` — clause 2: every boundary vertex survives.
* `squareMesh_inner_edge_at_fresh`, `squareMesh_unique_inner_edge` — clauses 3 and 4: a new
  internal edge meeting `S` ends at a fresh point, and exactly one such edge is incident with
  each fresh point.
* `squareMesh_cover_outerEdges` — the point-set half of "`S` is the outer cycle" (see above).
* `squareMesh_isConnected_diff` — clause 6: `|T| ∖ S` is connected.
* `radial_diam_bound` — the blueprint's radial estimate, isolated from all graph language.
* `subdivide_covers_source`, `subdivide_end_of_mem` — two general facts about `subdivide` that
  belong in `Schoenflies/Subdivide.lean`.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### Rings: the frame of a square about the origin -/

/-! ### Radial segments

Every point of a segment between two multiples of `z` is itself a multiple of `z`, with the
coefficient running through the corresponding real segment. This is the only fact about spokes
the whole module uses: along a spoke the coefficient — equivalently, by
`supNorm_smul_of_mem_modelCurve`, the sup norm — is a faithful coordinate. -/

/-! ### Spokes -/

/-! ### Two more facts about `subdivide`

Both are general and belong beside the others in `Schoenflies/Subdivide.lean`; they are here
because that module is on `main`.

`subdivide_covers_source` refines `subdivide_cover`: a point of a *named* source piece lies on
a piece of the subdivision *inside that source*. Without the "inside that source" clause one
cannot tell, of a point where two sources cross, which of them the piece through it came from
— and the whole description of the mesh's edges is by their source.

`subdivide_end_of_mem` is the converse of `subdivide_avoids`: a cut point that lies on a source
piece is not merely absent from every interior, it is an **endpoint** of a piece inside that
source. That is what makes a prescribed point a vertex of the overlay graph. -/

/-! ### Enlarging the list of cut points

Both cut-point conditions ask only that certain points *be* in the list, so both survive
adding more. That is what lets the mesh prescribe extra vertices — the anchors — on top of the
cut points the overlay itself needs. -/

/-! ### The mesh, as a list of segments

`N` concentric ring frames of radii `1/N, 2/N, …, 1`, and one full-length radial spoke at each
fresh boundary point. There is no rectangular grid: the innermost region is the square of
radius `1/N`, which is a single cell of diameter `2√2/N`, so filling it is unnecessary once `N`
is large. That is the one deviation from the blueprint's construction, and it removes the whole
"choose horizontal and vertical coordinates" step. -/

/-! ### The mesh as a plane graph

The cut points are the ones `exists_cut_points` supplies for the mesh segments, *together with*
the prescribed anchors. Enlarging the list is harmless — `EndsAreCut.mono` and
`MeetsAreCut.mono` — and it is what makes each anchor a vertex. -/

theorem meshGraph_isDrawing {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    Graph.IsDrawing (meshGraph N fresh anchors) segmentDrawing :=
  overlayGraph_isDrawing _ _ (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)

/-! ### Clause 2: the anchors are vertices on `S` -/

/-! ### Clause 3: the outer edges occupy exactly `S`

The blueprint asks for `S` to be the union of the edge arcs of a *cycle*. What is proved here
is the point-set half: the edges whose arcs lie on `S` occupy exactly `S`. See the module
docstring. -/

/-! ### Clause 4: the edges that reach `S` from inside

An edge of the mesh that meets `S` without lying on it is a subsegment of a spoke, and it
touches `S` at that spoke's fresh point only. -/

/-! ### Clause 1: every bounded face is small

The estimate is the blueprint's, in radial coordinates. A connected set missing the mesh
misses every ring, so its sup norm — continuous, hence with a preconnected image in `ℝ` —
stays inside one open interval `(k/N, (k+1)/N)` between consecutive ring radii. Inside the
innermost square that is already the whole bound; outside it the radial projection
`x ↦ ‖x‖∞⁻¹ • x` maps the set into `S`, connectedly, and away from every fresh point, because
a point projecting to a fresh point lies on that point's spoke. The blueprint's

  `‖x - y‖ ≤ ‖tz - tw‖ + ‖tw - sw‖ < δ/4 + δ/4 + δ/4`

is then `t‖z - w‖ + |t - s|‖w‖`, with `‖z - w‖` controlled by `FreshDense` and `|t - s|` by
one ring thickness. -/

/-! ### Clause 5: the mesh minus `S` is connected

The inner rings and the spokes-minus-their-outer-endpoint are each connected, every inner ring
meets every spoke, and every spoke meets the innermost ring. So a single point of the innermost
ring reaches everything, which is what `isPreconnected_of_forall` asks for. At least one fresh
point is needed: with no spokes the rings are disjoint circles. -/

/-! ### The mesh of a given size

`meshCount δ` rings make both the innermost square and one ring thickness small compared with
`δ`; `2 √2 < δ N` is the single inequality the whole diameter estimate rests on. -/

/-- The mesh is a plane graph, drawn with straight edges. -/
theorem squareMesh_isDrawing {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane) :
    Graph.IsDrawing (squareMesh δ fresh anchors) segmentDrawing :=
  meshGraph_isDrawing (two_le_meshCount δ) hfresh anchors

end Schoenflies
end



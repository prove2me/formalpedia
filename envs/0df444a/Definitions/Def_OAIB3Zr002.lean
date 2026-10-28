-- Prove2me | Definitions.Def_OAIB3Zr002
-- name    : OAIB3Zr002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T13:13:48.925995+00:00
-- url     : https://prove2.me/theorems/5183bbf0-d7ee-4c5a-af56-e3df89e2863d
-- title:
--   Definitions bundle OAIB3Zr002 of the split of OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 320 declarations of OpenAI's Lean: 135 definitions, 5 inductive types or structures, 2 instances and 178 theorems. The definitions and types are `OAI.Zarankiewicz.DrawingPiece`, `OAI.Zarankiewicz.ExteriorCrossingCut`, `OAI.Zarankiewicz.ExteriorCrossingCut.prefixInSurgery`, `OAI.Zarankiewicz.ExteriorCrossingCut.suffixInSurgery`, `OAI.Zarankiewicz.HasFiniteAffineCover`, `OAI.Zarankiewicz.LocallyStraightCrossings`, `OAI.Zarankiewicz.LocallyTransverseCrossings`, `OAI.Zarankiewicz.PolygonLinePosition`, `OAI.Zarankiewicz.PolygonalChain.Transverse`, `OAI.Zarankiewicz.PolygonalChain.append`, `OAI.Zarankiewicz.PolygonalChain.castEndpoints`, `OAI.Zarankiewicz.PolygonalChain.endFraction`, `OAI.Zarankiewicz.PolygonalChain.endPort`, `OAI.Zarankiewicz.PolygonalChain.path`, `OAI.Zarankiewicz.PolygonalChain.point`, `OAI.Zarankiewicz.PolygonalChain.reverse`, `OAI.Zarankiewicz.PolygonalChain.startFraction`, `OAI.Zarankiewicz.PolygonalChain.startPort`, `OAI.Zarankiewicz.PolygonalChain.truncated`, `OAI.Zarankiewicz.PolygonalChain.truncatedScale`, `OAI.Zarankiewicz.PolygonalChain.truncatedVertices`, `OAI.Zarankiewicz.PolygonalChain.widen`, `OAI.Zarankiewicz.PolygonalChain.withEndpoints`, `OAI.Zarankiewicz.PolygonalExterior`, `OAI.Zarankiewicz.PolygonalExterior.adjacentSurgeryFiniteDrawing`, `OAI.Zarankiewicz.PolygonalExterior.anchoredMiddle`, `OAI.Zarankiewicz.PolygonalExterior.assembledAdmissible`, `OAI.Zarankiewicz.PolygonalExterior.assembledDrawing`, `OAI.Zarankiewicz.PolygonalExterior.assembledEdge`, `OAI.Zarankiewicz.PolygonalExterior.endSpoke`, `OAI.Zarankiewicz.PolygonalExterior.middlePath`, `OAI.Zarankiewicz.PolygonalExterior.orderedBridge`, `OAI.Zarankiewicz.PolygonalExterior.orderedPath`, `OAI.Zarankiewicz.PolygonalExterior.startSpoke`, `OAI.Zarankiewicz.PolygonalParametrization`, `OAI.Zarankiewicz.PolygonalParametrization.containedChain`, `OAI.Zarankiewicz.PolygonalParametrization.pieceTrace`, `OAI.Zarankiewicz.PolygonalParametrization.vertices`, `OAI.Zarankiewicz.StraightEdgeEmbedding`, `OAI.Zarankiewicz.TriangleSegmentPosition` and 100 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Crossing_AdjacentSurgeryDrawing`, `Crossing_AdjacentSurgeryPointRemoval`, `Crossing_AdjacentSurgeryRoutes`, `Crossing_AlternatingPaths`, `Crossing_AssembledAdmissibleDrawing`, `Crossing_AssembledContinuousDrawing`, `Crossing_AssembledCrossings`, `Crossing_AssembledEdge`, `Crossing_AssembledNoTriples`, `Crossing_AssembledPortIncidence`, `Crossing_BipartiteDartGeometry`, `Crossing_Bivariate`, `Crossing_BivariateCoefficients`, `Crossing_ChainTracePieces`, `Crossing_CircleChords`, `Crossing_CircleConnectors`, `Crossing_CircleOffsetLine`, `Crossing_CrossingDiskNeighborhood`, `Crossing_CrossingDiskOwners`, `Crossing_CrossingReconnection`, `Crossing_CrossingSurgeryGraph`, `Crossing_CutTraceSeparation`, `Crossing_CutVertexAvoidance`, `Crossing_CycleBlockIntersections`, `Crossing_CycleEndpointSum`, `Crossing_CycleMatrixBlocks`, `Crossing_DartCyclePaths`, `Crossing_DartPathRealizations`, `Crossing_DetectorCrossingBound`, `Crossing_DrawingEdgeWalk`, `Crossing_DrawingSegmentIncidence`, `Crossing_DrawingSpokePorts`, `Crossing_DrawingSubdivisionGraph`, `Crossing_DrawingVertexPlacement`, `Crossing_DrawingWalkCutTraces`, `Crossing_DrawnEdgeChains`, `Crossing_EmbeddedGraphPaths`, `Crossing_EndpointFlagPairing`, `Crossing_EvaluationAmbient`, `Crossing_ExteriorChordMeeting`, `Crossing_ExteriorCrossingCut`, `Crossing_ExteriorSegmentGraph`, `Crossing_ExteriorSpokeMeeting`, `Crossing_FiniteAffineCover`, `Crossing_FiniteDiskCollar`, `Crossing_FiniteIntersectionDrawing`, `Crossing_FinitePolygonalComposition`, `Crossing_GenericPolygonIntersection`, `Crossing_GraphSequenceWalk`, `Crossing_GraphWalkRealizationLaws`, `Crossing_GraphWalkTrace`, `Crossing_IncidentSpokePorts`, `Crossing_Interpolation`, `Crossing_LocallyStraightNormalization`, `Crossing_LocallyTransverseNormalization`, `Crossing_MiddleEdgeIncidence`, `Crossing_MiddlePathInjective`, `Crossing_MiddleSpokeMeeting`, `Crossing_OffsetTrack`, `Crossing_OffsetVectors`, `Crossing_OpenSegmentEndpoints`, `Crossing_OrderedExteriorPaths`, `Crossing_OrientedSimilarity`, `Crossing_PathConcatenationInjective`, `Crossing_PlanarSegments`, `Crossing_PolygonComposition`, `Crossing_PolygonalArcInjective`, `Crossing_PolygonalBoundaryReplacement`, `Crossing_PolygonalChainComposition`, `Crossing_PolygonalChainExistence`, `Crossing_PolygonalChainShortcuts`, `Crossing_PolygonalChainTransversality`, `Crossing_PolygonalChains`, `Crossing_PolygonalEndpointCasts`, `Crossing_PolygonalExterior`, `Crossing_PolygonalParametrization`, `Crossing_PolygonalWalks`, `Crossing_PolynomialFiltration`, `Crossing_PolynomialKernel`, `Crossing_RadialBoundaryPorts`, `Crossing_RankDetector`, `Crossing_ReconnectedIntersectionCases`, `Crossing_ReconnectedPaths`, `Crossing_ReconnectedPointRemoval`, `Crossing_ReconnectedVertexAvoidance`, `Crossing_ReconnectedWalks`, `Crossing_ReconnectionChords`, `Crossing_ReconnectionOppositeCuts`, `Crossing_ReconnectionOtherEdges`, `Crossing_ReducedPolygonalPresentation`, `Crossing_SegmentAugmentation`, `Crossing_SpokeTrackDirections`, `Crossing_SubdivisionSegments`, `Crossing_SurgeryCrossingContainment`, `Crossing_SurgeryCutWalks`, `Crossing_SurgeryFiniteDrawing`, `Crossing_SurgeryNoTriples`, `Crossing_SurgeryPathWitnesses`, `Crossing_SurgeryRouteIntersections`, `Crossing_SurgeryStrictPointCount`, `Crossing_TrackEndpointConnections`, `Crossing_TriangleEntryExit`, `Crossing_TriangleTransversality`, `Crossing_TruncatedChainDirections`, `Crossing_TruncatedChainPath`, `Crossing_TruncatedChainVertices`, `Crossing_TruncatedSignedIntersections`, `Crossing_TruncatedSpokeCoordinates`, `Crossing_TruncatedSpokeDirections`, `Crossing_VertexDiskSpokes`, `Crossing_VertexOrderDetector`, `Crossing_VertexPassagePairing`, `Crossing_VertexTruncation`.
--
--   **Imports.** It imports the published bundle `Def_BipartiteCrossing`; the bundles `OAIB3Zr000` and `OAIB3Zr001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIB3Zr004`; the statements `OAI_Zarankiewicz_TruncatedSpokeCoordinates_closed_cycle_matrix_sum`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cross_type_radius`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cycle_block_radius`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.odd_normalized_crossing_lower_bound`, `OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius`, `OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections`, `OAI.Zarankiewicz.finite_intersection_normalization`, `OAI.Zarankiewicz.nonempty_polygonalExterior` and `OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse`; the proofs of `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cross_type_radius`, `OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius`, `OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections`, `OAI.Zarankiewicz.finite_intersection_normalization`, `OAI.Zarankiewicz.mainTarget_proof`, `OAI.Zarankiewicz.nonempty_polygonalExterior` and `OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse`.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr000
import Definitions.Def_OAIB3Zr001

section
-- module Solutions.OAIB3_Zar.Crossing_PlanarSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

def segmentCrossingSign (a b c d : Plane) : ℝ :=
  if SegmentsCrossProperly a b c d then
    (if 0 < det2 (b-a) (d-c) then 1 else -1) else 0

theorem segmentPoint_reverse (a b : Plane) (t : ℝ) :
    segmentPoint b a (1-t) = segmentPoint a b t := by
  simp [segmentPoint, add_comm]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OffsetVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def normalShift (v : Plane) : Plane := (squaredLength v)⁻¹ • rotateQuarter v

def cornerShift (u v : Plane) : Plane := (det2 u v)⁻¹ • (v-u)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteIntersectionDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

instance admissibleToFiniteIntersectionDrawing {m n : ℕ} :
    CoeOut (AdmissibleDrawing m n) (FiniteIntersectionDrawing m n) :=
  ⟨AdmissibleDrawing.toFiniteIntersectionDrawing⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteDiskCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def outsideDisks {ι : Type*} (z : ι → Plane) (r : ℝ) : Set Plane :=
  {x | ∀ i, r^2 < squaredLength (x-z i)}

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def circlePoint (t : ℝ) : Plane := ((1-t^2)/(1+t^2), 2*t/(1+t^2))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexDiskSpokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem spokes_meet_only_at_center (v a b : Plane) (hd : det2 (a-v) (b-v) ≠ 0)
    {x : Plane} (ha : x ∈ segment ℝ v a) (hb : x ∈ segment ℝ v b) : x=v := by
  rw [← Path.range_segment] at ha hb
  obtain ⟨s,hs⟩ := ha
  obtain ⟨t,ht⟩ := hb
  have hs' : segmentPoint v a s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint v b t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have hp := segment_intersection_parameters_unique v a v b hd s.val t.val 0 0
    (hs'.trans ht'.symm) (by simp)
  rw [hp.1,segmentPoint_zero] at hs'
  exact hs'.symm

theorem spoke_in_open_disk (z v a : Plane) (r : ℝ)
    (hv : squaredLength (v-z) < r^2) (ha : squaredLength (a-z)=r^2)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    squaredLength (segmentPoint v a t-z) < r^2 := by
  have he : squaredLength (segmentPoint v a t-z)=
      (1-t)*squaredLength (v-z)+t*squaredLength (a-z)-t*(1-t)*squaredLength (a-v) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hpos := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hv)
  have hnon : 0 ≤ t*(1-t)*squaredLength (a-v) := by
    apply mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2.le))
    dsimp [squaredLength]
    positivity
  rw [he,ha]
  nlinarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingVertexPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem vertex_spoke_injective (C : DrawingPassages D) (v : BipartiteVertex m n → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark i)) :
    Function.Injective (Path.segment (v i) (C.portPoint p.val)) := by
  apply Path.segment_injective_of_ne
  intro he
  have h := hv i
  have hp : squaredLength (C.portPoint p.val-D.vertex i)=C.radius^2 := C.portsAt_on_circle (C.vertexMark i) p
  rw [he,hp] at h
  exact lt_irrefl _ h

theorem vertex_spoke_interior (C : DrawingPassages D) (v : BipartiteVertex m n → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark i)) (t : unitInterval)
    (ht : t < 1) : squaredLength ((Path.segment (v i) (C.portPoint p.val)) t-D.vertex i) < C.radius^2 := by
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact spoke_in_open_disk (D.vertex i) (v i) (C.portPoint p.val) C.radius (hv i)
    (C.portsAt_on_circle (C.vertexMark i) p) t.val ⟨t.property.1,ht⟩

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def polygonIntersection (v w : ℕ → Plane) (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
    segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def reversedSequence (v : ℕ → Plane) (n i : ℕ) : Plane := v (n-i)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

def point (O : Set Plane) (a : Plane) (ha : a ∈ O) : PolygonalChain O a a where
  pieces := 0
  vertices := fun _ => a
  first := rfl
  last := rfl
  start_mem := ha
  inside := by intro i hi; omega

def append (P : PolygonalChain O a b) (c : Plane) (h : segment ℝ b c ⊆ O) : PolygonalChain O a c where
  pieces := P.pieces+1
  vertices := fun i => if i ≤ P.pieces then P.vertices i else c
  first := by simp [P.first]
  last := by simp
  start_mem := P.start_mem
  inside := by
    intro i hi
    by_cases hin : i < P.pieces
    · simpa only [ite_eq_left (show i ≤ P.pieces by omega),ite_eq_left (show i+1 ≤ P.pieces by omega)] using P.inside i hin
    · have he : i=P.pieces := by omega
      subst i
      simpa [P.last] using h

def path (P : PolygonalChain O a b) : Path a b :=
  (polygonalArcPath P.vertices P.pieces).cast P.first.symm P.last.symm

end PolygonalChain

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChainExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem path_range_subset (P : PolygonalChain O a b) : Set.range P.path ⊆ O := by
  change Set.range (polygonalArcPath P.vertices P.pieces) ⊆ O
  exact polygonalArcPath_range_subset P.vertices O (by rw [P.first]; exact P.start_mem) P.pieces P.inside

end PolygonalChain

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChainShortcuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

def withEndpoints (P : PolygonalChain O a b) {a' b' : Plane}
    (ha : a'=a) (hb : b'=b) : PolygonalChain O a' b' where
  pieces := P.pieces
  vertices := P.vertices
  first := P.first.trans ha.symm
  last := P.last.trans hb.symm
  start_mem := ha.symm ▸ P.start_mem
  inside := P.inside

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PathConcatenationInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem path_trans_injective {X : Type*} [TopologicalSpace X] {a b c : X}
    (γ : Path a b) (η : Path b c) (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hm : ∀ x, x ∈ Set.range γ → x ∈ Set.range η → x=b) :
    Function.Injective (γ.trans η) := by
  intro s t he
  by_cases hs : (s : ℝ) ≤ 1/2 <;> by_cases ht : (t : ℝ) ≤ 1/2
  · simp only [Path.trans_apply,dite_eq_left hs,dite_eq_left ht] at he
    have hh := congrArg Subtype.val (hγ he)
    apply Subtype.ext
    change 2*(s : ℝ)=2*(t : ℝ) at hh
    linarith
  · simp only [Path.trans_apply,dite_eq_left hs,dite_eq_right ht] at he
    have hh := congrArg Subtype.val (path_meeting_parameters γ η hγ hη hm _ _ he).2
    change 2*(t : ℝ)-1=0 at hh
    exfalso
    linarith
  · simp only [Path.trans_apply,dite_eq_right hs,dite_eq_left ht] at he
    have hh := congrArg Subtype.val (path_meeting_parameters γ η hγ hη hm _ _ he.symm).2
    change 2*(s : ℝ)-1=0 at hh
    exfalso
    linarith
  · simp only [Path.trans_apply,dite_eq_right hs,dite_eq_right ht] at he
    have hh := congrArg Subtype.val (hη he)
    apply Subtype.ext
    change 2*(s : ℝ)-1=2*(t : ℝ)-1 at hh
    linarith

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalArcInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygonalArcPath_range_piece (v : ℕ → Plane) :
    (n : ℕ) → 0 < n → ∀ x ∈ Set.range (polygonalArcPath v n),
      ∃ i, i < n ∧ x ∈ segment ℝ (v i) (v (i+1))
  | 0, hn, _, _ => by omega
  | 1, _, x, hx => by
    refine ⟨0,by omega,?_⟩
    simpa only [polygonalArcPath,Path.range_segment] using hx
  | n+2, _, x, hx => by
    rw [polygonalArcPath,Path.trans_range] at hx
    rcases hx with hx | hx
    · obtain ⟨i,hi,hh⟩ := polygonalArcPath_range_piece v (n+1) (by omega) x hx
      exact ⟨i,by omega,hh⟩
    · exact ⟨n+1,by omega,by simpa only [Path.range_segment] using hx⟩

theorem polygonalArcPath_injective (v : ℕ → Plane) : (n : ℕ) → 0 < n →
    (∀ i, i < n → v i ≠ v (i+1)) →
    (∀ i j, i < j → j < n → ∀ x,
      x ∈ segment ℝ (v i) (v (i+1)) → x ∈ segment ℝ (v j) (v (j+1)) →
      j=i+1 ∧ x=v j) → Function.Injective (polygonalArcPath v n)
  | 0, hn, _, _ => by omega
  | 1, _, hn, _ => Path.segment_injective_of_ne (hn 0 (by omega))
  | n+2, _, hn, hm => by
    apply path_trans_injective
    · exact polygonalArcPath_injective v (n+1) (by omega)
        (fun i hi => hn i (by omega)) (fun i j hij hj => hm i j hij (by omega))
    · exact Path.segment_injective_of_ne (hn (n+1) (by omega))
    · intro x hx hy
      obtain ⟨i,hi,hh⟩ := polygonalArcPath_range_piece v (n+1) (by omega) x hx
      rw [Path.range_segment] at hy
      exact (hm i (n+1) hi (by omega) x hh hy).2

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalBoundaryReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def PolygonalChain.widen {S T : Set Plane} {a b : Plane} (P : PolygonalChain S a b)
    (hST : S ⊆ T) : PolygonalChain T a b where
  pieces := P.pieces
  vertices := P.vertices
  first := P.first
  last := P.last
  start_mem := hST P.start_mem
  inside := fun i hi => (P.inside i hi).trans hST

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

structure PolygonalExterior (C : DrawingPassages D) where
  chain : ∀ i : C.ArcIndex, PolygonalChain Set.univ (C.arcStart i) (C.arcEnd i)
  injective : ∀ i, Function.Injective (chain i).path
  outside : ∀ i t, t ∈ Set.Ioo (0 : unitInterval) 1 →
    (chain i).path t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius
  disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (chain i).path) (Set.range (chain j).path)

namespace PolygonalExterior
variable {C : DrawingPassages D}

theorem outside_open_disks (E : PolygonalExterior C) (i : C.ArcIndex) (t : unitInterval)
    (x : DrawingMark D) : C.radius^2 ≤ squaredLength ((E.chain i).path t-x.val) := by
  by_cases ht0 : t=0
  · subst t
    rw [(E.chain i).path.source]
    exact C.portPoint_outside_open_disks (i,false) x
  by_cases ht1 : t=1
  · subst t
    rw [(E.chain i).path.target]
    exact C.portPoint_outside_open_disks (i,true) x
  exact (E.outside i t ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩ x).le

theorem avoids_new_vertices (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : C.ArcIndex) (t : unitInterval) (j : BipartiteVertex m n) : (E.chain i).path t ≠ v j := by
  intro he
  have h := E.outside_open_disks i t (C.vertexMark j)
  rw [he] at h
  exact (hv j).not_ge h

theorem parameter_endpoint_of_mem_disk (E : PolygonalExterior C) (i : C.ArcIndex)
    (t : unitInterval) (x : DrawingMark D)
    (ht : (E.chain i).path t ∈ closedRoundDisk x.val C.radius) : t=0 ∨ t=1 := by
  by_cases h0 : t=0
  · exact Or.inl h0
  by_cases h1 : t=1
  · exact Or.inr h1
  have h := E.outside i t ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm h0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) h1⟩ x
  exact False.elim (h.not_ge ht)

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ExteriorChordMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem chord_parameter_endpoint (E : PolygonalExterior C) (i : C.ArcIndex) (p : C.InnerIndex)
    (s t : unitInterval) (he : (E.chain i).path s=C.crossingChord p t) : t=0 ∨ t=1 := by
  by_cases ht0 : t=0
  · exact Or.inl ht0
  by_cases ht1 : t=1
  · exact Or.inr ht1
  have h := C.crossingChord_interior_in_disk p t
    ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
  have hx := E.outside_open_disks i s (C.innerMark p)
  rw [he] at hx
  exact False.elim (h.not_ge hx)

theorem exterior_chord_meeting_parameters (E : PolygonalExterior C) (i : C.ArcIndex) (p : C.InnerIndex)
    (s t : unitInterval) (he : (E.chain i).path s=C.crossingChord p t) :
    (i=C.incomingArc p ∧ s=1 ∧ t=0) ∨ (i=C.outgoingArc p ∧ s=0 ∧ t=1) := by
  have hs := E.parameter_endpoint_of_mem_disk i s (C.innerMark p) (by
    rw [he]
    exact C.crossingChord_range_subset_disk p ⟨t,rfl⟩)
  have ht := E.chord_parameter_endpoint i p s t he
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · simp only [Path.source] at he
    have hp : (i,false)=C.incomingPort p := C.portPoint_injective he
    have hh : false=true := congrArg Prod.snd hp
    cases hh
  · simp only [Path.source,Path.target] at he
    have hp : (i,false)=C.outgoingPort p := C.portPoint_injective he
    exact Or.inr ⟨congrArg Prod.fst hp,rfl,rfl⟩
  · simp only [Path.source,Path.target] at he
    have hp : (i,true)=C.incomingPort p := C.portPoint_injective he
    exact Or.inl ⟨congrArg Prod.fst hp,rfl,rfl⟩
  · simp only [Path.target] at he
    have hp : (i,true)=C.outgoingPort p := C.portPoint_injective he
    have hh : true=false := congrArg Prod.snd hp
    cases hh

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ExteriorSpokeMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem exterior_spoke_meeting_parameters (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (i : C.ArcIndex) (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (s t : unitInterval) (he : (E.chain i).path s=(Path.segment (v j) (C.portPoint p.val)) t) :
    t=1 ∧ ((s=0 ∧ (i,false)=p.val) ∨ (s=1 ∧ (i,true)=p.val)) := by
  have ht : t=1 := by
    apply le_antisymm (show t ≤ 1 from t.property.2)
    apply le_of_not_gt
    intro ht1
    have hinside := C.vertex_spoke_interior v hv j p t ht1
    have hout := E.outside_open_disks i s (C.vertexMark j)
    rw [he] at hout
    exact hinside.not_ge hout
  subst t
  rw [Path.target] at he
  have hs := E.parameter_endpoint_of_mem_disk i s (C.vertexMark j) (by
    rw [he]
    exact (C.portsAt_on_circle (C.vertexMark j) p).le)
  refine ⟨rfl,?_⟩
  rcases hs with rfl | rfl
  · rw [Path.source] at he
    exact Or.inl ⟨rfl,C.portPoint_injective he⟩
  · rw [Path.target] at he
    exact Or.inr ⟨rfl,C.portPoint_injective he⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AlternatingPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem alternatingPath_injective (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) : (n : ℕ) →
    (∀ i, i ≤ n → Function.Injective (p i)) → (∀ i, i < n → Function.Injective (q i)) →
    (∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (Set.range (p i)) (Set.range (p j))) →
    (∀ i j, i < n → j < n → i ≠ j → Disjoint (Set.range (q i)) (Set.range (q j))) →
    (∀ i j, i ≤ n → j < n → ∀ x, x ∈ Set.range (p i) → x ∈ Set.range (q j) →
      (i=j ∧ x=b j) ∨ (i=j+1 ∧ x=a (j+1))) →
    Function.Injective (alternatingPath a b p q n)
  | 0, hp, _, _, _, _ => hp 0 le_rfl
  | n+1, hp, hq, hpp, hqq, hpq => by
    have hprev : Function.Injective (alternatingPath a b p q n) :=
      alternatingPath_injective a b p q n (fun i hi => hp i (by omega))
        (fun i hi => hq i (by omega)) (fun i j hi hj => hpp i j (by omega) (by omega))
        (fun i j hi hj => hqq i j (by omega) (by omega))
        (fun i j hi hj => hpq i j (by omega) (by omega))
    have hfirst : Function.Injective ((alternatingPath a b p q n).trans (q n)) := by
      apply path_trans_injective _ _ hprev (hq n (by omega))
      intro x hx hy
      rcases (alternatingPath_range_iff a b p q n x).mp hx with ⟨i,hi,hh⟩ | ⟨i,hi,hh⟩
      · rcases hpq i n (by omega) (by omega) x hh hy with ⟨he,hx⟩ | ⟨he,hx⟩
        · exact hx
        · omega
      · exact False.elim (Set.disjoint_left.mp (hqq i n (by omega) (by omega) (by omega)) hh hy)
    apply path_trans_injective _ _ hfirst (hp (n+1) le_rfl)
    intro x hx hy
    rw [Path.trans_range] at hx
    rcases hx with hx | hx
    · rcases (alternatingPath_range_iff a b p q n x).mp hx with ⟨i,hi,hh⟩ | ⟨i,hi,hh⟩
      · exact False.elim (Set.disjoint_left.mp (hpp i (n+1) (by omega) le_rfl (by omega)) hh hy)
      · rcases hpq (n+1) i le_rfl (by omega) x hy hh with ⟨he,hx⟩ | ⟨he,hx⟩ <;> omega
    · rcases hpq (n+1) n le_rfl (by omega) x hy hx with ⟨he,hx⟩ | ⟨he,hx⟩
      · omega
      · exact hx

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OrderedExteriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

def orderedPath (E : PolygonalExterior C) (e : BipartiteEdge m n) (i : ℕ) :
    Path (C.arcStart (C.orderedArc e i)) (C.arcEnd (C.orderedArc e i)) :=
  (E.chain (C.orderedArc e i)).path

def orderedBridge (C : DrawingPassages D) (e : BipartiteEdge m n) (i : ℕ) :
    Path (C.arcEnd (C.orderedArc e i)) (C.arcStart (C.orderedArc e (i+1))) := Path.segment _ _

theorem orderedBridge_apply (e : BipartiteEdge m n) (j : ℕ) (hj : j+1 < C.count e)
    (t : unitInterval) :
    orderedBridge C e j t=C.crossingChord (C.orderedInner e j hj) t := by
  change (Path.segment _ _ : Path _ _) t=(Path.segment _ _ : Path _ _) t
  have ha : C.portPoint (C.incomingPort (C.orderedInner e j hj))=C.arcEnd (C.orderedArc e j) := by
    change C.arcEnd (C.incomingArc (C.orderedInner e j hj))=_
    rw [C.orderedInner_incoming]
  have hb : C.portPoint (C.outgoingPort (C.orderedInner e j hj))=C.arcStart (C.orderedArc e (j+1)) := by
    change C.arcStart (C.outgoingArc (C.orderedInner e j hj))=_
    rw [C.orderedInner_outgoing]
  simp only [Path.segment_apply,ha,hb]

theorem orderedBridge_range (e : BipartiteEdge m n) (j : ℕ) (hj : j+1 < C.count e) :
    Set.range (orderedBridge C e j)=Set.range (C.crossingChord (C.orderedInner e j hj)) := by
  congr 1
  funext t
  exact orderedBridge_apply e j hj t

def middlePath (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Path (C.arcStart (C.orderedArc e 0)) (C.arcEnd (C.orderedArc e (C.count e-1))) :=
  alternatingPath (fun i => C.arcStart (C.orderedArc e i))
    (fun i => C.arcEnd (C.orderedArc e i)) (E.orderedPath e) (orderedBridge C e) (C.count e-1)

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MiddlePathInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middlePath_injective (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Function.Injective (E.middlePath e) := by
  have hc := C.count_pos e
  apply alternatingPath_injective
  · intro i hi
    exact E.injective _
  · intro j hj
    have h := C.crossingChord_injective (C.orderedInner e j (by omega))
    intro s t he
    apply h
    simpa only [orderedBridge_apply (C:=C) e j (by omega)] using he
  · intro i j hi hj hij
    exact E.disjoint _ _ (fun he => hij (C.orderedArc_inj e i j (by omega) (by omega) he))
  · intro i j hi hj hij
    rw [orderedBridge_range e i (by omega),orderedBridge_range e j (by omega)]
    apply C.crossingChords_disjoint_of_marks_ne
    intro he
    apply hij
    apply C.orderedInner_inj e i j
    exact C.innerIndex_eq_of_edge_mark _ _ rfl he
  · intro i j hi hj x hx hy
    obtain ⟨s,hs⟩ := hx
    obtain ⟨t,ht⟩ := hy
    have hbridge := orderedBridge_apply (C:=C) e j (by omega) t
    have hm := E.exterior_chord_meeting_parameters (C.orderedArc e i)
      (C.orderedInner e j (by omega)) s t (hs.trans (ht.symm.trans hbridge))
    rcases hm with ⟨he,rfl,rfl⟩ | ⟨he,rfl,rfl⟩
    · rw [C.orderedInner_incoming] at he
      have hij := C.orderedArc_inj e i j (by omega) (by omega) he
      refine Or.inl ⟨hij,?_⟩
      subst i
      exact hs.symm.trans (E.orderedPath e j).target
    · rw [C.orderedInner_outgoing] at he
      have hij := C.orderedArc_inj e i (j+1) (by omega) (by omega) he
      refine Or.inr ⟨hij,?_⟩
      subst i
      exact hs.symm.trans (E.orderedPath e (j+1)).source

theorem middlePath_range_iff (E : PolygonalExterior C) (e : BipartiteEdge m n) (x : Plane) :
    x ∈ Set.range (E.middlePath e) ↔
      (∃ i : C.ArcIndex, i.1=e ∧ x ∈ Set.range (E.chain i).path) ∨
      (∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p)) := by
  have hc := C.count_pos e
  rw [middlePath,alternatingPath_range_iff]
  constructor
  · rintro (⟨i,hi,hx⟩ | ⟨j,hj,hx⟩)
    · exact Or.inl ⟨C.orderedArc e i,rfl,hx⟩
    · exact Or.inr ⟨C.orderedInner e j (by omega),rfl,
        by simpa only [orderedBridge_range (C:=C) e j (by omega)] using hx⟩
  · rintro (⟨⟨f,i⟩,he,hx⟩ | ⟨⟨f,⟨j,hj⟩⟩,he,hx⟩)
    · change f=e at he
      subst f
      refine Or.inl ⟨i.val,by omega,?_⟩
      have heq : C.orderedArc e i.val=⟨e,i⟩ := by
        unfold DrawingPassages.orderedArc
        congr 1
        apply Fin.ext
        change min i.val (C.count e-1)=i.val
        omega
      change x ∈ Set.range (E.chain (C.orderedArc e i.val)).path
      rw [heq]
      exact hx
    · change f=e at he
      subst f
      refine Or.inr ⟨j.val-1,by omega,?_⟩
      rw [orderedBridge_range e (j.val-1) (by omega)]
      have heq : C.orderedInner e (j.val-1) (by omega)=⟨e,⟨j,hj⟩⟩ := by
        unfold DrawingPassages.orderedInner
        congr 1
        apply Subtype.ext
        apply Fin.ext
        change j.val-1+1=j.val
        omega
      rw [heq]
      exact hx

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MiddleSpokeMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem vertex_spoke_range_in_disk (C : DrawingPassages D)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j)) :
    Set.range (Path.segment (v j) (C.portPoint p.val)) ⊆ closedRoundDisk (D.vertex j) C.radius := by
  rintro x ⟨t,rfl⟩
  by_cases ht : t=1
  · subst t
    rw [Path.target]
    exact (C.portsAt_on_circle (C.vertexMark j) p).le
  · exact (C.vertex_spoke_interior v hv j p t
      (lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht)).le

theorem vertex_spokes_disjoint_of_vertices_ne (C : DrawingPassages D)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : BipartiteVertex m n) (hjk : j ≠ k)
    (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k)) :
    Disjoint (Set.range (Path.segment (v j) (C.portPoint p.val)))
      (Set.range (Path.segment (v k) (C.portPoint q.val))) :=
  (C.disks_disjoint _ _ (C.vertexMark_injective.ne hjk)).mono
    (C.vertex_spoke_range_in_disk v hv j p) (C.vertex_spoke_range_in_disk v hv k q)

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middle_spoke_meeting (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : x=C.portPoint p.val := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,⟨s,hs⟩⟩ | ⟨q,hq,hx⟩
  · obtain ⟨t,ht⟩ := hy
    have he := E.exterior_spoke_meeting_parameters v hv i j p s t (hs.trans ht.symm)
    rw [he.1,Path.target] at ht
    exact ht.symm
  · exact False.elim (Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks q j)
      hx (C.vertex_spoke_range_in_disk v hv j p hy))

def anchoredMiddle (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Path (C.arcStart (C.firstArc e)) (C.arcEnd (C.lastArc e)) :=
  (E.middlePath e).cast (congrArg C.arcStart (C.orderedArc_first e).symm)
    (congrArg C.arcEnd (C.orderedArc_last e).symm)

theorem anchoredMiddle_range (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Set.range (E.anchoredMiddle e)=Set.range (E.middlePath e) := rfl

theorem anchoredMiddle_injective (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Function.Injective (E.anchoredMiddle e) := E.middlePath_injective e

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AssembledEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

def startSpoke (C : DrawingPassages D) (v : BipartiteVertex m n → Plane) (e : BipartiteEdge m n) :
    Path (v (.inl e.1)) (C.arcStart (C.firstArc e)) := Path.segment _ _

def endSpoke (C : DrawingPassages D) (v : BipartiteVertex m n → Plane) (e : BipartiteEdge m n) :
    Path (C.arcEnd (C.lastArc e)) (v (.inr e.2)) := (Path.segment _ _).symm

def assembledEdge (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (e : BipartiteEdge m n) : Path (v (.inl e.1)) (v (.inr e.2)) :=
  ((startSpoke C v e).trans (E.anchoredMiddle e)).trans (endSpoke C v e)

theorem startSpoke_injective (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n) :
    Function.Injective (startSpoke C v e) := C.vertex_spoke_injective v hv _ (C.startPortAt e)

theorem endSpoke_range (v : BipartiteVertex m n → Plane) (e : BipartiteEdge m n) :
    Set.range (endSpoke C v e)=Set.range (Path.segment (v (.inr e.2)) (C.portPoint (C.endPortAt e).val)) := by
  exact Path.symm_range _

theorem endSpoke_injective (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n) :
    Function.Injective (endSpoke C v e) := by
  intro s t he
  have hh := C.vertex_spoke_injective v hv _ (C.endPortAt e) he
  have hval := congrArg Subtype.val hh
  apply Subtype.ext
  change 1-s.val=1-t.val at hval
  linarith

theorem assembledEdge_injective (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n) :
    Function.Injective (E.assembledEdge v e) := by
  have hfirst : Function.Injective ((startSpoke C v e).trans (E.anchoredMiddle e)) := by
    apply path_trans_injective _ _ (startSpoke_injective v hv e) (E.anchoredMiddle_injective e)
    intro x hx hy
    exact E.middle_spoke_meeting v hv e _ (C.startPortAt e) x hy hx
  apply path_trans_injective _ _ hfirst (endSpoke_injective v hv e)
  intro x hx hy
  rw [Path.trans_range] at hx
  rw [endSpoke_range] at hy
  rcases hx with hx | hx
  · have hd := C.vertex_spokes_disjoint_of_vertices_ne v hv (.inl e.1) (.inr e.2)
      (by simp) (C.startPortAt e) (C.endPortAt e)
    exact False.elim (Set.disjoint_left.mp hd hx hy)
  · exact E.middle_spoke_meeting v hv e _ (C.endPortAt e) x hx hy

theorem assembledEdge_range_iff (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (e : BipartiteEdge m n) (x : Plane) :
    x ∈ Set.range (E.assembledEdge v e) ↔
      (x ∈ Set.range (startSpoke C v e) ∨
        (∃ i : C.ArcIndex, i.1=e ∧ x ∈ Set.range (E.chain i).path) ∨
        (∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p))) ∨
      x ∈ Set.range (endSpoke C v e) := by
  simp only [assembledEdge,Path.trans_range,Set.mem_union,anchoredMiddle_range,E.middlePath_range_iff]

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AssembledContinuousDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem vertex_spoke_vertex_eq (C : DrawingPassages D)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (hk : v k ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : k=j := by
  by_contra hkj
  have hd := C.disks_disjoint _ _ (C.vertexMark_injective.ne (Ne.symm hkj))
  exact Set.disjoint_left.mp hd (C.vertex_spoke_range_in_disk v hv j p hk) (hv k).le

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middlePath_avoids_vertices (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n)
    (j : BipartiteVertex m n) : v j ∉ Set.range (E.middlePath e) := by
  intro hx
  rcases (E.middlePath_range_iff e (v j)).mp hx with ⟨i,hi,⟨t,ht⟩⟩ | ⟨p,hp,hx⟩
  · exact E.avoids_new_vertices v hv i t j ht
  · exact Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks p j) hx (hv j).le

theorem assembledEdge_vertex_eq (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n)
    (j : BipartiteVertex m n) (hj : v j ∈ Set.range (E.assembledEdge v e)) :
    j=.inl e.1 ∨ j=.inr e.2 := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hj
  rcases hj with (hj | hj) | hj
  · exact Or.inl (C.vertex_spoke_vertex_eq v hv _ j (C.startPortAt e) hj)
  · exact False.elim (E.middlePath_avoids_vertices v hv e j hj)
  · rw [endSpoke_range] at hj
    exact Or.inr (C.vertex_spoke_vertex_eq v hv _ j (C.endPortAt e) hj)

theorem assembledEdge_interior_avoids_vertices (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1)
    (j : BipartiteVertex m n) : E.assembledEdge v e t ≠ v j := by
  intro he
  rcases E.assembledEdge_vertex_eq v hv e j ⟨t,he⟩ with rfl | rfl
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).source.symm)
    exact ht.1.ne hh.symm
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).target.symm)
    exact ht.2.ne hh

def assembledDrawing (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hvinj : Function.Injective v) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) :
    ContinuousDrawing m n where
  vertex := v
  vertex_injective := hvinj
  edge := E.assembledEdge v
  edge_injective := E.assembledEdge_injective v hv
  interior_avoids_vertices := E.assembledEdge_interior_avoids_vertices v hv

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MiddleEdgeIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middle_exterior_edge_eq (E : PolygonalExterior C) (e : BipartiteEdge m n)
    (i : C.ArcIndex) (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (E.chain i).path) : e=i.1 := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨j,hj,hx⟩ | ⟨p,hp,hx⟩
  · have he : j=i := by
      by_contra hji
      exact Set.disjoint_left.mp (E.disjoint j i hji) hx hy
    exact hj.symm.trans (congrArg Sigma.fst he)
  · obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    rcases E.exterior_chord_meeting_parameters i p s t (hs.trans ht.symm) with
      ⟨hi,_,_⟩ | ⟨hi,_,_⟩
    · exact hp.symm.trans (congrArg Sigma.fst hi).symm
    · exact hp.symm.trans (congrArg Sigma.fst hi).symm

theorem middle_spoke_edge_eq (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : e=p.val.1.1 := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,⟨s,hs⟩⟩ | ⟨q,hq,hx⟩
  · obtain ⟨t,ht⟩ := hy
    have hm := E.exterior_spoke_meeting_parameters v hv i j p s t (hs.trans ht.symm)
    rcases hm.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact hi.symm.trans (congrArg (fun r : C.Port => r.1.1) he)
    · exact hi.symm.trans (congrArg (fun r : C.Port => r.1.1) he)
  · exact False.elim (Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks q j)
      hx (C.vertex_spoke_range_in_disk v hv j p hy))

theorem middle_middle_meeting_chords (E : PolygonalExterior C) (e f : BipartiteEdge m n)
    (hef : e ≠ f) (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (E.middlePath f)) :
    ∃ p q : C.InnerIndex, p.1=e ∧ q.1=f ∧
      x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q) := by
  have he : ∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p) := by
    rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,hh⟩ | hh
    · exact False.elim (hef ((E.middle_exterior_edge_eq f i x hy hh).trans hi).symm)
    · exact hh
  have hf : ∃ q : C.InnerIndex, q.1=f ∧ x ∈ Set.range (C.crossingChord q) := by
    rcases (E.middlePath_range_iff f x).mp hy with ⟨i,hi,hh⟩ | hh
    · exact False.elim (hef ((E.middle_exterior_edge_eq e i x hx hh).trans hi))
    · exact hh
  obtain ⟨p,hp,hxp⟩ := he
  obtain ⟨q,hq,hxq⟩ := hf
  exact ⟨p,q,hp,hq,hxp,hxq⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AssembledCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem vertex_spokes_meeting (C : DrawingPassages D)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (j k : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k))
    (hpq : p.val ≠ q.val) (x : Plane)
    (hx : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val)))
    (hy : x ∈ Set.range (Path.segment (v k) (C.portPoint q.val))) : x=v j := by
  by_cases hjk : j=k
  · subst k
    exact spokes_meet_only_at_center _ _ _ (hdet j p q (fun he => hpq (congrArg Subtype.val he)))
      (by simpa only [Path.range_segment] using hx) (by simpa only [Path.range_segment] using hy)
  · exact False.elim (Set.disjoint_left.mp (C.vertex_spokes_disjoint_of_vertices_ne v hv j k hjk p q) hx hy)

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem assembled_spoke_meeting (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e : BipartiteEdge m n) (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (hep : e ≠ p.val.1.1) (x : Plane) (hx : x ∈ Set.range (E.assembledEdge v e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : x=v j := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hx
  rcases hx with (hx | hx) | hx
  · exact C.vertex_spokes_meeting v hv hdet j _ p (C.startPortAt e)
      (fun he => hep (congrArg (fun r : C.Port => r.1.1) he).symm) x hy hx
  · exact False.elim (hep (E.middle_spoke_edge_eq v hv e j p x hx hy))
  · rw [endSpoke_range] at hx
    exact C.vertex_spokes_meeting v hv hdet j _ p (C.endPortAt e)
      (fun he => hep (congrArg (fun r : C.Port => r.1.1) he).symm) x hy hx

theorem assembled_meeting_chords (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : BipartiteEdge m n) (hef : e ≠ f) (x : Plane)
    (havoid : ∀ j, x ≠ v j) (hx : x ∈ Set.range (E.assembledEdge v e))
    (hy : x ∈ Set.range (E.assembledEdge v f)) :
    ∃ p q : C.InnerIndex, p.1=e ∧ q.1=f ∧
      x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q) := by
  have hm (a b : BipartiteEdge m n) (hab : a ≠ b)
      (ha : x ∈ Set.range (E.assembledEdge v a)) (hb : x ∈ Set.range (E.assembledEdge v b)) :
      x ∈ Set.range (E.middlePath a) := by
    rw [assembledEdge,Path.trans_range,Path.trans_range] at ha
    rcases ha with (ha | ha) | ha
    · exact False.elim (havoid _ (E.assembled_spoke_meeting v hv hdet b _ (C.startPortAt a)
        (Ne.symm hab) x hb ha))
    · exact ha
    · rw [endSpoke_range] at ha
      exact False.elim (havoid _ (E.assembled_spoke_meeting v hv hdet b _ (C.endPortAt a)
        (Ne.symm hab) x hb ha))
  exact E.middle_middle_meeting_chords e f hef x (hm e f hef hx hy) (hm f e (Ne.symm hef) hy hx)

theorem assembled_crossings_subset (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    crossingPoints (E.assembledDrawing v hvinj hv) ⊆ C.chordCrossings := by
  rintro x ⟨e,f,hef,⟨s,hs,he⟩,⟨t,ht,hf⟩⟩
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq))
    ⟨s,he⟩ ⟨t,hf⟩
  exact ⟨p,q,(fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))),hxp,hxq⟩

theorem assembled_crossings_finite (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    (crossingPoints (E.assembledDrawing v hvinj hv)).Finite :=
  C.chordCrossings_finite.subset (E.assembled_crossings_subset v hvinj hv hdet)

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AssembledPortIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem portPoint_mem_exterior (E : PolygonalExterior C) (p : C.Port) :
    C.portPoint p ∈ Set.range (E.chain p.1).path := by
  rcases p with ⟨i,b⟩
  cases b
  · exact ⟨0,(E.chain i).path.source⟩
  · exact ⟨1,(E.chain i).path.target⟩

theorem assembled_exterior_edge_eq (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (i : C.ArcIndex) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hy : x ∈ Set.range (E.chain i).path) : e=i.1 := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    have hh := E.exterior_spoke_meeting_parameters v hv i _ (C.startPortAt e) s t (hs.trans ht.symm)
    rcases hh.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
  · exact E.middle_exterior_edge_eq e i x hx hy
  · rw [endSpoke_range] at hx
    obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    have hh := E.exterior_spoke_meeting_parameters v hv i _ (C.endPortAt e) s t (hs.trans ht.symm)
    rcases hh.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm

theorem assembled_port_unique_edge (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (p : C.Port)
    (hp : C.portPoint p ∈ Set.range (E.assembledEdge v e)) : e=p.1.1 :=
  E.assembled_exterior_edge_eq v hv e p.1 (C.portPoint p) hp (E.portPoint_mem_exterior p)

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteAffineCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def HasFiniteAffineCover {a b : Plane} (γ : Path a b) : Prop :=
  ∃ S : Finset (unitInterval × unitInterval),
    (∀ ab ∈ S, ab.1 < ab.2) ∧
    (∀ t : unitInterval, ∃ ab ∈ S, ab.1 ≤ t ∧ t ≤ ab.2) ∧
    (∀ ab ∈ S, ∀ t : unitInterval,
      γ (intervalSegment ab.1 ab.2 t)=segmentPoint (γ ab.1) (γ ab.2) t.val)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_EmbeddedGraphPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def StraightEdgeEmbedding {V : Type*} (G : SimpleGraph V) (pos : V → Plane) : Prop :=
  Function.Injective pos ∧
    ∀ a b c d, G.Adj a b → G.Adj c d → ∀ x,
      x ∈ segment ℝ (pos a) (pos b) → x ∈ segment ℝ (pos c) (pos d) →
      (a=c ∧ b=d) ∨ (a=d ∧ b=c) ∨
      (a=c ∧ x=pos a) ∨ (a=d ∧ x=pos a) ∨
      (b=c ∧ x=pos b) ∨ (b=d ∧ x=pos b)

def graphWalkPath {V : Type*} {G : SimpleGraph V} (pos : V → Plane) {a b : V} (p : G.Walk a b) :
    Path (pos a) (pos b) :=
  (polygonalArcPath (fun i => pos (p.getVert i)) p.length).cast
    (congrArg pos p.getVert_zero).symm (congrArg pos p.getVert_length).symm

theorem graphWalkPath_injective {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    (hemb : StraightEdgeEmbedding G pos) {a b : V} (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath) : Function.Injective (graphWalkPath pos p) := by
  have hn : 0 < p.length := by
    by_contra h
    have hz : p.length=0 := by omega
    have he := p.getVert_zero.symm.trans (hz ▸ p.getVert_length)
    exact hab he
  change Function.Injective (polygonalArcPath (fun i => pos (p.getVert i)) p.length)
  apply polygonalArcPath_injective _ _ hn
  · intro i hi he
    have hij := hp.getVert_injOn (show i ≤ p.length by omega) (show i+1 ≤ p.length by omega) (hemb.1 he)
    omega
  · intro i j hij hj x hx hy
    have hmeet := hemb.2 _ _ _ _ (p.adj_getVert_succ (show i < p.length by omega))
      (p.adj_getVert_succ hj) x hx hy
    have hindex (r s : ℕ) (hr : r ≤ p.length) (hs : s ≤ p.length)
        (he : p.getVert r=p.getVert s) : r=s := hp.getVert_injOn hr hs he
    rcases hmeet with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,hx⟩ | ⟨h₁,hx⟩ | ⟨h₁,hx⟩ | ⟨h₁,hx⟩
    · have hh := hindex i j (by omega) (by omega) h₁
      omega
    · have hh := hindex i (j+1) (by omega) (by omega) h₁
      omega
    · have hh := hindex i j (by omega) (by omega) h₁
      omega
    · have hh := hindex i (j+1) (by omega) (by omega) h₁
      omega
    · have hh := hindex (i+1) j (by omega) (by omega) h₁
      exact ⟨hh.symm,hx.trans (congrArg pos h₁)⟩
    · have hh := hindex (i+1) (j+1) (by omega) (by omega) h₁
      omega

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OffsetTrack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def trackDirection (v : ℕ → Plane) (i : ℕ) : Plane := v (i+1)-v i

def trackOffset (v : ℕ → Plane) (n i : ℕ) : Plane :=
  if i=0 then normalShift (trackDirection v 0)
  else if i < n then cornerShift (trackDirection v (i-1)) (trackDirection v i)
  else normalShift (trackDirection v (n-1))

def shiftedTrack (v : ℕ → Plane) (n : ℕ) (t : ℝ) (i : ℕ) : Plane :=
  v i+t • trackOffset v n i

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalParametrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

structure PolygonalParametrization {a b : Plane} (γ : Path a b) where
  pieces : ℕ
  knot : Fin (pieces+1) → unitInterval
  increasing : StrictMono knot
  first : knot 0=0
  last : knot (Fin.last pieces)=1
  affine : ∀ i : Fin pieces, ∀ t : unitInterval,
    γ (intervalSegment (knot i.castSucc) (knot i.succ) t) =
      segmentPoint (γ (knot i.castSucc)) (γ (knot i.succ)) t.val

namespace PolygonalParametrization
variable {a b : Plane} {γ : Path a b}

def vertices (P : PolygonalParametrization γ) (i : ℕ) : Plane :=
  γ (P.knot ⟨min i P.pieces,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)

theorem vertices_at (P : PolygonalParametrization γ) (i : Fin (P.pieces+1)) :
    P.vertices i.val=γ (P.knot i) := by
  unfold vertices
  congr 2
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)

theorem vertices_first (P : PolygonalParametrization γ) : P.vertices 0=a := by
  have he := P.vertices_at (0 : Fin (P.pieces+1))
  rw [P.first] at he
  simpa using he.trans γ.source

theorem vertices_last (P : PolygonalParametrization γ) : P.vertices P.pieces=b := by
  have he := P.vertices_at (Fin.last P.pieces)
  rw [P.last] at he
  simpa using he.trans γ.target

end PolygonalParametrization
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SubdivisionSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalParametrization
variable {a b : Plane} {γ : Path a b}

def pieceTrace (P : PolygonalParametrization γ) (i : Fin P.pieces) : Set Plane :=
  segment ℝ (γ (P.knot i.castSucc)) (γ (P.knot i.succ))

theorem pieceTrace_parameter (P : PolygonalParametrization γ) (i : Fin P.pieces)
    (x : Plane) (hx : x ∈ P.pieceTrace i) :
    ∃ t : unitInterval, γ (intervalSegment (P.knot i.castSucc) (P.knot i.succ) t)=x := by
  rw [pieceTrace,← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  refine ⟨t,(P.affine i t).trans ?_⟩
  simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht

theorem pieceTrace_subset_range (P : PolygonalParametrization γ) (i : Fin P.pieces) :
    P.pieceTrace i ⊆ Set.range γ := by
  intro x hx
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter i x hx
  exact ⟨intervalSegment (P.knot i.castSucc) (P.knot i.succ) t,ht⟩

end Zarankiewicz.PolygonalParametrization

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingSegmentIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

abbrev DrawingPiece {D : AdmissibleDrawing m n} (P : ∀ e, PolygonalParametrization (D.edge e)) :=
  (e : BipartiteEdge m n) × Fin (P e).pieces

def drawingPieceStart {D : AdmissibleDrawing m n} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.castSucc)

def drawingPieceEnd {D : AdmissibleDrawing m n} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.succ)

theorem drawingPiece_endpoints_ne {D : AdmissibleDrawing m n}
    (P : ∀ e, PolygonalParametrization (D.edge e)) (i : DrawingPiece P) :
    drawingPieceStart P i ≠ drawingPieceEnd P i := by
  intro he
  have hh := D.edge_injective i.1 he
  exact ((P i.1).increasing (show i.2.castSucc < i.2.succ by change i.2.val < i.2.val+1; omega)).ne hh

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingSubdivisionGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : AdmissibleDrawing m n}

def drawingSubdivisionGraph (P : ∀ e, PolygonalParametrization (D.edge e)) : SimpleGraph Plane where
  Adj := fun a b => a ≠ b ∧ ∃ p : DrawingPiece P,
    (a=drawingPieceStart P p ∧ b=drawingPieceEnd P p) ∨
      (a=drawingPieceEnd P p ∧ b=drawingPieceStart P p)
  symm := ⟨by
    rintro a b ⟨hab,p,hp⟩
    refine ⟨Ne.symm hab,p,?_⟩
    rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inr ⟨hb,ha⟩
    · exact Or.inl ⟨hb,ha⟩⟩
  loopless := ⟨by rintro a ⟨ha,_⟩; exact ha rfl⟩

theorem drawingSubdivisionGraph_piece_adj (P : ∀ e, PolygonalParametrization (D.edge e))
    (p : DrawingPiece P) :
    (drawingSubdivisionGraph P).Adj (drawingPieceStart P p) (drawingPieceEnd P p) :=
  ⟨drawingPiece_endpoints_ne P p,p,Or.inl ⟨rfl,rfl⟩⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GraphWalkTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygonalArcPath_piece_subset_range (v : ℕ → Plane) :
    (k : ℕ) → ∀ i, i < k → segment ℝ (v i) (v (i+1)) ⊆ Set.range (polygonalArcPath v k)
  | 0, i, hi => by omega
  | 1, i, hi => by
    have he : i=0 := by omega
    subst i
    rw [polygonalArcPath,Path.range_segment]
  | k+2, i, hi => by
    rw [polygonalArcPath,Path.trans_range]
    by_cases hin : i < k+1
    · exact (polygonalArcPath_piece_subset_range v (k+1) i hin).trans Set.subset_union_left
    · have he : i=k+1 := by omega
      subst i
      rw [Path.range_segment]
      exact Set.subset_union_right

theorem graphWalkPath_dart_subset_range {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) (d : G.Dart) (hd : d ∈ p.darts) :
    segment ℝ (pos d.fst) (pos d.snd) ⊆ Set.range (graphWalkPath pos p) := by
  obtain ⟨i,hi,hfst,hsnd⟩ := walk_dart_parameters p d hd
  rw [hfst,hsnd]
  exact polygonalArcPath_piece_subset_range (fun i => pos (p.getVert i)) p.length i hi

theorem graphWalkPath_range_subset_of_darts_subset {V : Type*} {G : SimpleGraph V}
    (pos : V → Plane) {a b : V} (p q : G.Walk a b) (hd : q.darts ⊆ p.darts) :
    Set.range (graphWalkPath pos q) ⊆ Set.range (graphWalkPath pos p) := by
  intro x hx
  by_cases hq : q.length=0
  · change x ∈ Set.range (polygonalArcPath (fun i => pos (q.getVert i)) q.length) at hx
    rw [hq] at hx
    obtain ⟨t,ht⟩ := hx
    have he : x=pos a := by simpa [polygonalArcPath,q.getVert_zero] using ht.symm
    exact ⟨0,(graphWalkPath pos p).source.trans he.symm⟩
  · obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (fun i => pos (q.getVert i)) q.length (by omega) x hx
    obtain ⟨d,hdq,hfst,hsnd⟩ := walk_dart_at q i hi
    apply graphWalkPath_dart_subset_range pos p d (hd hdq)
    simpa only [hfst,hsnd] using hxi

theorem graphWalkPath_bypass_range_subset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (pos : V → Plane) {a b : V} (p : G.Walk a b) :
    Set.range (graphWalkPath pos p.bypass) ⊆ Set.range (graphWalkPath pos p) :=
  graphWalkPath_range_subset_of_darts_subset pos p p.bypass p.darts_bypass_subset_darts

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GraphSequenceWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem graphSequenceWalk_getVert {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (h : ∀ i, i < k → G.Adj (v i) (v (i+1))) →
    ∀ i, i ≤ k → (graphSequenceWalk G v k h).getVert i=v i
  | 0, h, i, hi => by
    have he : i=0 := by omega
    subst i
    exact SimpleGraph.Walk.getVert_zero _
  | k+1, h, i, hi => by
    by_cases hik : i ≤ k
    · rw [graphSequenceWalk,SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append',
        graphSequenceWalk_length,ite_eq_left hik]
      exact graphSequenceWalk_getVert G v k _ i hik
    · have he : i=k+1 := by omega
      subst i
      simpa only [graphSequenceWalk_length] using (graphSequenceWalk G v (k+1) h).getVert_length

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingEdgeWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem drawingEdgeSequence_adj (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) (i : ℕ) (hi : i < (P e).pieces) :
    (drawingSubdivisionGraph P).Adj ((P e).vertices i) ((P e).vertices (i+1)) := by
  let j : Fin (P e).pieces := ⟨i,hi⟩
  have h0 : (P e).vertices i=drawingPieceStart P ⟨e,j⟩ := (P e).vertices_at j.castSucc
  have h1 : (P e).vertices (i+1)=drawingPieceEnd P ⟨e,j⟩ := (P e).vertices_at j.succ
  rw [h0,h1]
  exact drawingSubdivisionGraph_piece_adj P ⟨e,j⟩

def drawingEdgeWalk (P : ∀ e, PolygonalParametrization (D.edge e)) (e : BipartiteEdge m n) :
    (drawingSubdivisionGraph P).Walk (D.vertex (.inl e.1)) (D.vertex (.inr e.2)) :=
  (graphSequenceWalk (drawingSubdivisionGraph P) (P e).vertices (P e).pieces
    (drawingEdgeSequence_adj P e)).copy (P e).vertices_first (P e).vertices_last

theorem drawingEdgeWalk_length (P : ∀ e, PolygonalParametrization (D.edge e)) (e : BipartiteEdge m n) :
    (drawingEdgeWalk P e).length=(P e).pieces := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.length_copy,graphSequenceWalk_length]

theorem drawingEdgeWalk_getVert (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) (i : ℕ) (hi : i ≤ (P e).pieces) :
    (drawingEdgeWalk P e).getVert i=(P e).vertices i := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.getVert_copy]
  exact graphSequenceWalk_getVert _ _ _ _ i hi

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AssembledNoTriples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem assembled_no_triples (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f g : BipartiteEdge m n) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    edgeInterior (E.assembledDrawing v hvinj hv) e ∩
      edgeInterior (E.assembledDrawing v hvinj hv) f ∩
      edgeInterior (E.assembledDrawing v hvinj hv) g=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨⟨⟨s,hs,he⟩,⟨t,ht,hf⟩⟩,⟨u,hu,hg⟩⟩
  have ha : ∀ j, x ≠ v j := fun j heq =>
    E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x ha ⟨s,he⟩ ⟨t,hf⟩
  obtain ⟨r,z,hr,hz,hxr,hxz⟩ := E.assembled_meeting_chords v hv hdet e g heg x ha ⟨s,he⟩ ⟨u,hg⟩
  apply C.innerMark_no_triples p q z
  · intro heq
    exact hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  · intro heq
    exact heg (hp.symm.trans ((congrArg Sigma.fst heq).trans hz))
  · intro heq
    exact hfg (hq.symm.trans ((congrArg Sigma.fst heq).trans hz))
  · exact C.chord_meeting_marks_eq p q hxp hxq
  · exact C.chord_meeting_marks_eq p z hxp hxz

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingDiskNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem assembled_range_in_crossingDisk (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Set.range (E.assembledEdge v p.1) ↔ x ∈ Set.range (C.crossingChord p) := by
  constructor
  · intro he
    rcases (E.assembledEdge_range_iff v p.1 x).mp he with (he | ⟨i,hi,he⟩ | ⟨q,hq,he⟩) | he
    · exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
        hx (C.vertex_spoke_range_in_disk v hv _ (C.startPortAt p.1) he))
    · obtain ⟨t,rfl⟩ := he
      exact False.elim (hx.not_ge (E.outside_open_disks i t (C.innerMark p)))
    · have hm : C.innerMark q=C.innerMark p := by
        by_contra hn
        exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
          (C.crossingChord_range_subset_disk q he) (C.crossingDisk_subset_closed p hx)
      have hqp := C.innerIndex_eq_of_edge_mark q p hq hm
      exact hqp ▸ he
    · rw [endSpoke_range] at he
      exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
        hx (C.vertex_spoke_range_in_disk v hv _ (C.endPortAt p.1) he))
  · intro he
    apply (E.assembledEdge_range_iff v p.1 x).mpr
    exact Or.inl (Or.inr (Or.inr ⟨p,rfl,he⟩))

theorem assembled_trace_in_crossingDisk (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ edgeInterior (E.assembledDrawing v hvinj hv) p.1 ↔
      x ∈ openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) := by
  have havoid : ∀ j, x ≠ v j := by
    intro j he
    exact Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p j) hx (he.symm ▸ (hv j).le)
  rw [← C.crossingChord_openTrace_iff p x hx,← E.assembled_range_in_crossingDisk v hv p x hx]
  constructor
  · rintro ⟨t,ht,he⟩
    exact ⟨t,he⟩
  · rintro ⟨t,he⟩
    have ht0 : t ≠ 0 := by
      intro ht
      subst t
      rw [Path.source] at he
      exact havoid _ he.symm
    have ht1 : t ≠ 1 := by
      intro ht
      subst t
      rw [Path.target] at he
      exact havoid _ he.symm
    exact ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,he⟩

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AssembledAdmissibleDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem assembled_crossings_proper (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : BipartiteEdge m n) (hef : e ≠ f) (x : Plane)
    (hx : x ∈ edgeInterior (E.assembledDrawing v hvinj hv) e)
    (hy : x ∈ edgeInterior (E.assembledDrawing v hvinj hv) f) :
    ProperCrossing (edgeInterior (E.assembledDrawing v hvinj hv) e)
      (edgeInterior (E.assembledDrawing v hvinj hv) f) x := by
  obtain ⟨s,hs,he⟩ := hx
  obtain ⟨t,ht,hf⟩ := hy
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)) ⟨s,he⟩ ⟨t,hf⟩
  have hpq : p ≠ q := fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨hxin,hproper⟩ := C.crossingChord_meeting_proper p q hpq x hxp hxq
  apply properCrossing_of_local_eq _ _ _ _ x hproper (C.crossingDisk p) (C.crossingDisk_isOpen p) hxin
  · intro z hz
    simpa only [hp] using (E.assembled_trace_in_crossingDisk v hvinj hv p z hz).symm
  · intro z hz
    have hzq : z ∈ C.crossingDisk q := by
      change squaredLength (z-(C.innerMark q).val) < C.radius^2
      rw [← hm]
      exact hz
    simpa only [hq] using (E.assembled_trace_in_crossingDisk v hvinj hv q z hzq).symm

def assembledAdmissible (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) : AdmissibleDrawing m n where
  toContinuousDrawing := E.assembledDrawing v hvinj hv
  crossings_finite := E.assembled_crossings_finite v hvinj hv hdet
  crossings_proper := E.assembled_crossings_proper v hvinj hv hdet
  no_triples := E.assembled_no_triples v hvinj hv hdet

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingWalkCutTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem graphWalkPath_range_cases {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) (x : Plane) (hx : x ∈ Set.range (graphWalkPath pos p)) :
    x=pos a ∨ ∃ i, i < p.length ∧ x ∈ segment ℝ (pos (p.getVert i)) (pos (p.getVert (i+1))) := by
  by_cases hp : p.length=0
  · change x ∈ Set.range (polygonalArcPath (fun i => pos (p.getVert i)) p.length) at hx
    rw [hp] at hx
    obtain ⟨t,ht⟩ := hx
    exact Or.inl (by simpa [polygonalArcPath,p.getVert_zero] using ht.symm)
  · exact Or.inr (polygonalArcPath_range_piece _ _ (by omega) x hx)

variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem drawingEdgeWalk_take_trace (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) (k : Fin ((P e).pieces+1)) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P e).take k.val)) ⊆
      D.edge e '' Set.Icc (0 : unitInterval) ((P e).knot k) := by
  intro x hx
  rcases graphWalkPath_range_cases id ((drawingEdgeWalk P e).take k.val) x hx with he | ⟨i,hi,hxi⟩
  · exact ⟨0,⟨le_rfl,((P e).knot k).property.1⟩,(D.edge e).source.trans he.symm⟩
  · have hil : i < (P e).pieces := by
      rw [SimpleGraph.Walk.take_length,drawingEdgeWalk_length] at hi
      omega
    have hik : i+1 ≤ k.val := by
      rw [SimpleGraph.Walk.take_length,drawingEdgeWalk_length] at hi
      omega
    simp only [id_eq,SimpleGraph.Walk.take_getVert] at hxi
    rw [show min k.val i=i by omega,show min k.val (i+1)=i+1 by omega,
      drawingEdgeWalk_getVert P e i (by omega),drawingEdgeWalk_getVert P e (i+1) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨i,hil⟩
    have h0 : (P e).vertices i=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
    rw [h0,h1] at hxi
    obtain ⟨t,ht⟩ := (P e).pieceTrace_parameter j x hxi
    have hbetween := intervalSegment_between ((P e).knot j.castSucc) ((P e).knot j.succ) t
      ((P e).increasing.monotone (by change i ≤ i+1; omega))
    exact ⟨intervalSegment ((P e).knot j.castSucc) ((P e).knot j.succ) t,
      ⟨(intervalSegment _ _ t).property.1,hbetween.2.trans ((P e).increasing.monotone hik)⟩,ht⟩

theorem drawingEdgeWalk_drop_trace (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) (k : Fin ((P e).pieces+1)) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P e).drop k.val)) ⊆
      D.edge e '' Set.Icc ((P e).knot k) (1 : unitInterval) := by
  intro x hx
  rcases graphWalkPath_range_cases id ((drawingEdgeWalk P e).drop k.val) x hx with he | ⟨i,hi,hxi⟩
  · refine ⟨(P e).knot k,⟨le_rfl,((P e).knot k).property.2⟩,?_⟩
    have hh : (drawingEdgeWalk P e).getVert k.val=D.edge e ((P e).knot k) :=
      (drawingEdgeWalk_getVert P e k.val (by omega)).trans ((P e).vertices_at k)
    exact hh.symm.trans he.symm
  · have hil : k.val+i < (P e).pieces := by
      rw [SimpleGraph.Walk.drop_length,drawingEdgeWalk_length] at hi
      omega
    simp only [id_eq,SimpleGraph.Walk.drop_getVert] at hxi
    rw [drawingEdgeWalk_getVert P e (k.val+i) (by omega),
      drawingEdgeWalk_getVert P e (k.val+(i+1)) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨k.val+i,hil⟩
    have h0 : (P e).vertices (k.val+i)=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (k.val+(i+1))=D.edge e ((P e).knot j.succ) := by
      have hh : (P e).vertices (k.val+i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
      simpa only [Nat.add_assoc] using hh
    rw [h0,h1] at hxi
    obtain ⟨t,ht⟩ := (P e).pieceTrace_parameter j x hxi
    have hbetween := intervalSegment_between ((P e).knot j.castSucc) ((P e).knot j.succ) t
      ((P e).increasing.monotone (by change k.val+i ≤ k.val+i+1; omega))
    refine ⟨intervalSegment ((P e).knot j.castSucc) ((P e).knot j.succ) t,⟨?_,?_⟩,ht⟩
    · exact ((P e).increasing.monotone (show k ≤ j.castSucc by change k.val ≤ k.val+i; omega)).trans hbetween.1
    · exact (intervalSegment _ _ t).property.2

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ExteriorSegmentGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def exteriorSegmentGraph (G : SimpleGraph Plane) (U : Set Plane) : SimpleGraph Plane where
  Adj := fun a b => G.Adj a b ∧ Disjoint (segment ℝ a b) U
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,by simpa only [segment_symm] using h.2⟩⟩
  loopless := ⟨by intro a h; exact G.loopless.irrefl a h.1⟩

theorem graphWalkPath_edge_subset_range {G : SimpleGraph Plane} {a b : Plane}
    (p : G.Walk a b) (u v : Plane) (huv : s(u,v) ∈ p.edges) :
    segment ℝ u v ⊆ Set.range (graphWalkPath id p) := by
  obtain ⟨i,hi,he⟩ := (p.mk_mem_edges_iff_exists).mp huv
  have hpiece := polygonalArcPath_piece_subset_range (fun i => p.getVert i) p.length i hi
  change segment ℝ u v ⊆ Set.range (polygonalArcPath (fun i => p.getVert i) p.length)
  rcases Sym2.eq_iff.mp he with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simpa only [h0,h1] using hpiece
  · simpa only [h0,h1,segment_symm] using hpiece

def exteriorGraphWalk {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) :
    (exteriorSegmentGraph G U).Walk a b :=
  p.transfer (exteriorSegmentGraph G U) (by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro huv
      exact ⟨p.adj_of_mem_edges huv,h.mono_left (graphWalkPath_edge_subset_range p u v huv)⟩)

theorem exteriorGraphWalk_getVert {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) (i : ℕ) :
    (exteriorGraphWalk p U h).getVert i=p.getVert i := by
  have hlen : (exteriorGraphWalk p U h).length=p.length := by
    simp only [exteriorGraphWalk,SimpleGraph.Walk.length_transfer]
  have hsupport : (exteriorGraphWalk p U h).support=p.support := by
    simp only [exteriorGraphWalk,SimpleGraph.Walk.support_transfer]
  by_cases hi : i ≤ p.length
  · have hi' : i ≤ (exteriorGraphWalk p U h).length := by rw [hlen]; exact hi
    rw [SimpleGraph.Walk.getVert_eq_support_getElem _ hi',p.getVert_eq_support_getElem hi]
    simp only [hsupport]
  · rw [SimpleGraph.Walk.getVert_of_length_le _ (by
      rw [hlen]
      omega),p.getVert_of_length_le (by omega)]

theorem exteriorGraphWalk_length {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) :
    (exteriorGraphWalk p U h).length=p.length := by
  simp only [exteriorGraphWalk,SimpleGraph.Walk.length_transfer]

theorem exteriorGraphWalk_trace {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) :
    Set.range (graphWalkPath id (exteriorGraphWalk p U h))=Set.range (graphWalkPath id p) := by
  change Set.range (polygonalArcPath (fun i => (exteriorGraphWalk p U h).getVert i)
    (exteriorGraphWalk p U h).length)=Set.range (polygonalArcPath (fun i => p.getVert i) p.length)
  have hf : (fun i => (exteriorGraphWalk p U h).getVert i)=(fun i => p.getVert i) :=
    funext (exteriorGraphWalk_getVert p U h)
  exact congrArg₂ (fun (seq : ℕ → Plane) (k : ℕ) =>
    Set.range (fun t : unitInterval => polygonalArcPath seq k t)) hf (exteriorGraphWalk_length p U h)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingReconnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem crossing_reconnections_disjoint (a b c d : Plane) (h : SegmentsCrossProperly a b c d) :
    Disjoint (segment ℝ c b) (segment ℝ a d) := by
  obtain ⟨hd,s,hs,t,ht,hst⟩ := h
  let o := segmentPoint a b s
  let F := crossingCoordinates o (b-a) (d-c)
  have hFa : F a=(-s,0) := by
    have he := crossingCoordinates_first_segment a b c d o s 0 hd rfl
    simpa only [segmentPoint_zero,zero_sub] using he
  have hFb : F b=(1-s,0) := by
    have he := crossingCoordinates_first_segment a b c d o s 1 hd rfl
    simpa only [segmentPoint_one] using he
  have hFc : F c=(0,-t) := by
    have he := crossingCoordinates_second_segment a b c d o t 0 hd hst
    simpa only [segmentPoint_zero,zero_sub] using he
  have hFd : F d=(0,1-t) := by
    have he := crossingCoordinates_second_segment a b c d o t 1 hd hst
    simpa only [segmentPoint_one] using he
  apply Set.disjoint_left.mpr
  intro x hleft hright
  rw [← Path.range_segment] at hleft hright
  obtain ⟨u,hu⟩ := hleft
  obtain ⟨v,hv⟩ := hright
  have hu' : segmentPoint c b u.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hu
  have hv' : segmentPoint a d v.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hv
  have hleftF : F x=segmentPoint (0,-t) (1-s,0) u.val := by
    rw [← hu']
    exact (crossingCoordinates_affine o (b-a) (d-c) c b u.val).trans (by
      change segmentPoint (F c) (F b) u.val=_
      rw [hFc,hFb])
  have hrightF : F x=segmentPoint (-s,0) (0,1-t) v.val := by
    rw [← hv']
    exact (crossingCoordinates_affine o (b-a) (d-c) a d v.val).trans (by
      change segmentPoint (F a) (F d) v.val=_
      rw [hFa,hFd])
  have hl : 0 < (F x).1-(F x).2 := by
    rw [hleftF]
    have hh := convex_combination_pos t (1-s) u.val ht.1 (sub_pos.mpr hs.2) u.property
    dsimp [segmentPoint]
    nlinarith
  have hr : (F x).1-(F x).2 < 0 := by
    rw [hrightF]
    have hh := convex_combination_pos s (1-t) v.val hs.1 (sub_pos.mpr ht.2) v.property
    dsimp [segmentPoint]
    nlinarith
  exact hl.not_ge hr.le

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectionChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem reconnection_chords_disjoint (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) :
    ∀ i j : Bool, i ≠ j → Disjoint
      (segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i))
      (segment ℝ (C.reconnectionStart p q j) (C.reconnectionEnd p q j)) := by
  have hh := crossing_reconnections_disjoint _ _ _ _ hcross
  intro i j hij
  cases i <;> cases j
  · exact False.elim (hij rfl)
  · exact hh
  · exact hh.symm
  · exact False.elim (hij rfl)

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segment_endpoint_or_open (a b x : Plane) (hx : x ∈ segment ℝ a b) :
    x=a ∨ x=b ∨ x ∈ openSegmentTrace a b := by
  rw [← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  by_cases ht0 : t=0
  · subst t
    exact Or.inl (by simpa only [Path.source] using ht.symm)
  by_cases ht1 : t=1
  · subst t
    exact Or.inr (Or.inl (by simpa only [Path.target] using ht.symm))
  refine Or.inr (Or.inr ⟨t.val,⟨?_,?_⟩,?_⟩)
  · exact lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
  · exact lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
  · simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht

def segmentAugmentedGraph {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) : SimpleGraph Plane where
  Adj := fun x y => G.Adj x y ∨ ∃ i, (x=a i ∧ y=b i) ∨ (x=b i ∧ y=a i)
  symm := ⟨by
    rintro x y (hxy | ⟨i,⟨hx,hy⟩ | ⟨hx,hy⟩⟩)
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨i,Or.inr ⟨hy,hx⟩⟩
    · exact Or.inr ⟨i,Or.inl ⟨hy,hx⟩⟩⟩
  loopless := ⟨by
    rintro x (hxx | ⟨i,⟨hx,hy⟩ | ⟨hx,hy⟩⟩)
    · exact G.loopless.irrefl x hxx
    · exact hne i (hx.symm.trans hy)
    · exact hne i (hy.symm.trans hx)⟩

theorem le_segmentAugmentedGraph {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) : G ≤ segmentAugmentedGraph G a b hne := fun _ _ h => Or.inl h

theorem segmentAugmentedGraph_added_adj {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) (i : ι) : (segmentAugmentedGraph G a b hne).Adj (a i) (b i) :=
  Or.inr ⟨i,Or.inl ⟨rfl,rfl⟩⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingSurgeryGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

def crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) : SimpleGraph Plane :=
  segmentAugmentedGraph (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p))
    (C.reconnectionStart p q) (C.reconnectionEnd p q) (C.reconnection_endpoints_ne p q)

theorem exterior_le_crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) :
    exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p) ≤ crossingSurgeryGraph C P p q :=
  le_segmentAugmentedGraph _ _ _ _

theorem crossingSurgeryGraph_reconnection_adj (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) (i : Bool) :
    (crossingSurgeryGraph C P p q).Adj (C.reconnectionStart p q i) (C.reconnectionEnd p q i) :=
  segmentAugmentedGraph_added_adj _ _ _ _ i

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GraphWalkRealizationLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem graphWalkPath_range_iff {G : SimpleGraph Plane} {a b : Plane}
    (p : G.Walk a b) (x : Plane) :
    x ∈ Set.range (graphWalkPath id p) ↔
      x=a ∨ ∃ u v, s(u,v) ∈ p.edges ∧ x ∈ segment ℝ u v := by
  constructor
  · intro hx
    rcases graphWalkPath_range_cases id p x hx with h | ⟨i,hi,hx⟩
    · exact Or.inl h
    · refine Or.inr ⟨p.getVert i,p.getVert (i+1),?_,hx⟩
      exact (p.mk_mem_edges_iff_exists).mpr ⟨i,hi,rfl⟩
  · rintro (rfl | ⟨u,v,h,hx⟩)
    · exact ⟨0,(graphWalkPath id p).source⟩
    · exact graphWalkPath_edge_subset_range p u v h hx

theorem graphWalkPath_copy_range {G : SimpleGraph Plane} {a b a' b' : Plane}
    (p : G.Walk a b) (ha : a=a') (hb : b=b') :
    Set.range (graphWalkPath id (p.copy ha hb))=Set.range (graphWalkPath id p) := by
  subst a'
  subst b'
  rfl

theorem graphWalkPath_mapLe_range {G H : SimpleGraph Plane} (hle : G ≤ H)
    {a b : Plane} (p : G.Walk a b) :
    Set.range (graphWalkPath id (p.mapLe hle))=Set.range (graphWalkPath id p) := by
  ext x
  simp only [graphWalkPath_range_iff,SimpleGraph.Walk.edges_mapLe_eq_edges]

theorem graphWalkPath_append_range {G : SimpleGraph Plane} {a b c : Plane}
    (p : G.Walk a b) (q : G.Walk b c) :
    Set.range (graphWalkPath id (p.append q))=
      Set.range (graphWalkPath id p) ∪ Set.range (graphWalkPath id q) := by
  ext x
  simp only [Set.mem_union,graphWalkPath_range_iff,SimpleGraph.Walk.edges_append,List.mem_append]
  constructor
  · rintro (hx | ⟨u,v,h,hx⟩)
    · exact Or.inl (Or.inl hx)
    · rcases h with h | h
      · exact Or.inl (Or.inr ⟨u,v,h,hx⟩)
      · exact Or.inr (Or.inr ⟨u,v,h,hx⟩)
  · rintro ((hx | ⟨u,v,h,hx⟩) | (hx | ⟨u,v,h,hx⟩))
    · exact Or.inl hx
    · exact Or.inr ⟨u,v,Or.inl h,hx⟩
    · have hb : x ∈ Set.range (graphWalkPath id p) := ⟨1,(graphWalkPath id p).target.trans hx.symm⟩
      rcases (graphWalkPath_range_iff p x).mp hb with h | ⟨u,v,h,hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨u,v,Or.inl h,hx⟩
    · exact Or.inr ⟨u,v,Or.inr h,hx⟩

theorem graphWalkPath_toWalk_range {G : SimpleGraph Plane} {a b : Plane} (h : G.Adj a b) :
    Set.range (graphWalkPath id h.toWalk)=segment ℝ a b := by
  change Set.range (Path.segment a b)=segment ℝ a b
  exact Path.range_segment a b

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SurgeryCutWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

def surgeryPrefixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (i : ℕ) (hi : (drawingEdgeWalk P r.1).getVert i=C.portPoint (C.incomingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex (.inl r.1.1)) (C.portPoint (C.incomingPort r)) :=
  ((exteriorGraphWalk ((drawingEdgeWalk P r.1).take i) (C.crossingDisk p) hout).mapLe
    (exterior_le_crossingSurgeryGraph C P p q)).copy rfl hi

def surgerySuffixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (j : ℕ) (hj : (drawingEdgeWalk P r.1).getVert j=C.portPoint (C.outgoingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex (.inr r.1.2)) :=
  ((exteriorGraphWalk ((drawingEdgeWalk P r.1).drop j) (C.crossingDisk p) hout).mapLe
    (exterior_le_crossingSurgeryGraph C P p q)).copy hj rfl

theorem surgeryPrefixWalk_trace (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (i : ℕ) (hi : (drawingEdgeWalk P r.1).getVert i=C.portPoint (C.incomingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i))) (C.crossingDisk p)) :
    Set.range (graphWalkPath id (surgeryPrefixWalk C P p q r i hi hout))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i)) := by
  rw [surgeryPrefixWalk,graphWalkPath_copy_range,graphWalkPath_mapLe_range,exteriorGraphWalk_trace]

theorem surgerySuffixWalk_trace (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (j : ℕ) (hj : (drawingEdgeWalk P r.1).getVert j=C.portPoint (C.outgoingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j))) (C.crossingDisk p)) :
    Set.range (graphWalkPath id (surgerySuffixWalk C P p q r j hj hout))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j)) := by
  rw [surgerySuffixWalk,graphWalkPath_copy_range,graphWalkPath_mapLe_range,exteriorGraphWalk_trace]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ExteriorCrossingCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

structure ExteriorCrossingCut (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (r : C.InnerIndex) where
  first : Fin ((P r.1).pieces+1)
  last : Fin ((P r.1).pieces+1)
  ordered : first < last
  first_point : (drawingEdgeWalk P r.1).getVert first.val=C.portPoint (C.incomingPort r)
  last_point : (drawingEdgeWalk P r.1).getVert last.val=C.portPoint (C.outgoingPort r)
  prefix_outside : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take first.val))) (C.crossingDisk r)
  suffix_outside : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop last.val))) (C.crossingDisk r)

namespace ExteriorCrossingCut
variable {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q r : C.InnerIndex}

def prefixInSurgery (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex (.inl r.1.1)) (C.portPoint (C.incomingPort r)) :=
  surgeryPrefixWalk C P p q r K.first.val K.first_point (by
    simpa only [DrawingPassages.crossingDisk,hr] using K.prefix_outside)

def suffixInSurgery (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex (.inr r.1.2)) :=
  surgerySuffixWalk C P p q r K.last.val K.last_point (by
    simpa only [DrawingPassages.crossingDisk,hr] using K.suffix_outside)

theorem prefixInSurgery_trace (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    Set.range (graphWalkPath id (K.prefixInSurgery p q hr))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) :=
  surgeryPrefixWalk_trace _ _ _ _ _ _ _ _

theorem suffixInSurgery_trace (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    Set.range (graphWalkPath id (K.suffixInSurgery p q hr))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) :=
  surgerySuffixWalk_trace _ _ _ _ _ _ _ _

end ExteriorCrossingCut
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SurgeryPathWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def walkThroughChord {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) : G.Walk a b :=
  (A.append h.toWalk).append B

theorem walkThroughChord_range {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) :
    Set.range (graphWalkPath id (walkThroughChord A h B))=
      (Set.range (graphWalkPath id A) ∪ segment ℝ u v) ∪ Set.range (graphWalkPath id B) := by
  rw [walkThroughChord,graphWalkPath_append_range,graphWalkPath_append_range,graphWalkPath_toWalk_range]

variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

theorem surgery_mixed_endpoints_ne (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (p q : C.InnerIndex) : D'.vertex (.inl p.1.1) ≠ D'.vertex (.inr q.1.2) := by
  intro h
  cases D'.vertex_injective h

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectedWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem surgery_forward_adj : (crossingSurgeryGraph C P p q).Adj
    (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)) :=
  crossingSurgeryGraph_reconnection_adj C P p q true

theorem surgery_backward_adj : (crossingSurgeryGraph C P p q).Adj
    (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)) :=
  crossingSurgeryGraph_reconnection_adj C P p q false

def reconnectedForwardWalk (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex (.inl p.1.1)) (D'.vertex (.inr q.1.2)) :=
  walkThroughChord (Kp.prefixInSurgery p q rfl)
    surgery_forward_adj (Kq.suffixInSurgery p q hm.symm)

def reconnectedBackwardWalk (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex (.inl q.1.1)) (D'.vertex (.inr p.1.2)) :=
  walkThroughChord (Kq.prefixInSurgery p q hm.symm)
    surgery_backward_adj (Kp.suffixInSurgery p q rfl)

theorem reconnectedForwardWalk_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (graphWalkPath id (reconnectedForwardWalk Kp Kq hm))=
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val)) := by
  rw [reconnectedForwardWalk,walkThroughChord_range,
    ExteriorCrossingCut.prefixInSurgery_trace,ExteriorCrossingCut.suffixInSurgery_trace]

theorem reconnectedBackwardWalk_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (graphWalkPath id (reconnectedBackwardWalk Kp Kq hm))=
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) := by
  rw [reconnectedBackwardWalk,walkThroughChord_range,
    ExteriorCrossingCut.prefixInSurgery_trace,ExteriorCrossingCut.suffixInSurgery_trace]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectedPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def reconnectedForwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex (.inl p.1.1)) (D'.vertex (.inr q.1.2)) := by
  classical
  exact graphWalkPath id (reconnectedForwardWalk Kp Kq hm).bypass

def reconnectedBackwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex (.inl q.1.1)) (D'.vertex (.inr p.1.2)) := by
  classical
  exact graphWalkPath id (reconnectedBackwardWalk Kp Kq hm).bypass

theorem reconnectedForwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedForwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C p q)
    _ (reconnectedForwardWalk Kp Kq hm).bypass_isPath

theorem reconnectedBackwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedBackwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C q p)
    _ (reconnectedBackwardWalk Kp Kq hm).bypass_isPath

theorem reconnectedForwardPath_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (reconnectedForwardPath Kp Kq hm) ⊆
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val)) := by
  classical
  exact (graphWalkPath_bypass_range_subset id (reconnectedForwardWalk Kp Kq hm)).trans
    (by rw [reconnectedForwardWalk_trace])

theorem reconnectedBackwardPath_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (reconnectedBackwardPath Kp Kq hm) ⊆
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) := by
  classical
  exact (graphWalkPath_bypass_range_subset id (reconnectedBackwardWalk Kp Kq hm)).trans
    (by rw [reconnectedBackwardWalk_trace])

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectedPointRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem reconnected_paths_avoid_crossing (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∉ Set.range (reconnectedForwardPath Kp Kq hm) ∧
      x ∉ Set.range (reconnectedBackwardPath Kp Kq hm) := by
  obtain ⟨hxin,havoid⟩ := C.reconnection_avoids_chord_meeting p q hpq x hxp hxq
  have hxinq : x ∈ C.crossingDisk q := by
    simpa only [DrawingPassages.crossingDisk,hm] using hxin
  constructor
  · intro hx
    rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
    · exact Set.disjoint_left.mp Kp.prefix_outside hx hxin
    · exact havoid true hx
    · exact Set.disjoint_left.mp Kq.suffix_outside hx hxinq
  · intro hx
    rcases reconnectedBackwardPath_trace Kp Kq hm hx with (hx | hx) | hx
    · exact Set.disjoint_left.mp Kq.prefix_outside hx hxinq
    · exact havoid false hx
    · exact Set.disjoint_left.mp Kp.suffix_outside hx hxin

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CutVertexAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

theorem drawing_edge_vertex_parameter (D : ContinuousDrawing m n) (e : BipartiteEdge m n)
    (t : unitInterval) (v : BipartiteVertex m n) (he : D.edge e t=D.vertex v) :
    (t=0 ∧ v=.inl e.1) ∨ (t=1 ∧ v=.inr e.2) := by
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨rfl,(D.vertex_injective ((D.edge e).source.symm.trans he)).symm⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inr ⟨rfl,(D.vertex_injective ((D.edge e).target.symm.trans he)).symm⟩
  exact False.elim (D.interior_avoids_vertices e t
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩ v he)

namespace ExteriorCrossingCut
variable {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {r : C.InnerIndex}

theorem first_parameter_lt_one (K : ExteriorCrossingCut C P r) : (P r.1).knot K.first < 1 := by
  rw [← (P r.1).last]
  exact (P r.1).increasing (K.ordered.trans_le (Fin.le_last _))

theorem last_parameter_pos (K : ExteriorCrossingCut C P r) : 0 < (P r.1).knot K.last := by
  rw [← (P r.1).first]
  exact (P r.1).increasing ((Fin.zero_le K.first).trans_lt K.ordered)

theorem prefix_vertex_eq (K : ExteriorCrossingCut C P r) (v : BipartiteVertex m n)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val))) :
    v=.inl r.1.1 := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨_,hv⟩ | ⟨ht1,_⟩
  · exact hv
  · exact False.elim ((ht1 ▸ ht.2).not_gt K.first_parameter_lt_one)

theorem suffix_vertex_eq (K : ExteriorCrossingCut C P r) (v : BipartiteVertex m n)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val))) :
    v=.inr r.1.2 := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨ht0,_⟩ | ⟨_,hv⟩
  · exact False.elim ((ht0 ▸ ht.1).not_gt K.last_parameter_pos)
  · exact hv

end ExteriorCrossingCut
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectedVertexAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem path_interior_avoids_vertices_of_range {V : Type*} (vertex : V → Plane) (a b : V)
    (γ : Path (vertex a) (vertex b)) (hinj : Function.Injective γ)
    (hrange : ∀ v, vertex v ∈ Set.range γ → v=a ∨ v=b)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (v : V) : γ t ≠ vertex v := by
  intro he
  rcases hrange v ⟨t,he⟩ with rfl | rfl
  · exact ht.1.ne (hinj (he.trans γ.source.symm)).symm
  · exact ht.2.ne (hinj (he.trans γ.target.symm))

theorem reconnectedForwardPath_vertex_eq (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (j : BipartiteVertex m n) (hj : D'.vertex j ∈ Set.range (reconnectedForwardPath Kp Kq hm)) :
    j=.inl p.1.1 ∨ j=.inr q.1.2 := by
  rcases reconnectedForwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kp.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv true j hj)
  · exact Or.inr (Kq.suffix_vertex_eq j hj)

theorem reconnectedBackwardPath_vertex_eq (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (j : BipartiteVertex m n) (hj : D'.vertex j ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    j=.inl q.1.1 ∨ j=.inr p.1.2 := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kq.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv false j hj)
  · exact Or.inr (Kp.suffix_vertex_eq j hj)

theorem reconnectedForwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : BipartiteVertex m n) :
    reconnectedForwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedForwardPath_injective Kp Kq hm hemb)
    (reconnectedForwardPath_vertex_eq Kp Kq hm hv) t ht j

theorem reconnectedBackwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : BipartiteVertex m n) :
    reconnectedBackwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedBackwardPath_injective Kp Kq hm hemb)
    (reconnectedBackwardPath_vertex_eq Kp Kq hm hv) t ht j

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AdjacentSurgeryRoutes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def adjacentSurgeryRouteP (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2) :
    Path (D'.vertex (.inl p.1.1)) (D'.vertex (.inr p.1.2)) := by
  classical
  exact if h : p.1.1=q.1.1 then (reconnectedBackwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (.inl i)) h) rfl
  else (reconnectedForwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (.inr j)) (hadj.resolve_left h))

def adjacentSurgeryRouteQ (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2) :
    Path (D'.vertex (.inl q.1.1)) (D'.vertex (.inr q.1.2)) := by
  classical
  exact if h : p.1.1=q.1.1 then (reconnectedForwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (.inl i)) h.symm) rfl
  else (reconnectedBackwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (.inr j)) (hadj.resolve_left h).symm)

theorem adjacentSurgeryRouteP_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteP Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_injective Kp Kq hm hemb
  · exact reconnectedForwardPath_injective Kp Kq hm hemb

theorem adjacentSurgeryRouteQ_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_injective Kp Kq hm hemb
  · exact reconnectedBackwardPath_injective Kp Kq hm hemb

theorem adjacentSurgeryRouteP_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : BipartiteVertex m n) :
    adjacentSurgeryRouteP Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hemb t ht j
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hemb t ht j

theorem adjacentSurgeryRouteQ_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : BipartiteVertex m n) :
    adjacentSurgeryRouteQ Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hemb t ht j
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hemb t ht j

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AdjacentSurgeryDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def adjacentSurgeryDrawing (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) : ContinuousDrawing m n :=
  D'.toContinuousDrawing.replaceTwoEdges p.1 q.1
    (adjacentSurgeryRouteP Kp Kq hm hadj) (adjacentSurgeryRouteQ Kp Kq hm hadj)
    (adjacentSurgeryRouteP_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteQ_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteP_avoids_vertices Kp Kq hm hadj hv hemb)
    (adjacentSurgeryRouteQ_avoids_vertices Kp Kq hm hadj hv hemb)

theorem adjacentSurgeryDrawing_first (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge p.1=adjacentSurgeryRouteP Kp Kq hm hadj :=
  ContinuousDrawing.replaceTwoRoutes_first _ _ _ _ _

theorem adjacentSurgeryDrawing_second (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge q.1=adjacentSurgeryRouteQ Kp Kq hm hadj :=
  ContinuousDrawing.replaceTwoRoutes_second _ _ _ (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) _ _

theorem adjacentSurgeryDrawing_other (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e=D'.edge e :=
  ContinuousDrawing.replaceTwoRoutes_other _ _ _ _ _ _ hep heq

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AdjacentSurgeryPointRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem adjacentSurgeryRoutes_avoid_crossing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∉ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∧
      x ∉ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  have ha := reconnected_paths_avoid_crossing Kp Kq hm hpq x hxp hxq
  constructor
  · unfold adjacentSurgeryRouteP
    split
    · exact ha.2
    · exact ha.1
  · unfold adjacentSurgeryRouteQ
    split
    · exact ha.1
    · exact ha.2

theorem adjacentSurgeryDrawing_avoids_crossing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q))
    (hother : ∀ e, e ≠ p.1 → e ≠ q.1 → x ∉ Set.range (D'.edge e)) :
    ∀ e, x ∉ Set.range ((adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e) := by
  have ha := adjacentSurgeryRoutes_avoid_crossing Kp Kq hm hpq hadj x hxp hxq
  intro e
  classical
  by_cases hep : e=p.1
  · subst e
    rw [adjacentSurgeryDrawing_first]
    exact ha.1
  by_cases heq : e=q.1
  · subst e
    rw [adjacentSurgeryDrawing_second Kp Kq hm hpq]
    exact ha.2
  · rw [adjacentSurgeryDrawing_other Kp Kq hm hadj hv hemb e hep heq]
    exact hother e hep heq

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleEntryExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

def triangleStart (a b c : Plane) : Fin 3 → Plane := ![a,b,c]
def triangleEnd (a b c : Plane) : Fin 3 → Plane := ![b,c,a]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def TriangleSegmentPosition (a b c d e : Plane) : Prop :=
  (∀ i : Fin 3, det2 (triangleEnd a b c i-triangleStart a b c i) (e-d) ≠ 0) ∧
  (∀ i : Fin 3, orient2 d e (triangleStart a b c i) ≠ 0) ∧
  (∀ i : Fin 3, orient2 (triangleStart a b c i) (triangleEnd a b c i) d ≠ 0 ∧
    orient2 (triangleStart a b c i) (triangleEnd a b c i) e ≠ 0)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_GenericPolygonIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def PolygonLinePosition (v w : ℕ → Plane) (n m : ℕ) : Prop :=
  (∀ i : Fin n, ∀ j : Fin m, det2 (v (i.val+1)-v i.val) (w (j.val+1)-w j.val) ≠ 0) ∧
  (∀ i : Fin (n+1), ∀ j : Fin m, orient2 (w j.val) (w (j.val+1)) (v i.val) ≠ 0) ∧
  (∀ i : Fin n, ∀ j : Fin (m+1), orient2 (v i.val) (v (i.val+1)) (w j.val) ≠ 0)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChainComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b c : Plane}

def reverse (P : PolygonalChain O a b) : PolygonalChain O b a where
  pieces := P.pieces
  vertices := reversedSequence P.vertices P.pieces
  first := by simpa only [reversedSequence,Nat.sub_zero] using P.last
  last := by simpa only [reversedSequence,Nat.sub_self] using P.first
  start_mem := P.path_range_subset ⟨1,P.path.target⟩
  inside := by
    intro i hi
    have h₀ : P.pieces-i=P.pieces-1-i+1 := by omega
    have h₁ : P.pieces-(i+1)=P.pieces-1-i := by omega
    simp only [reversedSequence,h₀,h₁]
    rw [segment_symm]
    exact P.inside (P.pieces-1-i) (by omega)

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChainTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O T : Set Plane} {a b c d e : Plane}

def Transverse (P : PolygonalChain O a b) (Q : PolygonalChain T d e) : Prop :=
  ∀ i : Fin P.pieces, ∀ j : Fin Q.pieces,
    SegmentPairTransverse (P.vertices i.val) (P.vertices (i.val+1))
      (Q.vertices j.val) (Q.vertices (j.val+1))

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FinitePolygonalComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def finitePolygonalChain (O : Set Plane) (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) : (n : ℕ) → PolygonalChain O (v 0) (v n)
  | 0 => PolygonalChain.point O (v 0) h0
  | n+1 => (finitePolygonalChain O v h0 P n).join (P n)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleConnectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def circleTangentOffset (u : Plane) (δ : ℝ) : Plane := u+δ • rotateQuarter u

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReducedPolygonalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def PolygonalParametrization.containedChain {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : PolygonalChain (Set.range γ) a b where
  pieces := P.pieces
  vertices := P.vertices
  first := P.vertices_first
  last := P.vertices_last
  start_mem := ⟨0,γ.source⟩
  inside := by
    intro i hi
    let j : Fin P.pieces := ⟨i,hi⟩
    have h0 : P.vertices i=γ (P.knot j.castSucc) := P.vertices_at j.castSucc
    have h1 : P.vertices (i+1)=γ (P.knot j.succ) := P.vertices_at j.succ
    rw [h0,h1]
    exact P.pieceTrace_subset_range j

theorem PolygonalChain.pieces_pos_of_ne {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (hab : a ≠ b) : 0 < P.pieces := by
  by_contra hh
  have hz : P.pieces=0 := by omega
  exact hab (P.first.symm.trans (hz ▸ P.last))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ChainTracePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem drawing_chain_pieces_pos {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2))) :
    0 < P.pieces := by
  apply P.pieces_pos_of_ne
  intro h
  cases D.vertex_injective h

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RadialBoundaryPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def radialPort (a b : Plane) (r : ℝ) : Plane :=
  a+(r/Real.sqrt (squaredLength (b-a))) • (b-a)

theorem radialPort_parameter (a b : Plane) (r : ℝ) :
    radialPort a b r=segmentPoint a b (r/Real.sqrt (squaredLength (b-a))) := by
  apply Prod.ext <;> dsimp [radialPort,segmentPoint] <;> ring

theorem radialPort_parameter_between (a b : Plane) (r : ℝ) (hr : 0 < r)
    (hshort : r^2 < squaredLength (b-a)) :
    r/Real.sqrt (squaredLength (b-a)) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hL : 0 < squaredLength (b-a) := (sq_nonneg r).trans_lt hshort
  have hs := Real.sqrt_pos.mpr hL
  have hs2 := Real.sq_sqrt hL.le
  exact ⟨div_pos hr hs,(div_lt_one hs).mpr (by nlinarith)⟩

theorem radialPort_mem_openSegment (a b : Plane) (r : ℝ) (hr : 0 < r)
    (hshort : r^2 < squaredLength (b-a)) : radialPort a b r ∈ openSegmentTrace a b := by
  exact ⟨r/Real.sqrt (squaredLength (b-a)),radialPort_parameter_between a b r hr hshort,
    (radialPort_parameter a b r).symm⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OrientedSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def similarityPoint (o u x : Plane) : Plane :=
  o+(u.1*x.1-u.2*x.2,u.2*x.1+u.1*x.2)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleOffsetLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def circleTrackScale (d w : Plane) : ℝ := (det2 d (rotateQuarter w))⁻¹

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OpenSegmentEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem openSegmentTrace_subset_segment (a b : Plane) : openSegmentTrace a b ⊆ segment ℝ a b := by
  rintro x ⟨t,ht,he⟩
  rw [← Path.range_segment]
  exact ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,by simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingSpokePorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem openSegmentTrace_reverse_mem (a b x : Plane) (hx : x ∈ openSegmentTrace a b) :
    x ∈ openSegmentTrace b a := by
  obtain ⟨t,ht,he⟩ := hx
  exact ⟨1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,(segmentPoint_reverse a b t).trans he⟩

theorem squaredLength_sub_comm (a b : Plane) : squaredLength (a-b)=squaredLength (b-a) := by
  dsimp [squaredLength]
  ring

def PolygonalChain.startPort {O : Set Plane} {a b : Plane} (P : PolygonalChain O a b) (r : ℝ) : Plane :=
  radialPort (P.vertices 0) (P.vertices 1) r

def PolygonalChain.endPort {O : Set Plane} {a b : Plane} (P : PolygonalChain O a b) (r : ℝ) : Plane :=
  radialPort (P.vertices P.pieces) (P.vertices (P.pieces-1)) r

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_IncidentSpokePorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

instance incidentEdgesFintype (j : BipartiteVertex m n) : Fintype (IncidentEdges j) := by
  classical
  unfold IncidentEdges
  infer_instance

def drawingSpokePort (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (r : ℝ) (j : BipartiteVertex m n) (e : IncidentEdges j) : Plane :=
  if j=Sum.inl e.val.1 then (P e.val).startPort r else (P e.val).endPort r

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SpokeTrackDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def drawingSpokeDirection (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (j : BipartiteVertex m n) (e : IncidentEdges j) : Plane :=
  if j=Sum.inl e.val.1 then trackDirection (P e.val).vertices 0
    else trackDirection (P e.val).vertices ((P e.val).pieces-1)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_LocallyStraightNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def LocallyStraightCrossings (D : AdmissibleDrawing m n) : Prop :=
  ∀ e f : BipartiteEdge m n, e ≠ f → ∀ x,
    x ∈ edgeInterior D.toContinuousDrawing e → x ∈ edgeInterior D.toContinuousDrawing f →
      LocallyStraightAt D.toContinuousDrawing e x ∧ LocallyStraightAt D.toContinuousDrawing f x

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CutTraceSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.ExteriorCrossingCut
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {r : C.InnerIndex}

theorem first_parameter_point (K : ExteriorCrossingCut C P r) :
    D'.edge r.1 ((P r.1).knot K.first)=C.portPoint (C.incomingPort r) :=
  ((drawingEdgeWalk_getVert P r.1 K.first.val (by have h := K.first.isLt; omega)).trans
    ((P r.1).vertices_at K.first)).symm.trans K.first_point

theorem last_parameter_point (K : ExteriorCrossingCut C P r) :
    D'.edge r.1 ((P r.1).knot K.last)=C.portPoint (C.outgoingPort r) :=
  ((drawingEdgeWalk_getVert P r.1 K.last.val (by have h := K.last.isLt; omega)).trans
    ((P r.1).vertices_at K.last)).symm.trans K.last_point

theorem prefix_subset_edge (K : ExteriorCrossingCut C P r) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) ⊆ Set.range (D'.edge r.1) := by
  intro x hx
  obtain ⟨t,_,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  exact ⟨t,he⟩

theorem suffix_subset_edge (K : ExteriorCrossingCut C P r) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) ⊆ Set.range (D'.edge r.1) := by
  intro x hx
  obtain ⟨t,_,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hx
  exact ⟨t,he⟩

theorem incoming_not_suffix (K : ExteriorCrossingCut C P r) :
    C.portPoint (C.incomingPort r) ∉ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) := by
  intro hx
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hx
  have heq := D'.edge_injective r.1 (he.trans K.first_parameter_point.symm)
  exact ((P r.1).increasing K.ordered).not_ge (heq ▸ ht.1)

theorem outgoing_not_prefix (K : ExteriorCrossingCut C P r) :
    C.portPoint (C.outgoingPort r) ∉ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) := by
  intro hx
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  have heq := D'.edge_injective r.1 (he.trans K.last_parameter_point.symm)
  exact ((P r.1).increasing K.ordered).not_ge (heq ▸ ht.2)

theorem prefix_suffix_disjoint (K : ExteriorCrossingCut C P r) :
    Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  obtain ⟨u,hu,hf⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hy
  have heq := D'.edge_injective r.1 (he.trans hf.symm)
  exact ((P r.1).increasing K.ordered).not_ge (hu.1.trans (heq ▸ ht.2))

end Zarankiewicz.ExteriorCrossingCut

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingDiskOwners
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_in_crossingDisk_chord (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (p : C.InnerIndex) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hxin : x ∈ C.crossingDisk p) :
    ∃ r : C.InnerIndex, r.1=e ∧ C.innerMark r=C.innerMark p ∧ x ∈ Set.range (C.crossingChord r) := by
  rcases (E.assembledEdge_range_iff v e x).mp hx with (hx | ⟨i,hi,hx⟩ | ⟨r,hr,hx⟩) | hx
  · exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
      hxin (C.vertex_spoke_range_in_disk v hv _ (C.startPortAt e) hx))
  · obtain ⟨t,rfl⟩ := hx
    exact False.elim (hxin.not_ge (E.outside_open_disks i t (C.innerMark p)))
  · refine ⟨r,hr,?_,hx⟩
    by_contra hn
    exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
      (C.crossingChord_range_subset_disk r hx) (C.crossingDisk_subset_closed p hxin)
  · rw [endSpoke_range] at hx
    exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
      hxin (C.vertex_spoke_range_in_disk v hv _ (C.endPortAt e) hx))

theorem assembled_crossingDisk_owner (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : BipartiteEdge m n) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hxin : x ∈ C.crossingDisk p) : e=p.1 ∨ e=q.1 := by
  obtain ⟨r,hr,hrm,hxr⟩ := E.assembled_in_crossingDisk_chord v hv e p x hx hxin
  rcases C.innerIndex_at_mark_pair p q r hpq hm hrm.symm with rfl | rfl
  · exact Or.inl hr.symm
  · exact Or.inr hr.symm

theorem assembled_other_edge_avoids_crossingDisk (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    Disjoint (Set.range (E.assembledEdge v e)) (C.crossingDisk p) := by
  apply Set.disjoint_left.mpr
  intro x hx hxin
  rcases E.assembled_crossingDisk_owner v hv p q hpq hm e x hx hxin with h | h
  · exact hep h
  · exact heq h

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectionOtherEdges
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segment_disjoint_of_open_containment (a b : Plane) (U S : Set Plane)
    (hin : openSegmentTrace a b ⊆ U) (hout : Disjoint S U)
    (ha : a ∉ S) (hb : b ∉ S) : Disjoint (segment ℝ a b) S := by
  apply Set.disjoint_left.mpr
  intro x hx hs
  rcases segment_endpoint_or_open a b x hx with rfl | rfl | hx
  · exact ha hs
  · exact hb hs
  · exact Set.disjoint_left.mp hout hs (hin hx)

namespace PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_port_not_mem_other_edge (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (r : C.Port) (her : e ≠ r.1.1) :
    C.portPoint r ∉ Set.range (E.assembledEdge v e) :=
  fun hx => her (E.assembled_port_unique_edge v hv e r hx)

theorem reconnection_other_edge_disjoint (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (i : Bool) (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    Disjoint (segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i))
      (Set.range (E.assembledEdge v e)) := by
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm i)
    (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
  · cases i
    · exact E.assembled_port_not_mem_other_edge v hv e (C.incomingPort q) heq
    · exact E.assembled_port_not_mem_other_edge v hv e (C.incomingPort p) hep
  · cases i
    · exact E.assembled_port_not_mem_other_edge v hv e (C.outgoingPort p) hep
    · exact E.assembled_port_not_mem_other_edge v hv e (C.outgoingPort q) heq

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectionOppositeCuts
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem forward_chord_disjoint_opposite_prefix
    (Kq : ExteriorCrossingCut C P q) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val))) := by
  have hqp : q.1 ≠ p.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he.symm hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _ (C.reconnection_open_in_disk p q hm true)
  · simpa only [DrawingPassages.crossingDisk,hm] using Kq.prefix_outside
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv q.1 (C.incomingPort p) hqp (Kq.prefix_subset_edge hx)
  · exact Kq.outgoing_not_prefix

theorem forward_chord_disjoint_opposite_suffix
    (Kp : ExteriorCrossingCut C P p) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val))) := by
  have hpqe : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm true) Kp.suffix_outside
  · exact Kp.incoming_not_suffix
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv p.1 (C.outgoingPort q) hpqe (Kp.suffix_subset_edge hx)

theorem backward_chord_disjoint_opposite_prefix
    (Kp : ExteriorCrossingCut C P p) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val))) := by
  have hpqe : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm false) Kp.prefix_outside
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv p.1 (C.incomingPort q) hpqe (Kp.prefix_subset_edge hx)
  · exact Kp.outgoing_not_prefix

theorem backward_chord_disjoint_opposite_suffix
    (Kq : ExteriorCrossingCut C P q) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val))) := by
  have hqp : q.1 ≠ p.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he.symm hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _ (C.reconnection_open_in_disk p q hm false)
  · simpa only [DrawingPassages.crossingDisk,hm] using Kq.suffix_outside
  · exact Kq.incoming_not_suffix
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv q.1 (C.outgoingPort p) hqp (Kq.suffix_subset_edge hx)

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectedIntersectionCases
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem reconnected_paths_meeting_cases
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (reconnectedForwardPath Kp Kq hm))
    (hy : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    (x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∧
      x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val))) ∨
    (x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) ∧
      x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val))) := by
  have hFP := E.forward_chord_disjoint_opposite_prefix v hvinj hv hdet P Kq hpq hm
  have hFS := E.forward_chord_disjoint_opposite_suffix v hvinj hv hdet P Kp hpq hm
  have hBP := E.backward_chord_disjoint_opposite_prefix v hvinj hv hdet P Kp hpq hm
  have hBS := E.backward_chord_disjoint_opposite_suffix v hvinj hv hdet P Kq hpq hm
  have hchord := C.reconnection_chords_disjoint p q hcross true false (by decide)
  rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · rcases reconnectedBackwardPath_trace Kp Kq hm hy with (hy | hy) | hy
    · exact Or.inl ⟨hx,hy⟩
    · exact False.elim (Set.disjoint_left.mp hBP hy hx)
    · exact False.elim (Set.disjoint_left.mp Kp.prefix_suffix_disjoint hx hy)
  · rcases reconnectedBackwardPath_trace Kp Kq hm hy with (hy | hy) | hy
    · exact False.elim (Set.disjoint_left.mp hFP hx hy)
    · exact False.elim (Set.disjoint_left.mp hchord hx hy)
    · exact False.elim (Set.disjoint_left.mp hFS hx hy)
  · rcases reconnectedBackwardPath_trace Kp Kq hm hy with (hy | hy) | hy
    · exact False.elim (Set.disjoint_left.mp Kq.prefix_suffix_disjoint hy hx)
    · exact False.elim (Set.disjoint_left.mp hBS hy hx)
    · exact Or.inr ⟨hy,hx⟩

theorem reconnected_paths_meeting_old_edges
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (reconnectedForwardPath Kp Kq hm))
    (hy : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∧ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases E.reconnected_paths_meeting_cases v hvinj hv hdet P Kp Kq hpq hm hcross x hx hy with h | h
  · exact ⟨Kp.prefix_subset_edge h.1,Kq.prefix_subset_edge h.2⟩
  · exact ⟨Kp.suffix_subset_edge h.1,Kq.suffix_subset_edge h.2⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SurgeryRouteIntersections
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem reconnectedForwardPath_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (reconnectedForwardPath Kp Kq hm))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · exact Or.inl (Kp.prefix_subset_edge hx)
  · exact False.elim (Set.disjoint_left.mp (E.reconnection_other_edge_disjoint v hv p q hpq hm true e hep heq) hx hy)
  · exact Or.inr (Kq.suffix_subset_edge hx)

theorem reconnectedBackwardPath_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · exact Or.inr (Kq.prefix_subset_edge hx)
  · exact False.elim (Set.disjoint_left.mp (E.reconnection_other_edge_disjoint v hv p q hpq hm false e hep heq) hx hy)
  · exact Or.inl (Kp.suffix_subset_edge hx)

theorem adjacentSurgeryRoutes_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
      x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  have hf := E.reconnectedForwardPath_meeting_other v hvinj hv hdet P Kp Kq hpq hm e hep heq x
  have hb := E.reconnectedBackwardPath_meeting_other v hvinj hv hdet P Kp Kq hpq hm e hep heq x
  rcases hx with hx | hx
  · unfold adjacentSurgeryRouteP at hx
    split at hx
    · exact hb hx hy
    · exact hf hx hy
  · unfold adjacentSurgeryRouteQ at hx
    split at hx
    · exact hf hx hy
    · exact hb hx hy

theorem adjacentSurgeryRoutes_meeting_each_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
    (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∧ x ∈ Set.range (E.assembledEdge v q.1) := by
  have hh := E.reconnected_paths_meeting_old_edges v hvinj hv hdet P Kp Kq hpq hm hcross x
  by_cases h : p.1.1=q.1.1
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dite_eq_left h] at hx hy
    exact hh hy hx
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dite_eq_right h] at hx hy
    exact hh hx hy

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SurgeryCrossingContainment
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem adjacentSurgeryDrawing_crossings_subset
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) ⊆
      crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
  let B := (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  intro x hx
  obtain ⟨e,f,hef,hxe,hxf⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hpair (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) : x ∈ crossingPoints B := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hx hy
    exact crossing_of_ranges_not_vertices B p.1 q.1
      (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) x hh.1 hh.2 havoid
  have hmixed (g : BipartiteEdge m n) (hgp : g ≠ p.1) (hgq : g ≠ q.1)
      (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (hy : x ∈ Set.range (B.edge g)) : x ∈ crossingPoints B := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj g hgp hgq x hx hy with h | h
    · exact crossing_of_ranges_not_vertices B p.1 g (Ne.symm hgp) x h hy havoid
    · exact crossing_of_ranges_not_vertices B q.1 g (Ne.symm hgq) x h hy havoid
  have hcases (g : BipartiteEdge m n) (hg : x ∈ Set.range (A.edge g)) :=
    B.replaceTwoRoutes_range_cases p.1 q.1 (adjacentSurgeryRouteP Kp Kq hm hadj)
      (adjacentSurgeryRouteQ Kp Kq hm hadj) g x hg
  rcases hcases e (edgeInterior_subset_range A e hxe) with ⟨hep,hx⟩ | ⟨heq,hx⟩ | ⟨hep,heq,hx⟩
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact False.elim (hef (hep.trans hfp.symm))
    · exact hpair hx hy
    · exact hmixed f hfp hfq (Or.inl hx) hy
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hpair hy hx
    · exact False.elim (hef (heq.trans hfq.symm))
    · exact hmixed f hfp hfq (Or.inr hx) hy
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hmixed e hep heq (Or.inl hy) hx
    · exact hmixed e hep heq (Or.inr hy) hx
    · exact crossing_of_ranges_not_vertices B e f hef x hx hy havoid

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SurgeryNoTriples
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem adjacentSurgeryDrawing_no_triples
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e f g : BipartiteEdge m n) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) e ∩
      edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) f ∩
      edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) g = ∅ := by
  let B := E.assembledAdmissible v hvinj hv hdet
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨⟨hxe,hxf⟩,hxg⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hthree (a b c : BipartiteEdge m n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b))
      (hc : x ∈ Set.range (B.edge c)) : False := by
    have hmem : x ∈ edgeInterior B.toContinuousDrawing a ∩ edgeInterior B.toContinuousDrawing b ∩
        edgeInterior B.toContinuousDrawing c :=
      ⟨⟨edgeInterior_of_range_not_vertices _ a x ha havoid,
        edgeInterior_of_range_not_vertices _ b x hb havoid⟩,edgeInterior_of_range_not_vertices _ c x hc havoid⟩
    rw [B.no_triples a b c hab hac hbc] at hmem
    exact hmem
  have htwo (a : BipartiteEdge m n) (hap : a ≠ p.1) (haq : a ≠ q.1)
      (hp : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hq : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) : False := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hp hq
    exact hthree p.1 q.1 a (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm))
      (Ne.symm hap) (Ne.symm haq) hh.1 hh.2 ha
  have hone (a b : BipartiteEdge m n) (hab : a ≠ b)
      (hap : a ≠ p.1) (haq : a ≠ q.1) (hbp : b ≠ p.1) (hbq : b ≠ q.1)
      (hh : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b)) : False := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj a hap haq x hh ha with hp | hq
    · exact hthree p.1 a b (Ne.symm hap) (Ne.symm hbp) hab hp ha hb
    · exact hthree q.1 a b (Ne.symm haq) (Ne.symm hbq) hab hq ha hb
  have hcases (a : BipartiteEdge m n) (ha : x ∈ Set.range (A.edge a)) :=
    B.toContinuousDrawing.replaceTwoRoutes_range_cases p.1 q.1 (adjacentSurgeryRouteP Kp Kq hm hadj)
      (adjacentSurgeryRouteQ Kp Kq hm hadj) a x ha
  have hec := hcases e (edgeInterior_subset_range A e hxe)
  have hfc := hcases f (edgeInterior_subset_range A f hxf)
  have hgc := hcases g (edgeInterior_subset_range A g hxg)
  rcases hec with ⟨hep,hx⟩ | ⟨heq,hx⟩ | ⟨hep,heq,hx⟩
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hef (hep.trans hfp.symm)
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact heg (hep.trans hgp.symm)
      · exact hfg (hfq.trans hgq.symm)
      · exact htwo g hgp hgq hx hy hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact heg (hep.trans hgp.symm)
      · exact htwo f hfp hfq hx hz hy
      · exact hone f g hfg hfp hfq hgp hgq (Or.inl hx) hy hz
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hfg (hfp.trans hgp.symm)
      · exact heg (heq.trans hgq.symm)
      · exact htwo g hgp hgq hy hx hz
    · exact hef (heq.trans hfq.symm)
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact htwo f hfp hfq hz hx hy
      · exact heg (heq.trans hgq.symm)
      · exact hone f g hfg hfp hfq hgp hgq (Or.inr hx) hy hz
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hfg (hfp.trans hgp.symm)
      · exact htwo e hep heq hy hz hx
      · exact hone e g heg hep heq hgp hgq (Or.inl hy) hx hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact htwo e hep heq hz hy hx
      · exact hfg (hfq.trans hgq.symm)
      · exact hone e g heg hep heq hgp hgq (Or.inr hy) hx hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hone e f hef hep heq hfp hfq (Or.inl hz) hx hy
      · exact hone e f hef hep heq hfp hfq (Or.inr hz) hx hy
      · exact hthree e f g hef heg hfg hx hy hz

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SurgeryStrictPointCount
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  {p q : C.InnerIndex}

theorem crossingChord_meeting_is_assembled_crossing (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hxin := (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1
  have hxinq : x ∈ C.crossingDisk q := by
    simpa only [DrawingPassages.crossingDisk,hm] using hxin
  apply crossing_of_ranges_not_vertices (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing
    p.1 q.1 (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) x
    ((E.assembled_range_in_crossingDisk v hv p x hxin).mpr hxp)
    ((E.assembled_range_in_crossingDisk v hv q x hxinq).mpr hxq)
  intro j he
  exact Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p j) hxin (he.symm ▸ (hv j).le)

theorem adjacentSurgeryDrawing_strict_crossing_ncard
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    (crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).Finite ∧
      (crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).ncard <
        (crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing).ncard := by
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  have hsub := E.adjacentSurgeryDrawing_crossings_subset v hvinj hv hdet P Kp Kq hpq hm hadj hcross hemb
  have hfinite := (E.assembledAdmissible v hvinj hv hdet).crossings_finite
  have hremoved := adjacentSurgeryDrawing_avoids_crossing Kp Kq hm hpq hadj hv hemb x hxp hxq (by
    intro e hep heq hx
    exact Set.disjoint_left.mp (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
      hx (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1)
  have hnot : x ∉ crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) := by
    rintro ⟨e,f,hef,hxe,hxf⟩
    exact hremoved e (edgeInterior_subset_range _ e hxe)
  refine ⟨hfinite.subset hsub,Set.ncard_lt_ncard ⟨hsub,?_⟩ hfinite⟩
  intro hrev
  exact hnot (hrev (E.crossingChord_meeting_is_assembled_crossing v hvinj hv hdet hpq x hxp hxq))

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SurgeryFiniteDrawing
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

def adjacentSurgeryFiniteDrawing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    FiniteIntersectionDrawing m n where
  toContinuousDrawing := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  crossings_finite := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).1
  no_triples := E.adjacentSurgeryDrawing_no_triples v hvinj hv hdet P Kp Kq hpq hm hadj
    (C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq) hemb

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_LocallyTransverseNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def LocallyTransverseCrossings (D : AdmissibleDrawing m n) : Prop :=
  ∀ e f : BipartiteEdge m n, e ≠ f → ∀ x,
    x ∈ edgeInterior D.toContinuousDrawing e → x ∈ edgeInterior D.toContinuousDrawing f →
      ∃ a b c d : Plane, det2 (b-a) (d-c) ≠ 0 ∧
        x ∈ openSegmentTrace a b ∧ x ∈ openSegmentTrace c d ∧
        ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
          (∀ z ∈ U, z ∈ edgeInterior D.toContinuousDrawing e ↔ z ∈ openSegmentTrace a b) ∧
          (∀ z ∈ U, z ∈ edgeInterior D.toContinuousDrawing f ↔ z ∈ openSegmentTrace c d)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedChainVertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

def startFraction (P : PolygonalChain O a b) (r : ℝ) : ℝ :=
  r/Real.sqrt (squaredLength (P.vertices 1-P.vertices 0))

def endFraction (P : PolygonalChain O a b) (r : ℝ) : ℝ :=
  r/Real.sqrt (squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))

def truncatedVertices (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) : Plane :=
  if i=0 then P.startPort r else if i=P.pieces then P.endPort r else P.vertices i

theorem truncatedVertices_first (P : PolygonalChain O a b) (r : ℝ) :
    P.truncatedVertices r 0=P.startPort r := by simp [truncatedVertices]

theorem truncatedVertices_last (P : PolygonalChain O a b) (hp : 0 < P.pieces) (r : ℝ) :
    P.truncatedVertices r P.pieces=P.endPort r := by simp [truncatedVertices,ne_of_gt hp]

theorem truncated_piece_subset (P : PolygonalChain O a b) (r : ℝ) (hr : 0 < r)
    (hfirst : r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))
    (i : ℕ) (hi : i < P.pieces) :
    segment ℝ (P.truncatedVertices r i) (P.truncatedVertices r (i+1)) ⊆
      segment ℝ (P.vertices i) (P.vertices (i+1)) := by
  apply (convex_segment (𝕜 := ℝ) _ _).segment_subset
  · by_cases h0 : i=0
    · subst i
      rw [truncatedVertices_first]
      exact openSegmentTrace_subset_segment _ _ (radialPort_mem_openSegment _ _ r hr hfirst)
    · simp only [truncatedVertices,ite_eq_right h0,ite_eq_right (show i ≠ P.pieces by omega)]
      exact left_mem_segment ℝ _ _
  · by_cases hn : i+1=P.pieces
    · rw [show P.truncatedVertices r (i+1)=P.endPort r by rw [hn]; exact P.truncatedVertices_last (by omega) r]
      have hh : i=P.pieces-1 := by omega
      have hs : r^2 < squaredLength (P.vertices (P.pieces-1)-P.vertices P.pieces) := by
        rwa [squaredLength_sub_comm]
      have hx := openSegmentTrace_reverse_mem _ _ _ (radialPort_mem_openSegment _ _ r hr hs)
      have hseg := openSegmentTrace_subset_segment _ _ hx
      simpa only [endPort,hh,show P.pieces-1+1=P.pieces by omega] using hseg
    · simp only [truncatedVertices,ite_eq_right (show i+1 ≠ 0 by omega),ite_eq_right hn]
      exact right_mem_segment ℝ _ _

end PolygonalChain
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedChainDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

def truncatedScale (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) : ℝ :=
  1-(if i=0 then P.startFraction r else 0)-(if i+1=P.pieces then P.endFraction r else 0)

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedChainPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

def truncated (P : PolygonalChain O a b) (hp : 0 < P.pieces) (r : ℝ) (hr : 0 < r)
    (hfirst : r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    PolygonalChain O (P.startPort r) (P.endPort r) where
  pieces := P.pieces
  vertices := P.truncatedVertices r
  first := P.truncatedVertices_first r
  last := P.truncatedVertices_last hp r
  start_mem := P.inside 0 hp (openSegmentTrace_subset_segment _ _ (radialPort_mem_openSegment _ _ r hr hfirst))
  inside := fun i hi => (P.truncated_piece_subset r hr hfirst hlast i hi).trans (P.inside i hi)

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

structure VertexTruncation (D : ContinuousDrawing m n) where
  chain : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
    (D.vertex (.inl e.1)) (D.vertex (.inr e.2))
  minimal : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
    (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (chain e).pieces ≤ Q.pieces
  radius : ℝ
  radius_pos : 0 < radius
  short : ∀ e, 4*radius^2 < squaredLength ((chain e).vertices 1-(chain e).vertices 0) ∧
    4*radius^2 < squaredLength ((chain e).vertices (chain e).pieces-(chain e).vertices ((chain e).pieces-1))
  disks_disjoint : ∀ j k, j ≠ k →
    Disjoint (closedRoundDisk (D.vertex j) radius) (closedRoundDisk (D.vertex k) radius)
  piece_clearance : ∀ j e (i : Fin (chain e).pieces),
    ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(chain e).pieces)) →
    Disjoint (closedRoundDisk (D.vertex j) radius)
      (segment ℝ ((chain e).vertices i.val) ((chain e).vertices (i.val+1)))

namespace VertexTruncation
variable {D : ContinuousDrawing m n} (V : VertexTruncation D)

def pieces (e : BipartiteEdge m n) : ℕ := (V.chain e).pieces

def vertices (e : BipartiteEdge m n) : ℕ → Plane := (V.chain e).truncatedVertices V.radius

def startPort (e : BipartiteEdge m n) : Plane := (V.chain e).startPort V.radius

def endPort (e : BipartiteEdge m n) : Plane := (V.chain e).endPort V.radius

theorem pieces_pos (e : BipartiteEdge m n) : 0 < V.pieces e := drawing_chain_pieces_pos D e (V.chain e)

theorem weak_short (e : BipartiteEdge m n) :
    V.radius^2 < squaredLength ((V.chain e).vertices 1-(V.chain e).vertices 0) ∧
    V.radius^2 < squaredLength ((V.chain e).vertices (V.chain e).pieces-(V.chain e).vertices ((V.chain e).pieces-1)) := by
  constructor <;> nlinarith [(V.short e).1,(V.short e).2,sq_nonneg V.radius]

def path (e : BipartiteEdge m n) : Path (V.startPort e) (V.endPort e) :=
  ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos (V.weak_short e).1 (V.weak_short e).2).path

end VertexTruncation
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedSpokeDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

def spokePort (j : BipartiteVertex m n) (e : IncidentEdges j) : Plane :=
  drawingSpokePort D V.chain V.radius j e

def spokeIndex (j : BipartiteVertex m n) (e : IncidentEdges j) : ℕ :=
  if j=Sum.inl e.val.1 then 0 else V.pieces e.val-1

def spokeDirection (j : BipartiteVertex m n) (e : IncidentEdges j) : Plane :=
  trackDirection (V.vertices e.val) (V.spokeIndex j e)

def spokeScale (j : BipartiteVertex m n) (e : IncidentEdges j) : ℝ :=
  circleTrackScale (V.spokeDirection j e) (V.spokePort j e-D.vertex j)

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedSpokeCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : ContinuousDrawing m n}

structure TruncatedSpokeCoordinates (V : VertexTruncation D) where
  frame : BipartiteVertex m n → Plane
  frame_ne_zero : ∀ j, frame j ≠ 0
  frame_length : ∀ j, squaredLength (frame j)=V.radius^2
  node : ∀ j, IncidentEdges j → ℝ
  node_injective : ∀ j, Function.Injective (node j)
  point_eq : ∀ j e, similarityPoint (D.vertex j) (frame j) (circlePoint (node j e))=V.spokePort j e

namespace TruncatedSpokeCoordinates
variable {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

def shiftedPort (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) : Plane :=
  similarityPoint (D.vertex j) (C.frame j)
    (circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε))

def tangentPort (_C : TruncatedSpokeCoordinates V) (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) : Plane :=
  V.spokePort j e+ε • normalShift (V.spokeDirection j e)

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TrackEndpointConnections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

def leftIncident (_V : VertexTruncation D) (e : BipartiteEdge m n) : IncidentEdges (m:=m) (n:=n) (Sum.inl e.1) := ⟨e,Or.inl rfl⟩
def rightIncident (_V : VertexTruncation D) (e : BipartiteEdge m n) : IncidentEdges (m:=m) (n:=n) (Sum.inr e.2) := ⟨e,Or.inr rfl⟩

theorem vertices_first (e : BipartiteEdge m n) : V.vertices e 0=V.startPort e :=
  (V.chain e).truncatedVertices_first V.radius

theorem vertices_last (e : BipartiteEdge m n) : V.vertices e (V.pieces e)=V.endPort e :=
  (V.chain e).truncatedVertices_last (V.pieces_pos e) V.radius

theorem shiftedTrack_first (C : TruncatedSpokeCoordinates V) (e : BipartiteEdge m n) (ε : ℝ) :
    shiftedTrack (V.vertices e) (V.pieces e) ε 0=
      C.tangentPort (Sum.inl e.1) (V.leftIncident e) ε := by
  simp [shiftedTrack,trackOffset,TruncatedSpokeCoordinates.tangentPort,spokeDirection,
    spokeIndex,leftIncident,V.vertices_first,spokePort,drawingSpokePort,startPort]

theorem shiftedTrack_last (C : TruncatedSpokeCoordinates V) (e : BipartiteEdge m n) (ε : ℝ) :
    shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)=
      C.tangentPort (Sum.inr e.2) (V.rightIncident e) ε := by
  have hn : V.pieces e ≠ 0 := ne_of_gt (V.pieces_pos e)
  simp [shiftedTrack,trackOffset,hn,TruncatedSpokeCoordinates.tangentPort,spokeDirection,
    spokeIndex,rightIncident,V.vertices_last,spokePort,drawingSpokePort,endPort]

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawnEdgeChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

def trackChain (e : BipartiteEdge m n) : PolygonalChain Set.univ (V.startPort e) (V.endPort e) where
  pieces := V.pieces e
  vertices := V.vertices e
  first := V.vertices_first e
  last := V.vertices_last e
  start_mem := Set.mem_univ _
  inside := fun _ _ => Set.subset_univ _

def chordChain (j : BipartiteVertex m n) (a b : IncidentEdges j) :
    PolygonalChain Set.univ (V.spokePort j a) (V.spokePort j b) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

def shiftedTrackChain (e : BipartiteEdge m n) (ε : ℝ) :
    PolygonalChain Set.univ (C.tangentPort (Sum.inl e.1) (V.leftIncident e) ε)
      (C.tangentPort (Sum.inr e.2) (V.rightIncident e) ε) where
  pieces := V.pieces e
  vertices := shiftedTrack (V.vertices e) (V.pieces e) ε
  first := V.shiftedTrack_first C e ε
  last := V.shiftedTrack_last C e ε
  start_mem := Set.mem_univ _
  inside := fun _ _ => Set.subset_univ _

def connectorChain (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort j e ε) (C.tangentPort j e ε) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

def shiftedEdgeChain (e : BipartiteEdge m n) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort (Sum.inl e.1) (V.leftIncident e) ε)
      (C.shiftedPort (Sum.inr e.2) (V.rightIncident e) ε) :=
  ((C.connectorChain (Sum.inl e.1) (V.leftIncident e) ε).join (C.shiftedTrackChain e ε)).join
    (C.connectorChain (Sum.inr e.2) (V.rightIncident e) ε).reverse

def shiftedChordChain (j : BipartiteVertex m n) (a b : IncidentEdges j) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort j a ε) (C.shiftedPort j b ε) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BipartiteDartGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def dartSourceIncident (d : (completeBipartite m n).Dart) : IncidentEdges d.fst :=
  ⟨bipartiteDartEdge d,bipartiteDart_source_incident d⟩

def dartTargetIncident (d : (completeBipartite m n).Dart) : IncidentEdges d.snd :=
  ⟨bipartiteDartEdge d,bipartiteDart_target_incident d⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem bounded_zero (k : ℕ) : Bounded k (0 : PolynomialModule ℝ W) := by
  intro n hn
  simp

theorem bounded_mono {k l : ℕ} {p : PolynomialModule ℝ W}
    (hp : Bounded k p) (hkl : k ≤ l) : Bounded l p :=
  fun n hn => hp n (hkl.trans hn)

theorem bounded_add {k : ℕ} {p q : PolynomialModule ℝ W}
    (hp : Bounded k p) (hq : Bounded k q) : Bounded k (p + q) := by
  intro n hn
  simp [hp n hn, hq n hn]

theorem bounded_sub {k : ℕ} {p q : PolynomialModule ℝ W}
    (hp : Bounded k p) (hq : Bounded k q) : Bounded k (p - q) := by
  intro n hn
  change p.coeff n - q.coeff n = 0
  rw [hp n hn, hq n hn, sub_self]

theorem bounded_single {k n : ℕ} (hn : n < k) (w : W) :
    Bounded k (single ℝ n w) := by
  intro j hj
  simp [show n ≠ j by omega]

theorem bounded_zero_iff (p : PolynomialModule ℝ W) : Bounded 0 p ↔ p = 0 := by
  constructor
  · intro h
    ext n
    exact h n (Nat.zero_le n)
  · rintro rfl
    exact bounded_zero 0

theorem bounded_mulRoot {k : ℕ} {p : PolynomialModule ℝ W}
    (t : ℝ) (hp : Bounded k p) : Bounded (k+1) (mulRoot t p) := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [mulRoot_coeff_succ, hp j (by omega), hp (j+1) (by omega)]
  simp

theorem eq_constant_of_bounded_one {p : PolynomialModule ℝ W} (hp : Bounded 1 p) :
    p = single ℝ 0 (p.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [hp (n+1) (by omega)]

theorem exists_mulRoot_of_eval_zero (t : ℝ) (k : ℕ) (p : PolynomialModule ℝ W)
    (hp : Bounded (k+1) p) (he : eval t p = 0) :
    ∃ q, Bounded k q ∧ mulRoot t q = p := by
  induction k generalizing p with
  | zero =>
    have hc := eq_constant_of_bounded_one hp
    have hz : p.coeff 0 = 0 := by
      rw [hc] at he
      simpa only [eval_single, pow_zero, one_smul] using he
    refine ⟨0, bounded_zero 0, ?_⟩
    have hp0 : p = 0 := hc.trans (by rw [hz, single_zero])
    simp [mulRoot, hp0]
  | succ k ih =>
    let q₀ := single ℝ k (p.coeff (k+1))
    have hq₀ : Bounded (k+1) q₀ := bounded_single (by omega) _
    let r := p - mulRoot t q₀
    have hr : Bounded (k+1) r := by
      intro n hn
      rcases eq_or_lt_of_le hn with rfl | hn'
      · change p.coeff (k+1) - (mulRoot t q₀).coeff (k+1) = 0
        rw [mulRoot_coeff_succ]
        simp [q₀]
      · exact bounded_sub hp (bounded_mulRoot t hq₀) n (by omega)
    have er : eval t r = 0 := by simp [r, eval_mulRoot, he]
    obtain ⟨q, hq, eq⟩ := ih r hr er
    refine ⟨q + q₀, bounded_add (bounded_mono hq (by omega)) hq₀, ?_⟩
    change (Polynomial.X - Polynomial.C t) • (q + q₀) = p
    rw [smul_add]
    change mulRoot t q + mulRoot t q₀ = p
    rw [eq]
    exact sub_add_cancel p _

theorem eq_zero_of_mulRoot_eq_zero (t : ℝ) (k : ℕ) (p : PolynomialModule ℝ W)
    (hp : Bounded k p) (he : mulRoot t p = 0) : p = 0 := by
  induction k with
  | zero => exact (bounded_zero_iff p).mp hp
  | succ k ih =>
    have hc : p.coeff k = 0 := by
      have hh := congrArg (fun q : PolynomialModule ℝ W => q.coeff (k+1)) he
      rw [mulRoot_coeff_succ, hp (k+1) (by omega)] at hh
      simpa using hh
    apply ih
    intro n hn
    rcases eq_or_lt_of_le hn with rfl | hn'
    · exact hc
    · exact hp n (by omega)

variable {ι : Type*}

def constrained (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    (k : ℕ) : Submodule ℝ (PolynomialModule ℝ Z) where
  carrier := {p | Bounded k p ∧ ∀ i, Z.subtype (eval (node i) p) ∈ U i}
  zero_mem' := ⟨bounded_zero k, by simp⟩
  add_mem' := by
    intro p q hp hq
    refine ⟨bounded_add hp.1 hq.1, ?_⟩
    intro i
    simpa using (U i).add_mem (hp.2 i) (hq.2 i)
  smul_mem' := by
    intro c p hp
    refine ⟨?_, ?_⟩
    · intro n hn
      change c • p.coeff n = 0
      rw [hp.1 n hn, smul_zero]
    · intro i
      simpa using (U i).smul_mem c (hp.2 i)

variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

def constrainedEval (k : ℕ) (t : ℝ) : constrained U node Z k →ₗ[ℝ] Z :=
  (eval t).comp (constrained U node Z k).subtype

def toEvalKernel (k : ℕ) (t : ℝ) :
    constrained U node Z k →ₗ[ℝ] LinearMap.ker (constrainedEval U node Z (k+1) t) where
  toFun p := ⟨⟨mulRoot t p.val, bounded_mulRoot t p.property.1, by
    intro i
    have hi := (U i).smul_mem (node i-t) (p.property.2 i)
    simpa only [eval_mulRoot, _root_.map_smul] using hi⟩, by
      change eval t (mulRoot t p.val) = 0
      simp [eval_mulRoot]⟩
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact (mulRootLinear t).map_add p.val q.val
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (mulRootLinear t).map_smul c p.val

def constrainedCoefficients (k : ℕ) : constrained U node Z k →ₗ[ℝ] (Fin k → Z) where
  toFun p n := p.val.coeff n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_Interpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ι : Type*}

theorem bounded_sum (s : Finset ι) (p : ι → PolynomialModule ℝ W) (k : ℕ)
    (hp : ∀ i ∈ s, Bounded k (p i)) : Bounded k (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_zero (W := W) k
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bounded_add (hp a (Finset.mem_insert_self a s))
      (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))

theorem eq_zero_of_node_roots (node : ι → ℝ) (hn : Function.Injective node)
    (s : Finset ι) (p : PolynomialModule ℝ W) (hp : Bounded s.card p)
    (he : ∀ i ∈ s, eval (node i) p = 0) : p = 0 := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => exact (bounded_zero_iff p).mp hp
  | @insert a s ha ih =>
    have hp' : Bounded (s.card+1) p := by simpa [Finset.card_insert_of_notMem ha] using hp
    obtain ⟨q, hq, eq⟩ := exists_mulRoot_of_eval_zero (node a) s.card p hp'
      (he a (Finset.mem_insert_self a s))
    have hqe : ∀ i ∈ s, eval (node i) q = 0 := by
      intro i hi
      have h := he i (Finset.mem_insert_of_mem hi)
      rw [← eq, eval_mulRoot] at h
      have hia : node i - node a ≠ 0 := sub_ne_zero.mpr (fun e => ha (hn e ▸ hi))
      exact (smul_eq_zero.mp h).resolve_left hia
    have hq0 := ih q hq hqe
    rw [← eq, hq0]
    simp [mulRoot]

variable [Fintype ι]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

theorem bounded_vectorInterpolant (hn : Function.Injective node) (z : ∀ i, ↥(U i ⊓ Z)) :
    Bounded (Fintype.card ι) (vectorInterpolant U node Z z) := by
  classical
  apply bounded_sum
  intro i hi n hge
  rw [smul_single_apply]
  simp only [Nat.zero_le, ite_true, Nat.sub_zero]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
  · exact zero_smul _ _
  · have hc : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [Lagrange.natDegree_basis hn.injOn hi, Finset.card_univ]
    omega

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_Bivariate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule

def biCoeff (p : BiPoly) (a b : ℕ) : ℝ := (p.coeff a).coeff b

def biEval (u v : ℝ) : BiPoly →ₗ[ℝ] ℝ := (eval v).comp (eval u)

def boundedSpace (k : ℕ) : Submodule ℝ (PolynomialModule ℝ ℝ) where
  carrier := {p | Bounded k p}
  zero_mem' := bounded_zero k
  add_mem' := bounded_add
  smul_mem' := by
    intro c p hp n hn
    change c • p.coeff n = 0
    rw [hp n hn, smul_zero]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BivariateCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module
open scoped BigOperators

def biOfCoeffs (s : ℕ) (c : BiExponent s → ℝ) : BiPoly :=
  ∑ a : Fin s, single ℝ a.val (∑ b : Fin s, single ℝ b.val (c (a,b)))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalEndpointCasts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b a' b' : Plane}

def castEndpoints (P : PolygonalChain O a b) (ha : a'=a) (hb : b'=b) : PolygonalChain O a' b' where
  pieces := P.pieces
  vertices := P.vertices
  first := P.first.trans ha.symm
  last := P.last.trans hb.symm
  start_mem := ha.symm ▸ P.start_mem
  inside := P.inside

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DartPathRealizations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

def dartTrackChain (d : (completeBipartite m n).Dart) :
    PolygonalChain Set.univ (V.spokePort d.fst (dartSourceIncident d))
      (V.spokePort d.snd (dartTargetIncident d)) := by
  rcases d with ⟨⟨u,v⟩,h⟩
  rcases u with i | p <;> rcases v with k | q
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)
  · exact (V.trackChain (i,q)).castEndpoints
      (by simp [spokePort,drawingSpokePort,dartSourceIncident,bipartiteDartEdge,startPort])
      (by simp [spokePort,drawingSpokePort,dartTargetIncident,bipartiteDartEdge,endPort])
  · exact (V.trackChain (k,p)).reverse.castEndpoints
      (by simp [spokePort,drawingSpokePort,dartSourceIncident,bipartiteDartEdge,endPort])
      (by simp [spokePort,drawingSpokePort,dartTargetIncident,bipartiteDartEdge,startPort])
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

def shiftedDartChain (d : (completeBipartite m n).Dart) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort d.fst (dartSourceIncident d) ε)
      (C.shiftedPort d.snd (dartTargetIncident d) ε) := by
  rcases d with ⟨⟨u,v⟩,h⟩
  rcases u with i | p <;> rcases v with k | q
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)
  · exact (C.shiftedEdgeChain (i,q) ε).castEndpoints rfl rfl
  · exact (C.shiftedEdgeChain (k,p) ε).reverse.castEndpoints rfl rfl
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DartCyclePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def incidentCast {j k : BipartiteVertex m n} (h : j=k) (e : IncidentEdges j) : IncidentEdges k :=
  ⟨e.val,by simpa only [← h] using e.property⟩

def dartPassageNext (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) : IncidentEdges (d i).snd :=
  incidentCast (hd i).symm (dartSourceIncident (d (i+1)))

namespace VertexTruncation
variable {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem spokePort_cast {j k : BipartiteVertex m n} (h : j=k) (e : IncidentEdges j) :
    V.spokePort k (incidentCast h e)=V.spokePort j e := by subst k; rfl

def dartCycleVertex (d : ℕ → (completeBipartite m n).Dart) (i : ℕ) : Plane :=
  V.spokePort (d i).fst (dartSourceIncident (d i))

def dartCycleBlock (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) :
    PolygonalChain Set.univ (V.dartCycleVertex d i) (V.dartCycleVertex d (i+1)) :=
  ((V.dartTrackChain (d i)).join
    (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).castEndpoints
      rfl (V.spokePort_cast (hd i).symm _).symm

def dartCycleChain (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (N : ℕ) (hN : d N=d 0) :
    PolygonalChain Set.univ (V.dartCycleVertex d 0) (V.dartCycleVertex d 0) :=
  (finitePolygonalChain Set.univ (V.dartCycleVertex d) (Set.mem_univ _) (V.dartCycleBlock d hd) N).castEndpoints
    rfl (congrArg (fun a : (completeBipartite m n).Dart => V.spokePort a.fst (dartSourceIncident a)) hN.symm)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : ContinuousDrawing m n} {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

theorem shiftedPort_cast {j k : BipartiteVertex m n} (h : j=k) (e : IncidentEdges j) (ε : ℝ) :
    C.shiftedPort k (incidentCast h e) ε=C.shiftedPort j e ε := by subst k; rfl

def shiftedCycleVertex (d : ℕ → (completeBipartite m n).Dart) (ε : ℝ) (i : ℕ) : Plane :=
  C.shiftedPort (d i).fst (dartSourceIncident (d i)) ε

def shiftedCycleBlock (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (ε : ℝ) (i : ℕ) :
    PolygonalChain Set.univ (C.shiftedCycleVertex d ε i) (C.shiftedCycleVertex d ε (i+1)) :=
  ((C.shiftedDartChain (d i) ε).join
    (C.shiftedChordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i) ε)).castEndpoints
      rfl (C.shiftedPort_cast (hd i).symm _ ε).symm

def shiftedCycleChain (d : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (N : ℕ) (hN : d N=d 0) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedCycleVertex d ε 0) (C.shiftedCycleVertex d ε 0) :=
  (finitePolygonalChain Set.univ (C.shiftedCycleVertex d ε) (Set.mem_univ _) (C.shiftedCycleBlock d hd ε) N).castEndpoints
    rfl (congrArg (fun a : (completeBipartite m n).Dart => C.shiftedPort a.fst (dartSourceIncident a) ε) hN.symm)

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TruncatedSignedIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

def signedIntersection (e f : BipartiteEdge m n) : ℝ :=
  if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f)

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CycleBlockIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def passageIntersection (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (i j : ℕ) (ε : ℝ) : ℝ :=
  polygonIntersection (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)).vertices
    (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε).vertices 1 1

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexPassagePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def vertexChordPairing (j k : BipartiteVertex m n) (a b : IncidentEdges j) (c d : IncidentEdges k) : ℝ :=
  if h : k=j then chordEndpointPairing (C.node j a) (C.node j b)
    (C.node j (incidentCast h c)) (C.node j (incidentCast h d)) else 0

def passagePairing (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (i j : ℕ) : ℝ :=
  C.vertexChordPairing (d i).snd (f j).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)
    (dartTargetIncident (f j)) (dartPassageNext f hf j)

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_EndpointFlagPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def dartSourceFlag (d : (completeBipartite m n).Dart) : IncidentFlag m n :=
  ⟨d.fst,dartSourceIncident d⟩

def dartTargetFlag (d : (completeBipartite m n).Dart) : IncidentFlag m n :=
  ⟨d.snd,dartTargetIncident d⟩

namespace TruncatedSpokeCoordinates
variable {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def flagPairing (a b : IncidentFlag m n) : ℝ :=
  if h : b.1=a.1 then orderSign (C.node a.1 a.2) (C.node a.1 (incidentCast h b.2))/2 else 0

def edgeEndpointPairing (e f : BipartiteEdge m n) : ℝ :=
  C.flagPairing (dartSourceFlag (forwardBipartiteDart e)) (dartSourceFlag (forwardBipartiteDart f))+
    C.flagPairing (dartTargetFlag (forwardBipartiteDart e)) (dartTargetFlag (forwardBipartiteDart f))

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CycleEndpointSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def cycleIntersectionMatrix : Matrix (BipartiteEdge m n) (BipartiteEdge m n) ℝ :=
  fun e f => V.signedIntersection e f+C.edgeEndpointPairing e f

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RankDetector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def detectorVector (s : ℕ) (node : ι → ℝ) (p q : ι) : BiExponent s → ℝ :=
  fun ab => node p ^ ab.1.val * node q ^ ab.2.val

def detectorAtom (s : ℕ) (node : ι → ℝ) (p q : ι) :
    Matrix (BiExponent s) (BiExponent s) ℝ :=
  detectorWeight node p q • Matrix.vecMulVec (detectorVector s node p q) (detectorVector s node p q)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DetectorCrossingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)

def intersectionBlock (i k : Fin m) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q => V.signedIntersection (i,p) (k,q)

end Zarankiewicz.VertexTruncation

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CycleMatrixBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def leftHalfOrder (i : Fin m) : Matrix (Fin n) (Fin n) ℝ := fun p q =>
  orderSign (C.node (Sum.inl i) (V.leftIncident (i,p))) (C.node (Sum.inl i) (V.leftIncident (i,q)))/2

def rightHalfOrder (p : Fin n) : Matrix (Fin m) (Fin m) ℝ := fun i k =>
  orderSign (C.node (Sum.inr p) (V.rightIncident (i,p))) (C.node (Sum.inr p) (V.rightIncident (k,p)))/2

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
open scoped BigOperators
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

def evaluationFiltration (t : ℝ) (k : ℕ) : Submodule ℝ Z :=
  LinearMap.range (constrainedEval U node Z k t)

def columnIncrement (t : ℝ) (e : ℕ) : ℕ :=
  finrank ℝ (evaluationFiltration U node Z t (e+1)) -
    finrank ℝ (evaluationFiltration U node Z t e)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_EvaluationAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ)

def constrainedInclusion {Z₁ Z₂ : Submodule ℝ W} (hZ : Z₁ ≤ Z₂) (k : ℕ) :
    constrained U node Z₁ k →ₗ[ℝ] constrained U node Z₂ k where
  toFun p := ⟨PolynomialModule.map ℝ (Submodule.inclusion hZ) p.val, by
    constructor
    · intro n hn
      change Submodule.inclusion hZ (p.val.coeff n) = 0
      rw [p.property.1 n hn, map_zero]
    · intro i
      rw [show eval (node i) (PolynomialModule.map ℝ (Submodule.inclusion hZ) p.val) =
        Submodule.inclusion hZ (eval (node i) p.val) by
          simpa using PolynomialModule.eval_map ℝ (Submodule.inclusion hZ) p.val (node i)]
      exact p.property.2 i⟩
  map_add' p q := Subtype.ext ((PolynomialModule.map ℝ (Submodule.inclusion hZ)).map_add p.val q.val)
  map_smul' c p := Subtype.ext ((PolynomialModule.map ℝ (Submodule.inclusion hZ)).map_smul c p.val)

def ambientEval (Z : Submodule ℝ W) (k : ℕ) (t : ℝ) : constrained U node Z k →ₗ[ℝ] W :=
  Z.subtype.comp (constrainedEval U node Z k t)

def ambientEvalRange (Z : Submodule ℝ W) (k : ℕ) (t : ℝ) : Submodule ℝ W :=
  LinearMap.range (ambientEval U node Z k t)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexOrderDetector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def leftNode (i : Fin m) (p : Fin n) : ℝ := C.node (Sum.inl i) (V.leftIncident (i,p))

theorem leftNode_injective (i : Fin m) : Function.Injective (C.leftNode i) := by
  intro p q hpq
  have he := C.node_injective (Sum.inl i) hpq
  exact congrArg (fun e : IncidentEdges (Sum.inl i) => e.val.2) he

@[instance_reducible] def leftOrder (i : Fin m) : LinearOrder (Fin n) := LinearOrder.lift' (C.leftNode i) (C.leftNode_injective i)

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end



-- Prove2me | Definitions.Def_OAIQ4Cc002
-- name    : OAIQ4Cc002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T04:40:50.370394+00:00
-- url     : https://prove2.me/theorems/45630ab7-0a46-4caf-8267-57ae8e8e1ae8
-- title:
--   Definitions bundle OAIQ4Cc002 of the split of OpenAI, The crossing number of complete graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Paper170.complete_graph_crossing_number`, carved from OpenAI's openai/math development (OpenAI, *The crossing number of complete graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 210 declarations of OpenAI's Lean: 102 definitions, 2 inductive types or structures, 2 instances and 104 theorems. The definitions and types are `OAI.Paper170Geometry.PolygonalExterior.adjacentSurgeryFiniteDrawing`, `OAI.Paper170Geometry.PolygonalExterior.assembledAdmissible`, `OAI.Paper170Geometry.PolygonalExterior.assembledDrawing`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.connectorChain`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.cycleIntersectionMatrix`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.edgeEndpointPairing`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.flagPairing`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.passageIntersection`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.passagePairing`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedChordChain`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedCycleBlock`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedCycleChain`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedCycleVertex`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedDartChain`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedEdgeChain`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedPort`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedTrackChain`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.tangentPort`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.vertexChordPairing`, `OAI.Paper170Geometry.VertexTruncation`, `OAI.Paper170Geometry.VertexTruncation.chordChain`, `OAI.Paper170Geometry.VertexTruncation.dartCycleBlock`, `OAI.Paper170Geometry.VertexTruncation.dartCycleChain`, `OAI.Paper170Geometry.VertexTruncation.dartCycleVertex`, `OAI.Paper170Geometry.VertexTruncation.dartTrackChain`, `OAI.Paper170Geometry.VertexTruncation.endPort`, `OAI.Paper170Geometry.VertexTruncation.leftIncident`, `OAI.Paper170Geometry.VertexTruncation.path`, `OAI.Paper170Geometry.VertexTruncation.pieces`, `OAI.Paper170Geometry.VertexTruncation.rightIncident`, `OAI.Paper170Geometry.VertexTruncation.signedIntersection`, `OAI.Paper170Geometry.VertexTruncation.spokeDirection`, `OAI.Paper170Geometry.VertexTruncation.spokeIndex`, `OAI.Paper170Geometry.VertexTruncation.spokePort`, `OAI.Paper170Geometry.VertexTruncation.spokeScale`, `OAI.Paper170Geometry.VertexTruncation.startPort`, `OAI.Paper170Geometry.VertexTruncation.trackChain`, `OAI.Paper170Geometry.VertexTruncation.vertices`, `OAI.Paper170Geometry.adjacentSurgeryDrawing` and 64 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/CompleteCrossing, in whole or in part: `CompleteCrossing_AdjacentSurgery`, `CompleteCrossing_Assembly`, `CompleteCrossing_CrossingCuts`, `CompleteCrossing_CycleIntersections`, `CompleteCrossing_CycleSpace`, `CompleteCrossing_DartPaths`, `CompleteCrossing_DiskChords`, `CompleteCrossing_Drawing`, `CompleteCrossing_Polygonalization`, `CompleteCrossing_SpokePorts`, `CompleteCrossing_SurgeryIntersections`, `CompleteCrossing_Tracks`, `CompleteCrossing_Truncation`, `Crossing_AlternatingPaths`, `Crossing_Bivariate`, `Crossing_CircleChords`, `Crossing_CircleConnectors`, `Crossing_CircleOffsetLine`, `Crossing_CircleOffsetParameter`, `Crossing_DrawingSpokePorts`, `Crossing_EmbeddedGraphPaths`, `Crossing_FiniteAffineCover`, `Crossing_FiniteLineAvoidance`, `Crossing_FinitePolygonalComposition`, `Crossing_GenericPolygonIntersection`, `Crossing_GraphWalkRealizationLaws`, `Crossing_GraphWalkTrace`, `Crossing_OffsetTrack`, `Crossing_OffsetVectors`, `Crossing_OpenSegmentEndpoints`, `Crossing_OrderedPathParts`, `Crossing_PathConcatenationInjective`, `Crossing_PeriodicPolygon`, `Crossing_PolygonComposition`, `Crossing_PolygonalArcInjective`, `Crossing_PolygonalBoundaryReplacement`, `Crossing_PolygonalChainComposition`, `Crossing_PolygonalChainShortcuts`, `Crossing_PolygonalChainTransversality`, `Crossing_PolygonalChains`, `Crossing_PolygonalEndpointCasts`, `Crossing_PolygonalReach`, `Crossing_PolygonalWalks`, `Crossing_ProperCrossingLocality`, `Crossing_RadialBoundaryPorts`, `Crossing_ReducedPolygonalPresentation`, `Crossing_SegmentAugmentation`, `Crossing_SegmentContinuity`, `Crossing_SubdivisionSegments`, `Crossing_TriangleEntryExit`, `Crossing_TriangleOrientations`, `Crossing_TriangleTransversality`, `Crossing_TruncatedChainDirections`, `Crossing_TruncatedChainPath`, `Crossing_TruncatedChainVertices`.
--
--   **Imports.** It imports the published bundle `Def_CompleteCrossing`; the bundles `OAIQ4Cc000` and `OAIQ4Cc001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_cycle_block_radius`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_dart_intersection_radius`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_passage_pairing_radius` and `OAI.Paper170.cycle_pairing_of_coordinates`; the proofs of `OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_cycle_block_radius`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_dart_intersection_radius`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_passage_pairing_radius`, `OAI.Paper170.complete_graph_crossing_number`, `OAI.Paper170.complete_graph_lower_bound`, `OAI.Paper170.cycle_pairing_of_coordinates` and `OAI.Paper170.polygonal_no_adjacent_normalization`.
-- source:
--   OpenAI, The crossing number of complete graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/CompleteCrossing at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_CompleteCrossing
import Definitions.Def_OAIQ4Cc000
import Definitions.Def_OAIQ4Cc001

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Drawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous graph drawings, proper spatial crossings, incidence, and endpoint properties. -/

section

/-! Converting actual nonvertex trace contacts to the exact crossing-point definition. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem crossing_of_ranges_not_vertices (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (hef : e ≠ f) (x : Plane) (he : x ∈ Set.range (D.edge e)) (hf : x ∈ Set.range (D.edge f))
    (hv : ∀ j, x ≠ D.vertex j) : x ∈ Paper170.crossingPoints D :=
  ⟨e,f,hef,edgeInterior_of_range_not_vertices D e x he hv,edgeInterior_of_range_not_vertices D f x hf hv⟩

end Paper170Geometry

end
end

section

/-! A weaker INPUT for normalization: actual simple routes with finite contacts and no triples.
The endpoint's Paper170.AdmissibleDrawing and MainTarget definitions are unchanged. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

def finiteCrossingCount  (D : FiniteIntersectionDrawing graph) : ℕ :=
  D.crossings_finite.toFinset.card

end Paper170Geometry

end
end

section

/-! Finite point incidence for actual drawings, retaining repeated pair crossings. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
open scoped BigOperators Classical

/-- The actual finite set of crossing points for a specified ordered edge pair. -/
def pairCrossings (D : Paper170.AdmissibleDrawing graph) (e f : Edge) : Finset Plane :=
  D.crossings_finite.toFinset.filter (fun x => e ≠ f ∧
    x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∧ x ∈ Paper170.edgeInterior D.toContinuousDrawing f)

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalReach
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

def SegmentReach (O : Set Plane) (a b : Plane) : Prop :=
  Relation.ReflTransGen (fun x y => segment ℝ x y ⊆ O) a b

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChains
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

end PolygonalChain

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FiniteAffineCover
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
-- module Solutions.OAIQ4_Cc.Crossing_OffsetVectors
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
-- module Solutions.OAIQ4_Cc.Crossing_OffsetTrack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

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
-- module Solutions.OAIQ4_Cc.Crossing_SegmentContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

def ClosedSegmentsMeet (a b c d : Plane) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ u ∈ Set.Icc (0 : ℝ) 1,
    segmentPoint a b t = segmentPoint c d u

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalWalks
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

def triangleSegmentIntersection (o a b c d : Plane) : ℝ :=
  segmentCrossingSign o a c d + segmentCrossingSign a b c d + segmentCrossingSign b o c d

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonComposition
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
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChainShortcuts
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
-- module Solutions.OAIQ4_Cc.Crossing_PathConcatenationInjective
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
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalArcInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

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
-- module Solutions.OAIQ4_Cc.Crossing_EmbeddedGraphPaths
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
-- module Solutions.OAIQ4_Cc.Crossing_SubdivisionSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalParametrization
variable {a b : Plane} {γ : Path a b}

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
-- module Solutions.OAIQ4_Cc.Crossing_GraphWalkTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

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
-- module Solutions.OAIQ4_Cc.Crossing_CircleChords
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
-- module Solutions.OAIQ4_Cc.Crossing_FiniteLineAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators Classical

def lineAvoidancePolynomial (z a v : Plane) : ℝ[X] :=
  C v.2 * X - C v.1 * X^2 + C (det2 (z-a) v)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalBoundaryReplacement
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
-- module Solutions.OAIQ4_Cc.Crossing_AlternatingPaths
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
-- module Solutions.OAIQ4_Cc.Crossing_ProperCrossingLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem chart_restr_image_of_local_eq (e : OpenPartialHomeomorph Plane Plane)
    (A A' L U : Set Plane) (hU : IsOpen U) (hA : ∀ x ∈ U, x ∈ A ↔ x ∈ A')
    (h : e '' (e.source ∩ A)=e.target ∩ L) :
    (e.restrOpen U hU) '' ((e.restrOpen U hU).source ∩ A')=(e.restrOpen U hU).target ∩ L := by
  let f := e.restrOpen U hU
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    have hs : x ∈ e.source ∩ U := hx.1
    exact ⟨f.map_source hx.1,(chart_image_mem_iff e A L h x hs.1).mp ((hA x hs.2).mpr hx.2)⟩
  · rintro y ⟨hy,hl⟩
    have hs : f.symm y ∈ f.source := f.map_target hy
    have hs' : f.symm y ∈ e.source ∩ U := hs
    have he : e (f.symm y)=y := f.right_inv hy
    have ha : f.symm y ∈ A := (chart_image_mem_iff e A L h _ hs'.1).mpr (he.symm ▸ hl)
    exact ⟨f.symm y,⟨hs,(hA _ hs'.2).mp ha⟩,f.right_inv hy⟩

theorem properCrossing_of_local_eq (A B A' B' : Set Plane) (x : Plane)
    (h : ProperCrossing A B x) (U : Set Plane) (hU : IsOpen U) (hx : x ∈ U)
    (hA : ∀ z ∈ U, z ∈ A ↔ z ∈ A') (hB : ∀ z ∈ U, z ∈ B ↔ z ∈ B') :
    ProperCrossing A' B' x := by
  obtain ⟨e,hs,he,hEA,hEB⟩ := h
  refine ⟨e.restrOpen U hU,⟨hs,hx⟩,he,?_,?_⟩
  · exact chart_restr_image_of_local_eq e A A' {y | y.2=0} U hU hA hEA
  · exact chart_restr_image_of_local_eq e B B' {y | y.1=0} U hU hB hEB

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_DiskChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior polygonal replacement, ordered passages, and injective middle paths. -/

section

/-! The actual ordered replacement of an edge between its first and last boundary ports is simple. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middlePath_injective (E : PolygonalExterior C) (e : Edge) :
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

theorem middlePath_range_iff (E : PolygonalExterior C) (e : Edge) (x : Plane) :
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! A constructed middle path meets a vertex spoke only at its boundary port. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middle_spoke_meeting (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
    (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : x=C.portPoint p.val := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,⟨s,hs⟩⟩ | ⟨q,hq,hx⟩
  · obtain ⟨t,ht⟩ := hy
    have he := E.exterior_spoke_meeting_parameters v hv i j p s t (hs.trans ht.symm)
    rw [he.1,Path.target] at ht
    exact ht.symm
  · exact False.elim (Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks q j)
      hx (C.vertex_spoke_range_in_disk v hv j p hy))

theorem anchoredMiddle_injective (E : PolygonalExterior C) (e : Edge) :
    Function.Injective (E.anchoredMiddle e) := E.middlePath_injective e

end PolygonalExterior
end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous assembled edges, their incidences, crossings, and absence of triple points. -/

section

/-! Actual simple replacement edges, including both graph-vertex spokes. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembledEdge_injective (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge) :
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
  · have hd := C.vertex_spokes_disjoint_of_vertices_ne v hv (graph.src e) (graph.dst e)
      (graph.loopless e) (C.startPortAt e) (C.endPortAt e)
    exact False.elim (Set.disjoint_left.mp hd hx hy)
  · exact E.middle_spoke_meeting v hv e _ (C.endPortAt e) x hx hy

theorem assembledEdge_range_iff (E : PolygonalExterior C) (v : Vertex → Plane)
    (e : Edge) (x : Plane) :
    x ∈ Set.range (E.assembledEdge v e) ↔
      (x ∈ Set.range (startSpoke C v e) ∨
        (∃ i : C.ArcIndex, i.1=e ∧ x ∈ Set.range (E.chain i).path) ∨
        (∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p))) ∨
      x ∈ Set.range (endSpoke C v e) := by
  simp only [assembledEdge,Path.trans_range,Set.mem_union,anchoredMiddle_range,E.middlePath_range_iff]

end Paper170Geometry.PolygonalExterior

end
end

section

/-! The assembled replacement is an actual continuous drawing with simple, vertex-avoiding edges. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middlePath_avoids_vertices (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge)
    (j : Vertex) : v j ∉ Set.range (E.middlePath e) := by
  intro hx
  rcases (E.middlePath_range_iff e (v j)).mp hx with ⟨i,hi,⟨t,ht⟩⟩ | ⟨p,hp,hx⟩
  · exact E.avoids_new_vertices v hv i t j ht
  · exact Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks p j) hx (hv j).le

theorem assembledEdge_vertex_eq (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge)
    (j : Vertex) (hj : v j ∈ Set.range (E.assembledEdge v e)) :
    j=graph.src e ∨ j=graph.dst e := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hj
  rcases hj with (hj | hj) | hj
  · exact Or.inl (C.vertex_spoke_vertex_eq v hv _ j (C.startPortAt e) hj)
  · exact False.elim (E.middlePath_avoids_vertices v hv e j hj)
  · rw [endSpoke_range] at hj
    exact Or.inr (C.vertex_spoke_vertex_eq v hv _ j (C.endPortAt e) hj)

theorem assembledEdge_interior_avoids_vertices (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1)
    (j : Vertex) : E.assembledEdge v e t ≠ v j := by
  intro he
  rcases E.assembledEdge_vertex_eq v hv e j ⟨t,he⟩ with rfl | rfl
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).source.symm)
    exact ht.1.ne hh.symm
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).target.symm)
    exact ht.2.ne hh

def assembledDrawing (E : PolygonalExterior C) (v : Vertex → Plane)
    (hvinj : Function.Injective v) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) :
    Paper170.ContinuousDrawing graph where
  vertex := v
  vertex_injective := hvinj
  edge := E.assembledEdge v
  edge_injective := E.assembledEdge_injective v hv
  interior_avoids_vertices := E.assembledEdge_interior_avoids_vertices v hv

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Cross-edge incidence of the actual middle paths and exterior pieces. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middle_exterior_edge_eq (E : PolygonalExterior C) (e : Edge)
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
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
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

theorem middle_middle_meeting_chords (E : PolygonalExterior C) (e f : Edge)
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Every nonvertex intersection of assembled edges is an actual crossing-disk chord intersection. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_spoke_meeting (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e : Edge) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
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
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : Edge) (hef : e ≠ f) (x : Plane)
    (havoid : ∀ j, x ≠ v j) (hx : x ∈ Set.range (E.assembledEdge v e))
    (hy : x ∈ Set.range (E.assembledEdge v f)) :
    ∃ p q : C.InnerIndex, p.1=e ∧ q.1=f ∧
      x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q) := by
  have hm (a b : Edge) (hab : a ≠ b)
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
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    Paper170.crossingPoints (E.assembledDrawing v hvinj hv) ⊆ C.chordCrossings := by
  rintro x ⟨e,f,hef,⟨s,hs,he⟩,⟨t,ht,hf⟩⟩
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq))
    ⟨s,he⟩ ⟨t,hf⟩
  exact ⟨p,q,(fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))),hxp,hxq⟩

theorem assembled_crossings_finite (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    (Paper170.crossingPoints (E.assembledDrawing v hvinj hv)).Finite :=
  C.chordCrossings_finite.subset (E.assembled_crossings_subset v hvinj hv hdet)

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! No triple intersection is introduced by the actual replacement drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_no_triples (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f g : Edge) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e ∩
      Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f ∩
      Paper170.edgeInterior (E.assembledDrawing v hvinj hv) g=∅ := by
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Each actual boundary port belongs to exactly its assigned assembled edge. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_exterior_edge_eq (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (i : C.ArcIndex) (x : Plane)
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
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (p : C.Port)
    (hp : C.portPoint p ∈ Set.range (E.assembledEdge v e)) : e=p.1.1 :=
  E.assembled_exterior_edge_eq v hv e p.1 (C.portPoint p) hp (E.portPoint_mem_exterior p)

end Paper170Geometry.PolygonalExterior

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Polygonalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Admissible polygonal replacement and retention of crossing counts. -/

section

/-! Inside a crossing disk, an assembled edge has exactly its assigned straight chord trace. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_range_in_crossingDisk (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
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
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) p.1 ↔
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
end Paper170Geometry

end
end

section

/-! All admissibility conditions and spatial crossing-count nonincrease for the assembled drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_crossings_proper (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : Edge) (hef : e ≠ f) (x : Plane)
    (hx : x ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e)
    (hy : x ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f) :
    Paper170.ProperCrossing (Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e)
      (Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f) x := by
  obtain ⟨s,hs,he⟩ := hx
  obtain ⟨t,ht,hf⟩ := hy
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)) ⟨s,he⟩ ⟨t,hf⟩
  have hpq : p ≠ q := fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨hxin,hproper⟩ := C.crossingChord_meeting_proper p q hpq x hxp hxq
  constructor
  apply properCrossing_of_local_eq _ _ _ _ x hproper.chart_exists (C.crossingDisk p) (C.crossingDisk_isOpen p) hxin
  · intro z hz
    simpa only [hp] using (E.assembled_trace_in_crossingDisk v hvinj hv p z hz).symm
  · intro z hz
    have hzq : z ∈ C.crossingDisk q := by
      change squaredLength (z-(C.innerMark q).val) < C.radius^2
      rw [← hm]
      exact hz
    simpa only [hq] using (E.assembled_trace_in_crossingDisk v hvinj hv q z hzq).symm

def assembledAdmissible (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) : Paper170.AdmissibleDrawing graph where
  toContinuousDrawing := E.assembledDrawing v hvinj hv
  crossings_finite := E.assembled_crossings_finite v hvinj hv hdet
  crossings_proper := E.assembled_crossings_proper v hvinj hv hdet
  no_triples := E.assembled_no_triples v hvinj hv hdet

end PolygonalExterior
end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_GraphWalkRealizationLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

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
-- module Solutions.OAIQ4_Cc.Crossing_OrderedPathParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def OrderedPathPart {a b c d : Plane} (γ : Path a b) (δ : Path c d) : Prop :=
  ∃ f : unitInterval → unitInterval, StrictMono f ∧ ∀ t, γ (f t)=δ t

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentAugmentation
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

theorem segmentAugmentedGraph_added_adj {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) (i : ι) : (segmentAugmentedGraph G a b hne).Adj (a i) (b i) :=
  Or.inr ⟨i,Or.inl ⟨rfl,rfl⟩⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CrossingCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered crossing ports, surgery cut walks, path witnesses, and cut separation. -/

section

/-! The actual embedded surgery graph: exterior drawing tracks and two disjoint reconnection chords. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

theorem crossingSurgeryGraph_reconnection_adj (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) (i : Bool) :
    (crossingSurgeryGraph C P p q).Adj (C.reconnectionStart p q i) (C.reconnectionEnd p q i) :=
  segmentAugmentedGraph_added_adj _ _ _ _ i

end Paper170Geometry

end
end

section

/-! Exactly the two incident assembled edges can enter a chosen crossing disk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_in_crossingDisk_chord (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (p : C.InnerIndex) (x : Plane)
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
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hxin : x ∈ C.crossingDisk p) : e=p.1 ∨ e=q.1 := by
  obtain ⟨r,hr,hrm,hxr⟩ := E.assembled_in_crossingDisk_chord v hv e p x hx hxin
  rcases C.innerIndex_at_mark_pair p q r hpq hm hrm.symm with rfl | rfl
  · exact Or.inl hr.symm
  · exact Or.inr hr.symm

theorem assembled_other_edge_avoids_crossingDisk (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    Disjoint (Set.range (E.assembledEdge v e)) (C.crossingDisk p) := by
  apply Set.disjoint_left.mpr
  intro x hx hxin
  rcases E.assembled_crossingDisk_owner v hv p q hpq hm e x hx hxin with h | h
  · exact hep h
  · exact heq h

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Simple actual polygonal paths obtained from transferred tracks and one new chord. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem walkThroughChord_range {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) :
    Set.range (graphWalkPath id (walkThroughChord A h B))=
      (Set.range (graphWalkPath id A) ∪ segment ℝ u v) ∪ Set.range (graphWalkPath id B) := by
  rw [walkThroughChord,graphWalkPath_append_range,graphWalkPath_append_range,graphWalkPath_toWalk_range]

variable  {D D' : Paper170.AdmissibleDrawing graph}

theorem surgery_mixed_endpoints_ne (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (p q : C.InnerIndex) (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1) :
    D'.vertex (graph.src p.1) ≠ D'.vertex (graph.dst q.1) := by
  intro h
  have he := D'.vertex_injective h
  rcases hadj with hs | ht
  · exact graph.loopless q.1 (hs.symm.trans he)
  · exact graph.loopless p.1 (he.trans ht.symm)

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_AdjacentSurgery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reconnected paths and point-removing surgery on adjacent edges. -/

section

/-! The two actual switched walks, before loop deletion. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
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
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src p.1))) (D'.vertex ((graph.dst q.1))) :=
  walkThroughChord (Kp.prefixInSurgery p q rfl)
    surgery_forward_adj (Kq.suffixInSurgery p q hm.symm)

def reconnectedBackwardWalk (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src q.1))) (D'.vertex ((graph.dst p.1))) :=
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

end Paper170Geometry

end
end

section

/-! Actual simple polygonal paths extracted from the two switched walks. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def reconnectedForwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex ((graph.src p.1))) (D'.vertex ((graph.dst q.1))) := by
  classical
  exact graphWalkPath id (reconnectedForwardWalk Kp Kq hm).bypass

def reconnectedBackwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex ((graph.src q.1))) (D'.vertex ((graph.dst p.1))) := by
  classical
  exact graphWalkPath id (reconnectedBackwardWalk Kp Kq hm).bypass

theorem reconnectedForwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedForwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C p q hadj)
    _ (reconnectedForwardWalk Kp Kq hm).bypass_isPath

theorem reconnectedBackwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedBackwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C q p (hadj.imp Eq.symm Eq.symm))
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

end Paper170Geometry

end
end

section

/-! The selected spatial crossing point is absent from both actual bypassed paths. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
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

end Paper170Geometry

end
end

section

/-! The actual rerouted simple paths have vertex-avoiding interiors. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
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
    (j : Vertex) (hj : D'.vertex j ∈ Set.range (reconnectedForwardPath Kp Kq hm)) :
    j=(graph.src p.1) ∨ j=(graph.dst q.1) := by
  rcases reconnectedForwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kp.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv true j hj)
  · exact Or.inr (Kq.suffix_vertex_eq j hj)

theorem reconnectedBackwardPath_vertex_eq (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (j : Vertex) (hj : D'.vertex j ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    j=(graph.src q.1) ∨ j=(graph.dst p.1) := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kq.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv false j hj)
  · exact Or.inr (Kp.suffix_vertex_eq j hj)

theorem reconnectedForwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    reconnectedForwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedForwardPath_injective Kp Kq hm hadj hemb)
    (reconnectedForwardPath_vertex_eq Kp Kq hm hv) t ht j

theorem reconnectedBackwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    reconnectedBackwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedBackwardPath_injective Kp Kq hm hadj hemb)
    (reconnectedBackwardPath_vertex_eq Kp Kq hm hv) t ht j

end Paper170Geometry

end
end

section

/-! Assigning the two switched paths to the original edges for either shared endpoint. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def adjacentSurgeryRouteP (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1)) :
    Path (D'.vertex ((graph.src p.1))) (D'.vertex ((graph.dst p.1))) := by
  classical
  exact if h : (graph.src p.1)=(graph.src q.1) then (reconnectedBackwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (i)) h) rfl
  else (reconnectedForwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (j)) (hadj.resolve_left h))

def adjacentSurgeryRouteQ (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1)) :
    Path (D'.vertex ((graph.src q.1))) (D'.vertex ((graph.dst q.1))) := by
  classical
  exact if h : (graph.src p.1)=(graph.src q.1) then (reconnectedForwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (i)) h.symm) rfl
  else (reconnectedBackwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (j)) (hadj.resolve_left h).symm)

theorem adjacentSurgeryRouteP_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteP Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_injective Kp Kq hm hadj hemb
  · exact reconnectedForwardPath_injective Kp Kq hm hadj hemb

theorem adjacentSurgeryRouteQ_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_injective Kp Kq hm hadj hemb
  · exact reconnectedBackwardPath_injective Kp Kq hm hadj hemb

theorem adjacentSurgeryRouteP_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    adjacentSurgeryRouteP Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j

theorem adjacentSurgeryRouteQ_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    adjacentSurgeryRouteQ Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j

end Paper170Geometry

end
end

section

/-! An actual continuous drawing with the two adjacent routes replaced. Admissibility is a later theorem. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def adjacentSurgeryDrawing (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) : Paper170.ContinuousDrawing graph :=
  D'.toContinuousDrawing.replaceTwoEdges p.1 q.1
    (adjacentSurgeryRouteP Kp Kq hm hadj) (adjacentSurgeryRouteQ Kp Kq hm hadj)
    (adjacentSurgeryRouteP_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteQ_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteP_avoids_vertices Kp Kq hm hadj hv hemb)
    (adjacentSurgeryRouteQ_avoids_vertices Kp Kq hm hadj hv hemb)

theorem adjacentSurgeryDrawing_first (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge p.1=adjacentSurgeryRouteP Kp Kq hm hadj :=
  Paper170.ContinuousDrawing.replaceTwoRoutes_first _ _ _ _ _

theorem adjacentSurgeryDrawing_second (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge q.1=adjacentSurgeryRouteQ Kp Kq hm hadj :=
  Paper170.ContinuousDrawing.replaceTwoRoutes_second _ _ _ (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) _ _

theorem adjacentSurgeryDrawing_other (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e=D'.edge e :=
  Paper170.ContinuousDrawing.replaceTwoRoutes_other _ _ _ _ _ _ hep heq

end Paper170Geometry

end
end

section

/-! Polygonality and actual removal of the selected point from every new drawing route. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem adjacentSurgeryRoutes_avoid_crossing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
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
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
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

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cycle-space spanning, flows, simple cycles, and oriented darts. -/

section

/-! Directed traversals of the fixed edges of an arbitrary finite simple graph. -/
noncomputable section
namespace Paper170Geometry
variable {V E : Type} {G : Paper170.Graph V E}

def forwardDart (G : Paper170.Graph V E) (e : E) : OrientedDart G := ⟨e,true⟩

def backwardDart (G : Paper170.Graph V E) (e : E) : OrientedDart G := ⟨e,false⟩

def dartSign (d : OrientedDart G) : ℝ := if d.forward then 1 else -1

theorem dart_source_incident (d : OrientedDart G) :
    d.fst = G.src d.edge ∨ d.fst = G.dst d.edge := by
  cases d with
  | mk e b =>
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem dart_target_incident (d : OrientedDart G) :
    d.snd = G.src d.edge ∨ d.snd = G.dst d.edge := by
  cases d with
  | mk e b =>
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TriangleEntryExit
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
def triangleIndicator (a b c z : Plane) : ℝ :=
  ∏ i : Fin 3, positiveIndicator (orient2 (triangleStart a b c i) (triangleEnd a b c i) z)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TriangleTransversality
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
-- module Solutions.OAIQ4_Cc.Crossing_TriangleOrientations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

def orientedTriangleIndicator (a b c z : Plane) : ℝ :=
  if 0 < orient2 a b c then triangleIndicator a b c z else -triangleIndicator a c b z

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_GenericPolygonIntersection
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
-- module Solutions.OAIQ4_Cc.Crossing_PeriodicPolygon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def periodicPolygon (n : ℕ) (hn : 0 < n) (p : Fin n → Plane) (i : ℕ) : Plane := p (cyclicIndex n hn i)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ReducedPolygonalPresentation
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
-- module Solutions.OAIQ4_Cc.Crossing_OpenSegmentEndpoints
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
-- module Solutions.OAIQ4_Cc.Crossing_RadialBoundaryPorts
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
-- module Solutions.OAIQ4_Cc.Crossing_DrawingSpokePorts
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
-- module Solutions.OAIQ4_Cc.CompleteCrossing_SpokePorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chain pieces near vertices, incident spoke ports, and short vertex radii. -/

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem drawing_chain_pieces_pos (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e)))) :
    0 < P.pieces := by
  apply P.pieces_pos_of_ne
  intro h
  exact graph.loopless e (D.vertex_injective h)

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

instance incidentEdgesFintype [Fintype Edge] (j : Vertex) : Fintype (IncidentEdges graph j) := by
  classical
  unfold IncidentEdges
  infer_instance

def drawingSpokePort (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (r : ℝ) (j : Vertex) (e : IncidentEdges graph j) : Plane :=
  if j=graph.src e.val then (P e.val).startPort r else (P e.val).endPort r

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TruncatedChainVertices
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
-- module Solutions.OAIQ4_Cc.Crossing_TruncatedChainDirections
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
-- module Solutions.OAIQ4_Cc.Crossing_TruncatedChainPath
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
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Truncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex-disk truncation, retained crossings, reduced corners, and transverse segments. -/

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
structure VertexTruncation (D : Paper170.ContinuousDrawing graph) where
  chain : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
    (D.vertex ((graph.src e))) (D.vertex ((graph.dst e)))
  minimal : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
    (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (chain e).pieces ≤ Q.pieces
  radius : ℝ
  radius_pos : 0 < radius
  short : ∀ e, 4*radius^2 < squaredLength ((chain e).vertices 1-(chain e).vertices 0) ∧
    4*radius^2 < squaredLength ((chain e).vertices (chain e).pieces-(chain e).vertices ((chain e).pieces-1))
  disks_disjoint : ∀ j k, j ≠ k →
    Disjoint (closedRoundDisk (D.vertex j) radius) (closedRoundDisk (D.vertex k) radius)
  piece_clearance : ∀ j e (i : Fin (chain e).pieces),
    ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(chain e).pieces)) →
    Disjoint (closedRoundDisk (D.vertex j) radius)
      (segment ℝ ((chain e).vertices i.val) ((chain e).vertices (i.val+1)))

namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def pieces (e : Edge) : ℕ := (V.chain e).pieces

def vertices (e : Edge) : ℕ → Plane := (V.chain e).truncatedVertices V.radius

def startPort (e : Edge) : Plane := (V.chain e).startPort V.radius

def endPort (e : Edge) : Plane := (V.chain e).endPort V.radius

theorem pieces_pos (e : Edge) : 0 < V.pieces e := drawing_chain_pieces_pos D e (V.chain e)

theorem weak_short (e : Edge) :
    V.radius^2 < squaredLength ((V.chain e).vertices 1-(V.chain e).vertices 0) ∧
    V.radius^2 < squaredLength ((V.chain e).vertices (V.chain e).pieces-(V.chain e).vertices ((V.chain e).pieces-1)) := by
  constructor <;> nlinarith [(V.short e).1,(V.short e).2,sq_nonneg V.radius]

def path (e : Edge) : Path (V.startPort e) (V.endPort e) :=
  ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos (V.weak_short e).1 (V.weak_short e).2).path

end VertexTruncation

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleOffsetParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

def offsetParameter (a δ : ℝ) : ℝ :=
  (circleOffset (circlePoint a) δ).2/(1+(circleOffset (circlePoint a) δ).1)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleOffsetLine
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
-- module Solutions.OAIQ4_Cc.Crossing_CircleConnectors
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
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Tracks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Truncated spoke coordinates, endpoint connections, and stable signed track intersections. -/

section

/-! Fixed graph-edge directions at both endpoint circles, including the incoming right-vertex direction. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

def drawingSpokeDirection (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (j : Vertex) (e : IncidentEdges graph j) : Plane :=
  if j=(graph.src e.val) then trackDirection (P e.val).vertices 0
    else trackDirection (P e.val).vertices ((P e.val).pieces-1)

end Paper170Geometry

end
end

section

/-! The actual endpoint directions of truncated tracks, with their common fixed edge orientation. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def spokePort (j : Vertex) (e : IncidentEdges graph j) : Plane :=
  drawingSpokePort D V.chain V.radius j e

def spokeIndex (j : Vertex) (e : IncidentEdges graph j) : ℕ :=
  if j=(graph.src e.val) then 0 else V.pieces e.val-1

def spokeDirection (j : Vertex) (e : IncidentEdges graph j) : Plane :=
  trackDirection (V.vertices e.val) (V.spokeIndex j e)

def spokeScale (j : Vertex) (e : IncidentEdges graph j) : ℝ :=
  circleTrackScale (V.spokeDirection j e) (V.spokePort j e-D.vertex j)

end Paper170Geometry.VertexTruncation

end
end

section

/-! One actual oriented circle chart at each vertex, chosen before any cycle or pair of chords. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable {D : Paper170.ContinuousDrawing graph}

structure TruncatedSpokeCoordinates (V : VertexTruncation D) where
  frame : Vertex → Plane
  frame_ne_zero : ∀ j, frame j ≠ 0
  frame_length : ∀ j, squaredLength (frame j)=V.radius^2
  node : ∀ j, IncidentEdges graph j → ℝ
  node_injective : ∀ j, Function.Injective (node j)
  point_eq : ∀ j e, similarityPoint (D.vertex j) (frame j) (circlePoint (node j e))=V.spokePort j e

namespace TruncatedSpokeCoordinates
variable {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

def shiftedPort (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) : Plane :=
  similarityPoint (D.vertex j) (C.frame j)
    (circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε))

def tangentPort (_C : TruncatedSpokeCoordinates V) (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) : Plane :=
  V.spokePort j e+ε • normalShift (V.spokeDirection j e)

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! The ends of each actual shifted track are precisely the ends of its two circle connectors. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def leftIncident (_V : VertexTruncation D) (e : Edge) : IncidentEdges graph ((graph.src e)) := ⟨e,Or.inl rfl⟩
def rightIncident (_V : VertexTruncation D) (e : Edge) : IncidentEdges graph ((graph.dst e)) := ⟨e,Or.inr rfl⟩

theorem vertices_first (e : Edge) : V.vertices e 0=V.startPort e :=
  (V.chain e).truncatedVertices_first V.radius

theorem vertices_last (e : Edge) : V.vertices e (V.pieces e)=V.endPort e :=
  (V.chain e).truncatedVertices_last (V.pieces_pos e) V.radius

theorem shiftedTrack_first (C : TruncatedSpokeCoordinates V) (e : Edge) (ε : ℝ) :
    shiftedTrack (V.vertices e) (V.pieces e) ε 0=
      C.tangentPort ((graph.src e)) (V.leftIncident e) ε := by
  simp [shiftedTrack,trackOffset,TruncatedSpokeCoordinates.tangentPort,spokeDirection,
    spokeIndex,leftIncident,V.vertices_first,spokePort,drawingSpokePort,startPort]

theorem shiftedTrack_last (C : TruncatedSpokeCoordinates V) (e : Edge) (ε : ℝ) :
    shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)=
      C.tangentPort ((graph.dst e)) (V.rightIncident e) ε := by
  have hn : V.pieces e ≠ 0 := ne_of_gt (V.pieces_pos e)
  simp [shiftedTrack,trackOffset,hn,TruncatedSpokeCoordinates.tangentPort,spokeDirection,
    spokeIndex,rightIncident,V.vertices_last,spokePort,drawingSpokePort,endPort,(graph.loopless e).symm]

end Paper170Geometry.VertexTruncation

end
end

section

/-! Signed intersections are actual segment-traversal sums; their support is controlled by spatial crossing points. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
open scoped BigOperators
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def signedIntersection (e f : Edge) : ℝ :=
  if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f)

end Paper170Geometry.VertexTruncation

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChainComposition
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
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChainTransversality
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
-- module Solutions.OAIQ4_Cc.Crossing_FinitePolygonalComposition
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
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalEndpointCasts
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
-- module Solutions.OAIQ4_Cc.CompleteCrossing_DartPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Drawn-edge chains, dart-path realizations, and endpoint-flag pairing. -/

section

/-! Incident flags of an oriented traversal in an arbitrary finite simple graph. -/
noncomputable section
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

instance instFintypeOrientedDart [Fintype Edge] : Fintype (OrientedDart graph) :=
  Fintype.ofEquiv (Edge × Bool)
    { toFun := fun p => ⟨p.1,p.2⟩
      invFun := fun d => (d.edge,d.forward)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def dartSourceIncident (d : OrientedDart graph) : IncidentEdges graph d.fst :=
  ⟨d.edge,dart_source_incident d⟩

def dartTargetIncident (d : OrientedDart graph) : IncidentEdges graph d.snd :=
  ⟨d.edge,dart_target_incident d⟩

end Paper170Geometry

end
end

section

/-! Actual edge paths between vertex circles, and actual shifted paths with both exterior connectors. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def trackChain (e : Edge) : PolygonalChain Set.univ (V.startPort e) (V.endPort e) where
  pieces := V.pieces e
  vertices := V.vertices e
  first := V.vertices_first e
  last := V.vertices_last e
  start_mem := Set.mem_univ _
  inside := fun _ _ => Set.subset_univ _

def chordChain (j : Vertex) (a b : IncidentEdges graph j) :
    PolygonalChain Set.univ (V.spokePort j a) (V.spokePort j b) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

def shiftedTrackChain (e : Edge) (ε : ℝ) :
    PolygonalChain Set.univ (C.tangentPort ((graph.src e)) (V.leftIncident e) ε)
      (C.tangentPort ((graph.dst e)) (V.rightIncident e) ε) where
  pieces := V.pieces e
  vertices := shiftedTrack (V.vertices e) (V.pieces e) ε
  first := V.shiftedTrack_first C e ε
  last := V.shiftedTrack_last C e ε
  start_mem := Set.mem_univ _
  inside := fun _ _ => Set.subset_univ _

def connectorChain (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort j e ε) (C.tangentPort j e ε) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

def shiftedEdgeChain (e : Edge) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort ((graph.src e)) (V.leftIncident e) ε)
      (C.shiftedPort ((graph.dst e)) (V.rightIncident e) ε) :=
  ((C.connectorChain ((graph.src e)) (V.leftIncident e) ε).join (C.shiftedTrackChain e ε)).join
    (C.connectorChain ((graph.dst e)) (V.rightIncident e) ε).reverse

def shiftedChordChain (j : Vertex) (a b : IncidentEdges graph j) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort j a ε) (C.shiftedPort j b ε) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! Actual polygonal realizations of the two orientations of every graph edge. -/
noncomputable section
open Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def dartTrackChain (d : OrientedDart graph) :
    PolygonalChain Set.univ (V.spokePort d.fst (dartSourceIncident d))
      (V.spokePort d.snd (dartTargetIncident d)) := by
  rcases d with ⟨e,b⟩
  cases b
  · exact (V.trackChain e).reverse.castEndpoints
      (by simp [spokePort,drawingSpokePort,dartSourceIncident,OrientedDart.fst,
        endPort,(graph.loopless e).symm])
      (by simp [spokePort,drawingSpokePort,dartTargetIncident,OrientedDart.snd,startPort])
  · exact (V.trackChain e).castEndpoints
      (by simp [spokePort,drawingSpokePort,dartSourceIncident,OrientedDart.fst,startPort])
      (by simp [spokePort,drawingSpokePort,dartTargetIncident,OrientedDart.snd,
        endPort,(graph.loopless e).symm])

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

def shiftedDartChain (d : OrientedDart graph) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort d.fst (dartSourceIncident d) ε)
      (C.shiftedPort d.snd (dartTargetIncident d) ε) := by
  rcases d with ⟨e,b⟩
  cases b
  · exact (C.shiftedEdgeChain e ε).reverse.castEndpoints rfl rfl
  · exact (C.shiftedEdgeChain e ε).castEndpoints rfl rfl

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! Actual closed polygonal realizations of cyclic graph darts, with a chord at every vertex passage. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

def incidentCast {j k : Vertex} (h : j=k) (e : IncidentEdges graph j) : IncidentEdges graph k :=
  ⟨e.val,by simpa only [← h] using e.property⟩

def dartPassageNext (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) : IncidentEdges graph (d i).snd :=
  incidentCast (hd i).symm (dartSourceIncident (d (i+1)))

namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem spokePort_cast {j k : Vertex} (h : j=k) (e : IncidentEdges graph j) :
    V.spokePort k (incidentCast h e)=V.spokePort j e := by subst k; rfl

def dartCycleVertex (d : ℕ → OrientedDart graph) (i : ℕ) : Plane :=
  V.spokePort (d i).fst (dartSourceIncident (d i))

def dartCycleBlock (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) :
    PolygonalChain Set.univ (V.dartCycleVertex d i) (V.dartCycleVertex d (i+1)) :=
  ((V.dartTrackChain (d i)).join
    (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).castEndpoints
      rfl (V.spokePort_cast (hd i).symm _).symm

def dartCycleChain (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (N : ℕ) (hN : d N=d 0) :
    PolygonalChain Set.univ (V.dartCycleVertex d 0) (V.dartCycleVertex d 0) :=
  (finitePolygonalChain Set.univ (V.dartCycleVertex d) (Set.mem_univ _) (V.dartCycleBlock d hd) N).castEndpoints
    rfl (congrArg (fun a : OrientedDart graph => V.spokePort a.fst (dartSourceIncident a)) hN.symm)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

theorem shiftedPort_cast {j k : Vertex} (h : j=k) (e : IncidentEdges graph j) (ε : ℝ) :
    C.shiftedPort k (incidentCast h e) ε=C.shiftedPort j e ε := by subst k; rfl

def shiftedCycleVertex (d : ℕ → OrientedDart graph) (ε : ℝ) (i : ℕ) : Plane :=
  C.shiftedPort (d i).fst (dartSourceIncident (d i)) ε

def shiftedCycleBlock (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (ε : ℝ) (i : ℕ) :
    PolygonalChain Set.univ (C.shiftedCycleVertex d ε i) (C.shiftedCycleVertex d ε (i+1)) :=
  ((C.shiftedDartChain (d i) ε).join
    (C.shiftedChordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i) ε)).castEndpoints
      rfl (C.shiftedPort_cast (hd i).symm _ ε).symm

def shiftedCycleChain (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (N : ℕ) (hN : d N=d 0) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedCycleVertex d ε 0) (C.shiftedCycleVertex d ε 0) :=
  (finitePolygonalChain Set.univ (C.shiftedCycleVertex d ε) (Set.mem_univ _) (C.shiftedCycleBlock d hd ε) N).castEndpoints
    rfl (congrArg (fun a : OrientedDart graph => C.shiftedPort a.fst (dartSourceIncident a) ε) hN.symm)

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! Endpoint pairings at actual vertex-circle passages. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def vertexChordPairing (j k : Vertex) (a b : IncidentEdges graph j) (c d : IncidentEdges graph k) : ℝ :=
  if h : k=j then chordEndpointPairing (C.node j a) (C.node j b)
    (C.node j (incidentCast h c)) (C.node j (incidentCast h d)) else 0

def passagePairing (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (i j : ℕ) : ℝ :=
  C.vertexChordPairing (d i).snd (f j).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)
    (dartTargetIncident (f j)) (dartPassageNext f hf j)

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Fixed vertex half-order kernels on actual incident edge flags. -/
noncomputable section
open Zarankiewicz
open scoped Classical
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

def dartSourceFlag (d : OrientedDart graph) : IncidentFlag graph :=
  ⟨d.fst,dartSourceIncident d⟩

def dartTargetFlag (d : OrientedDart graph) : IncidentFlag graph :=
  ⟨d.snd,dartTargetIncident d⟩

namespace TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def flagPairing (a b : IncidentFlag graph) : ℝ :=
  if h : b.1=a.1 then orderSign (C.node a.1 a.2) (C.node a.1 (incidentCast h b.2))/2 else 0

def edgeEndpointPairing (e f : Edge) : ℝ :=
  C.flagPairing (dartTargetFlag (forwardDart graph e)) (dartTargetFlag (forwardDart graph f))-
    C.flagPairing (dartTargetFlag (forwardDart graph e)) (dartSourceFlag (forwardDart graph f))-
    C.flagPairing (dartSourceFlag (forwardDart graph e)) (dartTargetFlag (forwardDart graph f))+
    C.flagPairing (dartSourceFlag (forwardDart graph e)) (dartSourceFlag (forwardDart graph f))

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CycleIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed dart and cycle intersections, passage pairing, and endpoint averaging. -/

section

/-! Every actual cycle-block intersection splits into its edge term and its vertex-chord term. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

namespace TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def passageIntersection (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (i j : ℕ) (ε : ℝ) : ℝ :=
  polygonIntersection (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)).vertices
    (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε).vertices 1 1

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! Every local passage endpoint is counted once at the corresponding graph-edge endpoint. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped BigOperators
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def cycleIntersectionMatrix : Edge → Edge → ℝ :=
  fun e f => V.signedIntersection e f+C.edgeEndpointPairing e f

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_SurgeryIntersections
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Surgery intersection containment, strict crossing reduction, and admissibility. -/

section

/-! Actual new chords cannot meet any third normalized edge, including at ports. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

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
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_port_not_mem_other_edge (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (r : C.Port) (her : e ≠ r.1.1) :
    C.portPoint r ∉ Set.range (E.assembledEdge v e) :=
  fun hx => her (E.assembled_port_unique_edge v hv e r hx)

theorem reconnection_other_edge_disjoint (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (i : Bool) (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1) :
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
end Paper170Geometry

end
end

section

/-! Each new chord avoids the retained cuts assigned to the other switched walk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Exact retained-track cases for intersections of the two actual rerouted paths. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Every contact of rerouted edges is carried by the original drawing tracks. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem reconnectedForwardPath_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1)
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
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · exact Or.inr (Kq.prefix_subset_edge hx)
  · exact False.elim (Set.disjoint_left.mp (E.reconnection_other_edge_disjoint v hv p q hpq hm false e hep heq) hx hy)
  · exact Or.inl (Kp.suffix_subset_edge hx)

theorem adjacentSurgeryRoutes_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1)
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
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
    (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∧ x ∈ Set.range (E.assembledEdge v q.1) := by
  have hh := E.reconnected_paths_meeting_old_edges v hvinj hv hdet P Kp Kq hpq hm hcross x
  by_cases h : (graph.src p.1)=(graph.src q.1)
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dite_eq_left h] at hx hy
    exact hh hy hx
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dite_eq_right h] at hx hy
    exact hh hx hy

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Every actual spatial crossing of the surgery drawing was already a crossing before surgery. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem adjacentSurgeryDrawing_crossings_subset
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) ⊆
      Paper170.crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
  let B := (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  intro x hx
  obtain ⟨e,f,hef,hxe,hxf⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hpair (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) : x ∈ Paper170.crossingPoints B := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hx hy
    exact crossing_of_ranges_not_vertices B p.1 q.1
      (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) x hh.1 hh.2 havoid
  have hmixed (g : Edge) (hgp : g ≠ p.1) (hgq : g ≠ q.1)
      (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (hy : x ∈ Set.range (B.edge g)) : x ∈ Paper170.crossingPoints B := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj g hgp hgq x hx hy with h | h
    · exact crossing_of_ranges_not_vertices B p.1 g (Ne.symm hgp) x h hy havoid
    · exact crossing_of_ranges_not_vertices B q.1 g (Ne.symm hgq) x h hy havoid
  have hcases (g : Edge) (hg : x ∈ Set.range (A.edge g)) :=
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! A strict decrease of the actual spatial crossing set; properness of the new drawing is still separate. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  {p q : C.InnerIndex}

theorem crossingChord_meeting_is_assembled_crossing (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ Paper170.crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
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
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    (Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).Finite ∧
      (Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).ncard <
        (Paper170.crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing).ncard := by
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  have hsub := E.adjacentSurgeryDrawing_crossings_subset v hvinj hv hdet P Kp Kq hpq hm hadj hcross hemb
  have hfinite := (E.assembledAdmissible v hvinj hv hdet).crossings_finite
  have hremoved := adjacentSurgeryDrawing_avoids_crossing Kp Kq hm hpq hadj hv hemb x hxp hxq (by
    intro e hep heq hx
    exact Set.disjoint_left.mp (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
      hx (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1)
  have hnot : x ∉ Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) := by
    rintro ⟨e,f,hef,hxe,hxf⟩
    exact hremoved e (edgeInterior_subset_range _ e hxe)
  refine ⟨hfinite.subset hsub,Set.ncard_lt_ncard ⟨hsub,?_⟩ hfinite⟩
  intro hrev
  exact hnot (hrev (E.crossingChord_meeting_is_assembled_crossing v hvinj hv hdet hpq x hxp hxq))

end Paper170Geometry.PolygonalExterior

end
end

section

/-! The actual surgery drawing has no triple interior contacts. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem adjacentSurgeryDrawing_no_triples
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e f g : Edge) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    Paper170.edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) e ∩
      Paper170.edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) f ∩
      Paper170.edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) g = ∅ := by
  let B := E.assembledAdmissible v hvinj hv hdet
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨⟨hxe,hxf⟩,hxg⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hthree (a b c : Edge) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b))
      (hc : x ∈ Set.range (B.edge c)) : False := by
    have hmem : x ∈ Paper170.edgeInterior B.toContinuousDrawing a ∩ Paper170.edgeInterior B.toContinuousDrawing b ∩
        Paper170.edgeInterior B.toContinuousDrawing c :=
      ⟨⟨edgeInterior_of_range_not_vertices _ a x ha havoid,
        edgeInterior_of_range_not_vertices _ b x hb havoid⟩,edgeInterior_of_range_not_vertices _ c x hc havoid⟩
    rw [B.no_triples a b c hab hac hbc] at hmem
    exact hmem
  have htwo (a : Edge) (hap : a ≠ p.1) (haq : a ≠ q.1)
      (hp : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hq : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) : False := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hp hq
    exact hthree p.1 q.1 a (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm))
      (Ne.symm hap) (Ne.symm haq) hh.1 hh.2 ha
  have hone (a b : Edge) (hab : a ≠ b)
      (hap : a ≠ p.1) (haq : a ≠ q.1) (hbp : b ≠ p.1) (hbq : b ≠ q.1)
      (hh : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b)) : False := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj a hap haq x hh ha with hp | hq
    · exact hthree p.1 a b (Ne.symm hap) (Ne.symm hbp) hab hp ha hb
    · exact hthree q.1 a b (Ne.symm haq) (Ne.symm hbq) hab hq ha hb
  have hcases (a : Edge) (ha : x ∈ Set.range (A.edge a)) :=
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! The constructed surgery drawing satisfies exactly the proved weaker normalization input. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

def adjacentSurgeryFiniteDrawing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    FiniteIntersectionDrawing graph where
  toContinuousDrawing := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  crossings_finite := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).1
  no_triples := E.adjacentSurgeryDrawing_no_triples v hvinj hv hdet P Kp Kq hpq hm hadj
    (C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq) hemb

end Paper170Geometry.PolygonalExterior

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_Bivariate
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

def BiBounded (r s : ℕ) (p : BiPoly) : Prop :=
  Bounded r p ∧ ∀ a, Bounded s (p.coeff a)

def swapBi : BiPoly ≃ₗ[ℝ] BiPoly :=
  (flattenBi.trans (Finsupp.mapDomain.linearEquiv ℝ ℝ (Equiv.prodComm ℕ ℕ))).trans
    flattenBi.symm

end Zarankiewicz

end

end OAI
end



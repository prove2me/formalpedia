-- Prove2me | Definitions.Def_OAIQ4Cc000
-- name    : OAIQ4Cc000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T04:38:58.070506+00:00
-- url     : https://prove2.me/theorems/71065e16-b36d-45ed-9ace-8caf36850ade
-- title:
--   Definitions bundle OAIQ4Cc000 of the split of OpenAI, The crossing number of complete graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Paper170.complete_graph_crossing_number`, carved from OpenAI's openai/math development (OpenAI, *The crossing number of complete graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 567 declarations of OpenAI's Lean: 239 definitions, 20 inductive types or structures, 2 instances and 306 theorems. The definitions and types are `OAI.Paper170.AdmissibleDrawing.castGraph`, `OAI.Paper170.AdmissibleDrawing.reorient`, `OAI.Paper170.AdmissibleDrawing.toFiniteIntersectionDrawing`, `OAI.Paper170.AffineCoverData`, `OAI.Paper170.AffineCoverData.segment`, `OAI.Paper170.AffineCoverData.trans`, `OAI.Paper170.BoundedExponents`, `OAI.Paper170.CircleConfiguration`, `OAI.Paper170.ContinuousDrawing.reorient`, `OAI.Paper170.ContinuousDrawing.reorientedPath`, `OAI.Paper170.ContinuousDrawing.replaceTwoEdges`, `OAI.Paper170.ContinuousDrawing.replaceTwoRoutes`, `OAI.Paper170.CrossingTensor`, `OAI.Paper170.CyclicRecord`, `OAI.Paper170.EvenTriangleCoord`, `OAI.Paper170.FlowVertex`, `OAI.Paper170.Graph.IncidentEdge`, `OAI.Paper170.Graph.reorient`, `OAI.Paper170.NormalizedDrawing`, `OAI.Paper170.Poly2`, `OAI.Paper170.Poly4`, `OAI.Paper170.PolygonalParametrization`, `OAI.Paper170.PolygonalParametrization.cast`, `OAI.Paper170.PolygonalParametrization.vertices`, `OAI.Paper170.SimpleCycle`, `OAI.Paper170.SimpleCycle.cyclicDart`, `OAI.Paper170.SimpleCycle.dart`, `OAI.Paper170.SimpleCycle.edgeChain`, `OAI.Paper170.SimpleCycle.modIndex`, `OAI.Paper170.SimpleCycle.next`, `OAI.Paper170.SpokeOrders`, `OAI.Paper170.SupportCoord`, `OAI.Paper170.SymmetricCoordinate`, `OAI.Paper170.TwoPageDrawing`, `OAI.Paper170.VertexDeletion`, `OAI.Paper170.angleCoordinateFrame`, `OAI.Paper170.angleRotation`, `OAI.Paper170.boundary`, `OAI.Paper170.boundaryLinear`, `OAI.Paper170.box4` and 219 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/CompleteCrossing, in whole or in part: `CompleteCrossing_AdjacentSurgery`, `CompleteCrossing_AlgebraDefs`, `CompleteCrossing_Angles`, `CompleteCrossing_Assembly`, `CompleteCrossing_CircleArcs`, `CompleteCrossing_CirclePlacement`, `CompleteCrossing_Counting`, `CompleteCrossing_CrossingCuts`, `CompleteCrossing_CycleSpace`, `CompleteCrossing_DartPaths`, `CompleteCrossing_Deletion`, `CompleteCrossing_DiskChords`, `CompleteCrossing_DiskFilling`, `CompleteCrossing_Drawing`, `CompleteCrossing_DrawingMarks`, `CompleteCrossing_Hill`, `CompleteCrossing_Interpolation`, `CompleteCrossing_Isotropy`, `CompleteCrossing_LocalGeometry`, `CompleteCrossing_Normalization`, `CompleteCrossing_OrderPairing`, `CompleteCrossing_PairSums`, `CompleteCrossing_Plane`, `CompleteCrossing_Polygonalization`, `CompleteCrossing_Polynomials`, `CompleteCrossing_Ports`, `CompleteCrossing_Reconnection`, `CompleteCrossing_Residues`, `CompleteCrossing_SpokePorts`, `CompleteCrossing_Subdivision`, `CompleteCrossing_Support`, `CompleteCrossing_Tensor`, `CompleteCrossing_Triangle`, `CompleteCrossing_TwoPage`, `CompleteCrossing_VertexEvaluation`, `Crossing_AffinePathHalves`, `Crossing_AlternatingPaths`, `Crossing_Bivariate`, `Crossing_ChordTransversality`, `Crossing_CircleChords`, `Crossing_CircleOffset`, `Crossing_CrossingCoordinates`, `Crossing_CrossingReconnection`, `Crossing_DiskPassage`, `Crossing_DrawingDefinition`, `Crossing_DrawingWalkCutTraces`, `Crossing_EmbeddedGraphPaths`, `Crossing_ExteriorSegmentGraph`, `Crossing_FiniteDiskCollar`, `Crossing_GraphSequenceWalk`, `Crossing_GraphWalkRealizationLaws`, `Crossing_GraphWalkTrace`, `Crossing_IntervalSegments`, `Crossing_NodeMoments`, `Crossing_OffsetTrack`, `Crossing_OffsetVectors`, `Crossing_OrderedPassages`, `Crossing_OrientedSimilarity`, `Crossing_ParallelDirection`, `Crossing_PathConcatenationInjective`, `Crossing_PathSubarc`, `Crossing_PlanarDeterminant`, `Crossing_PlanarSegments`, `Crossing_PolygonComposition`, `Crossing_PolygonalArcInjective`, `Crossing_PolygonalChainExistence`, `Crossing_PolygonalChainOperations`, `Crossing_PolygonalChains`, `Crossing_PolygonalParametrization`, `Crossing_ProperCrossingLocality`, `Crossing_ProperSegmentCrossing`, `Crossing_RadialExterior`, `Crossing_ReconnectedVertexAvoidance`, `Crossing_RoundCircleChords`, `Crossing_RoundDiskClearance`, `Crossing_SegmentAugmentation`, `Crossing_SegmentContinuity`, `Crossing_SegmentCrossingCoordinates`, `Crossing_SegmentIntersectionUnique`, `Crossing_SegmentParameters`, `Crossing_SegmentSides`, `Crossing_SegmentSymmetries`, `Crossing_SubdivisionSegments`, `Crossing_VertexDiskSpokes`.
--
--   **Imports.** It imports the published bundle `Def_CompleteCrossing`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ4Cc002`; the statement `OAI.Paper170.polygonal_no_adjacent_normalization`.
-- source:
--   OpenAI, The crossing number of complete graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/CompleteCrossing at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_CompleteCrossing

section
-- module Solutions.OAIQ4_Cc.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_DrawingDefinition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

abbrev Plane := ℝ × ℝ

def ProperCrossing (A B : Set Plane) (x : Plane) : Prop :=
  ∃ chart : OpenPartialHomeomorph Plane Plane,
    x ∈ chart.source ∧ chart x = (0,0) ∧
    chart '' (chart.source ∩ A) = chart.target ∩ {y | y.2 = 0} ∧
    chart '' (chart.source ∩ B) = chart.target ∩ {y | y.1 = 0}

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Drawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous graph drawings, proper spatial crossings, incidence, and endpoint properties. -/

section

/-!

The coordinate plane has its usual topology; every Euclidean circle below is
specified by squaredLength, not by the product norm.
-/

noncomputable section
open Set
open scoped BigOperators Classical

namespace Paper170

def squaredLength (x : Plane) : ℝ := x.1 ^ 2 + x.2 ^ 2

def det2 (x y : Plane) : ℝ := x.1 * y.2 - x.2 * y.1

def segmentPoint (a b : Plane) (t : ℝ) : Plane := (1 - t) • a + t • b

instance instFintypeCompleteEdge (n : ℕ) : Fintype (CompleteEdge n) := Fintype.ofFinite _

variable {V E : Type} (G : Graph V E)

namespace Graph

abbrev IncidentEdge (v : V) := {e : E // G.src e = v ∨ G.dst e = v}

end Graph

variable {G}

/-- A finite affine parametrization of the actual path. -/
structure PolygonalParametrization {a b : Plane} (γ : Path a b) where
  pieces : ℕ
  positive : 0 < pieces
  knot : Fin (pieces + 1) → unitInterval
  increasing : StrictMono knot
  first : knot 0 = 0
  last : knot (Fin.last pieces) = 1
  affine : ∀ i : Fin pieces, ∀ t : unitInterval,
    knot i.castSucc ≤ t → t ≤ knot i.succ →
    γ t = segmentPoint (γ (knot i.castSucc)) (γ (knot i.succ))
      (((t : ℝ) - knot i.castSucc) / ((knot i.succ : ℝ) - knot i.castSucc))

def PolygonalParametrization.vertices {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (i : ℕ) : Plane :=
  γ (P.knot ⟨min i P.pieces, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)

/-- A convenient subdivision of a normalized drawing. Avoiding subdivision
knots at crossings is additional presentation data, obtained by the normalization theorem. -/
structure NormalizedDrawing (G : Graph V E) extends AdmissibleDrawing G where
  polygonal : ∀ e, PolygonalParametrization (edge e)
  no_adjacent : ∀ e f, e ≠ f →
    (G.src e = G.src f ∨ G.src e = G.dst f ∨ G.dst e = G.src f ∨ G.dst e = G.dst f) →
    Disjoint (edgeInterior toContinuousDrawing e) (edgeInterior toContinuousDrawing f)
  crossings_not_knots : ∀ e (i : Fin ((polygonal e).pieces + 1)),
    edge e ((polygonal e).knot i) ∉ crossingPoints toContinuousDrawing

/-- Directed open-segment intersection, with the ordinary determinant sign. -/
def segmentIntersection (a b c d : Plane) : ℝ :=
  if ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1,
      segmentPoint a b s = segmentPoint c d t then
    if 0 < det2 (b - a) (d - c) then 1
    else if det2 (b - a) (d - c) < 0 then -1 else 0
  else 0

def interiorIntersection (N : NormalizedDrawing G) (e f : E) : ℝ :=
  if e = f then 0 else
    ∑ i ∈ Finset.range (N.polygonal e).pieces,
      ∑ j ∈ Finset.range (N.polygonal f).pieces,
        segmentIntersection ((N.polygonal e).vertices i) ((N.polygonal e).vertices (i + 1))
          ((N.polygonal f).vertices j) ((N.polygonal f).vertices (j + 1))

def outwardSpoke (N : NormalizedDrawing G) (v : V) (e : E) : Plane :=
  if G.src e = v then (N.polygonal e).vertices 1 - (N.polygonal e).vertices 0
  else (N.polygonal e).vertices ((N.polygonal e).pieces - 1) -
    (N.polygonal e).vertices (N.polygonal e).pieces

def spokeAngle (cut : ℝ) (a : Plane) : ℝ :=
  Complex.arg (Complex.exp (-(cut : ℂ) * Complex.I) * (⟨a.1, a.2⟩ : ℂ))

/-- The linear local orders are witnessed by the actual counterclockwise angles,
with a cut in a gap. No intersection identity is part of this data. -/
structure SpokeOrders (N : NormalizedDrawing G) where
  cut : V → ℝ
  order : ∀ v, LinearOrder (G.IncidentEdge v)
  cut_avoids : ∀ v (e : G.IncidentEdge v), spokeAngle (cut v) (outwardSpoke N v e.val) ≠ Real.pi
  compatible : ∀ v (e f : G.IncidentEdge v),
    @LT.lt _ (order v).toLT e f ↔
      spokeAngle (cut v) (outwardSpoke N v e.val) <
        spokeAngle (cut v) (outwardSpoke N v f.val)

def endpointSign (G : Graph V E) (v : V) (e : E) : ℝ :=
  if G.src e = v then 1 else if G.dst e = v then -1 else 0

def spokeComparison {N : NormalizedDrawing G} (O : SpokeOrders N) (v : V) (e f : E) : ℝ :=
  if he : G.src e = v ∨ G.dst e = v then if hf : G.src f = v ∨ G.dst f = v then
    if @LT.lt _ (O.order v).toLT ⟨e, he⟩ ⟨f, hf⟩ then 1
    else if @LT.lt _ (O.order v).toLT ⟨f, hf⟩ ⟨e, he⟩ then -1 else 0
  else 0 else 0

variable [Fintype V] [Fintype E]

def cycleIntersection {N : NormalizedDrawing G} (O : SpokeOrders N) (e f : E) : ℝ :=
  interiorIntersection N e f + (1 / 2 : ℝ) *
    ∑ v, endpointSign G v e * endpointSign G v f * spokeComparison O v e f

def edgePairing (J : E → E → ℝ) (z z' : E → ℝ) : ℝ :=
  ∑ e, ∑ f, z e * z' f * J e f

def boundary (G : Graph V E) (z : E → ℝ) (v : V) : ℝ :=
  ∑ e, z e * ((if G.dst e = v then 1 else 0) - (if G.src e = v then 1 else 0))

def completeEdgeVector {n : ℕ} (i p : Fin n) : CompleteEdge n → ℝ :=
  fun e => if e.val.1 = i ∧ e.val.2 = p then 1
    else if e.val.1 = p ∧ e.val.2 = i then -1 else 0

def rawCycleIntersection {n : ℕ} {N : NormalizedDrawing (completeGraph n)}
    (O : SpokeOrders N) (i p k q : Fin n) : ℝ :=
  edgePairing (cycleIntersection O) (completeEdgeVector i p) (completeEdgeVector k q)

/-- A simple combinatorial cycle with a chosen direction of traversal. -/
structure SimpleCycle (G : Graph V E) where
  length : ℕ
  three_le : 3 ≤ length
  vertex : Fin length → V
  vertex_injective : Function.Injective vertex
  edge : Fin length → E
  follows : ∀ i,
    let j : Fin length := ⟨(i.val + 1) % length,
      Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0 < 3) three_le)⟩
    (G.src (edge i) = vertex i ∧ G.dst (edge i) = vertex j) ∨
      (G.dst (edge i) = vertex i ∧ G.src (edge i) = vertex j)

def SimpleCycle.edgeChain (C : SimpleCycle G) : E → ℝ :=
  fun e => ∑ i, if C.edge i = e then (if G.src e = C.vertex i then 1 else -1) else 0

def inversion (z : Plane) : Plane := (z.1 / squaredLength z, z.2 / squaredLength z)

end Paper170

end
end

section

/-! Converting actual nonvertex trace contacts to the exact crossing-point definition. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem edgeInterior_subset_range (D : Paper170.ContinuousDrawing graph) (e : Edge) :
    Paper170.edgeInterior D e ⊆ Set.range (D.edge e) := by
  rintro x ⟨t,_,he⟩
  exact ⟨t,he⟩

theorem edgeInterior_of_range_not_vertices (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hvertex : ∀ j, x ≠ D.vertex j) :
    x ∈ Paper170.edgeInterior D e := by
  obtain ⟨t,he⟩ := hx
  have ht0 : t ≠ 0 := by
    intro ht
    subst t
    exact hvertex _ (he.symm.trans (D.edge e).source)
  have ht1 : t ≠ 1 := by
    intro ht
    subst t
    exact hvertex _ (he.symm.trans (D.edge e).target)
  exact ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,he⟩

theorem edgeInterior_not_vertex (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (x : Plane) (hx : x ∈ Paper170.edgeInterior D e) (j : Vertex) : x ≠ D.vertex j := by
  obtain ⟨t,ht,he⟩ := hx
  exact fun hj => D.interior_avoids_vertices e t ht j (he.trans hj)

end Paper170Geometry

end
end

section

namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

theorem drawing_edge_vertex_parameter (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (t : unitInterval) (v : Vertex) (he : D.edge e t=D.vertex v) :
    (t=0 ∧ v=(graph.src e)) ∨ (t=1 ∧ v=(graph.dst e)) := by
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨rfl,(D.vertex_injective ((D.edge e).source.symm.trans he)).symm⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inr ⟨rfl,(D.vertex_injective ((D.edge e).target.symm.trans he)).symm⟩
  exact False.elim (D.interior_avoids_vertices e t
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩ v he)

end Paper170Geometry

end

section

/-! A weaker INPUT for normalization: actual simple routes with finite contacts and no triples.
The endpoint's Paper170.AdmissibleDrawing and MainTarget definitions are unchanged. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

structure FiniteIntersectionDrawing (graph : Paper170.Graph Vertex Edge) extends Paper170.ContinuousDrawing graph where
  crossings_finite : (Paper170.crossingPoints toContinuousDrawing).Finite
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    Paper170.edgeInterior toContinuousDrawing e ∩ Paper170.edgeInterior toContinuousDrawing f ∩
      Paper170.edgeInterior toContinuousDrawing g = ∅

abbrev toFiniteIntersectionDrawing  (D : Paper170.AdmissibleDrawing graph) :
    FiniteIntersectionDrawing graph where
  toContinuousDrawing := D.toContinuousDrawing
  crossings_finite := D.crossings_finite
  no_triples := D.no_triples

instance admissibleToFiniteIntersectionDrawing  :
    CoeOut (Paper170.AdmissibleDrawing graph) (FiniteIntersectionDrawing graph) :=
  ⟨toFiniteIntersectionDrawing⟩

end Paper170Geometry

namespace Paper170.AdmissibleDrawing

abbrev toFiniteIntersectionDrawing {V E : Type} {G : Graph V E} (D : AdmissibleDrawing G) :
    Paper170Geometry.FiniteIntersectionDrawing G := Paper170Geometry.toFiniteIntersectionDrawing D

end Paper170.AdmissibleDrawing

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_IntervalSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

def intervalSegment (a b t : unitInterval) : unitInterval :=
  ⟨(1-t.val)*a.val+t.val*b.val,by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
        (mul_nonneg t.property.1 b.property.1)
    · have h₀ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
      have h₁ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
      linarith⟩

theorem intervalSegment_between (a b t : unitInterval) (hab : a ≤ b) :
    a ≤ intervalSegment a b t ∧ intervalSegment a b t ≤ b := by
  have hab' : a.val ≤ b.val := hab
  have h₀ := mul_nonneg t.property.1 (sub_nonneg.mpr hab')
  have h₁ := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hab')
  change a.val ≤ (1-t.val)*a.val+t.val*b.val ∧ (1-t.val)*a.val+t.val*b.val ≤ b.val
  constructor <;> nlinarith

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_AffinePathHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def intervalLeft (t : unitInterval) : unitInterval := ⟨t.val/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
def intervalRight (t : unitInterval) : unitInterval := ⟨(1+t.val)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩

theorem intervalLeft_strictMono : StrictMono intervalLeft := by
  intro s t hst
  change s.val/2 < t.val/2
  exact div_lt_div_of_pos_right hst (by norm_num)

theorem intervalRight_strictMono : StrictMono intervalRight := by
  intro s t hst
  change (1+s.val)/2 < (1+t.val)/2
  have hh : s.val < t.val := hst
  linarith

theorem intervalSegment_left (a b t : unitInterval) :
    intervalSegment (intervalLeft a) (intervalLeft b) t=intervalLeft (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*(a.val/2)+t.val*(b.val/2)=((1-t.val)*a.val+t.val*b.val)/2
  ring

theorem intervalSegment_right (a b t : unitInterval) :
    intervalSegment (intervalRight a) (intervalRight b) t=intervalRight (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*((1+a.val)/2)+t.val*((1+b.val)/2)=(1+((1-t.val)*a.val+t.val*b.val))/2
  ring

theorem path_trans_intervalLeft {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalLeft t)=γ t := by
  rw [← (γ.trans η).extend_extends' (intervalLeft t)]
  rw [Path.extend_trans_of_le_half γ η (show (intervalLeft t).val ≤ 1/2 by
    change t.val/2 ≤ 1/2
    linarith [t.property.2])]
  have he : 2*(intervalLeft t).val=t.val := by change 2*(t.val/2)=t.val; ring
  rw [he,γ.extend_extends']

theorem path_trans_intervalRight {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalRight t)=η t := by
  rw [← (γ.trans η).extend_extends' (intervalRight t)]
  rw [Path.extend_trans_of_half_le γ η (show 1/2 ≤ (intervalRight t).val by
    change 1/2 ≤ (1+t.val)/2
    linarith [t.property.1])]
  have he : 2*(intervalRight t).val-1=t.val := by change 2*((1+t.val)/2)-1=t.val; ring
  rw [he,η.extend_extends']

theorem intervalSegment_zero_one (t : unitInterval) : intervalSegment 0 1 t=t := by
  apply Subtype.ext
  change (1-t.val)*0+t.val*1=t.val
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PlanarSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

def det2 (u v : Plane) : ℝ := u.1*v.2-u.2*v.1

def segmentPoint (a b : Plane) (t : ℝ) : Plane := (1-t) • a+t • b

def openSegmentTrace (a b : Plane) : Set Plane := segmentPoint a b '' Set.Ioo 0 1

def SegmentsCrossProperly (a b c d : Plane) : Prop :=
  det2 (b-a) (d-c) ≠ 0 ∧
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ u ∈ Set.Ioo (0 : ℝ) 1,
      segmentPoint a b t = segmentPoint c d u

def segmentCrossingSign (a b c d : Plane) : ℝ :=
  if SegmentsCrossProperly a b c d then
    (if 0 < det2 (b-a) (d-c) then 1 else -1) else 0

@[simp] theorem segmentPoint_zero (a b : Plane) : segmentPoint a b 0 = a := by
  simp [segmentPoint]

@[simp] theorem segmentPoint_one (a b : Plane) : segmentPoint a b 1 = b := by
  simp [segmentPoint]

theorem segmentPoint_reverse (a b : Plane) (t : ℝ) :
    segmentPoint b a (1-t) = segmentPoint a b t := by
  simp [segmentPoint, add_comm]

theorem det2_swap (u v : Plane) : det2 v u = -det2 u v := by
  simp only [det2]
  ring

theorem segment_intersection_parameters_unique (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (t u t' u' : ℝ)
    (h : segmentPoint a b t = segmentPoint c d u)
    (h' : segmentPoint a b t' = segmentPoint c d u') : t = t' ∧ u = u' := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  have h₁' := congrArg Prod.fst h'
  have h₂' := congrArg Prod.snd h'
  change (1-t)*a.1+t*b.1 = (1-u)*c.1+u*d.1 at h₁
  change (1-t)*a.2+t*b.2 = (1-u)*c.2+u*d.2 at h₂
  change (1-t')*a.1+t'*b.1 = (1-u')*c.1+u'*d.1 at h₁'
  change (1-t')*a.2+t'*b.2 = (1-u')*c.2+u'*d.2 at h₂'
  have ht : (t-t') * det2 (b-a) (d-c) = 0 := by
    dsimp [det2]
    linear_combination (d.2-c.2)*h₁ - (d.1-c.1)*h₂ - (d.2-c.2)*h₁' + (d.1-c.1)*h₂'
  have hu : (u-u') * det2 (b-a) (d-c) = 0 := by
    dsimp [det2]
    linear_combination (b.2-a.2)*h₁ - (b.1-a.1)*h₂ - (b.2-a.2)*h₁' + (b.1-a.1)*h₂'
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hn),
    sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hn)⟩

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

def polygonalArcPath (v : ℕ → Plane) : (n : ℕ) → Path (v 0) (v n)
  | 0 => Path.refl (v 0)
  | 1 => Path.segment (v 0) (v 1)
  | n+2 => (polygonalArcPath v (n+1)).trans (Path.segment (v (n+1)) (v (n+2)))

structure PolygonalChain (O : Set Plane) (a b : Plane) where
  pieces : ℕ
  vertices : ℕ → Plane
  first : vertices 0=a
  last : vertices pieces=b
  start_mem : a ∈ O
  inside : ∀ i, i < pieces → segment ℝ (vertices i) (vertices (i+1)) ⊆ O

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

def path (P : PolygonalChain O a b) : Path a b :=
  (polygonalArcPath P.vertices P.pieces).cast P.first.symm P.last.symm

end PolygonalChain

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PathSubarc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem intervalSegment_surjective_interval (a b : unitInterval) (hab : a < b)
    (t : unitInterval) (ht : a ≤ t ∧ t ≤ b) : ∃ u : unitInterval, intervalSegment a b u=t := by
  have hd : 0 < b.val-a.val := sub_pos.mpr hab
  have ht0 : 0 ≤ (t.val-a.val)/(b.val-a.val) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have ht1 : (t.val-a.val)/(b.val-a.val) ≤ 1 :=
    (div_le_one hd).mpr (sub_le_sub_right (show t.val ≤ b.val from ht.2) a.val)
  refine ⟨⟨(t.val-a.val)/(b.val-a.val),ht0,ht1⟩,?_⟩
  apply Subtype.ext
  change (1-(t.val-a.val)/(b.val-a.val))*a.val+((t.val-a.val)/(b.val-a.val))*b.val=t.val
  field_simp
  ring

def pathSubarc {a b : Plane} (γ : Path a b) (u v : unitInterval) : Path (γ u) (γ v) where
  toFun := fun t => γ (intervalSegment u v t)
  continuous_toFun := by
    apply γ.continuous.comp
    unfold intervalSegment
    fun_prop
  source' := by simp [intervalSegment]
  target' := by simp [intervalSegment]

theorem pathSubarc_range {a b : Plane} (γ : Path a b) (u v : unitInterval) (huv : u < v) :
    Set.range (pathSubarc γ u v)=γ '' Set.Icc u v := by
  apply Set.Subset.antisymm
  · rintro x ⟨t,rfl⟩
    exact ⟨intervalSegment u v t,intervalSegment_between u v t huv.le,rfl⟩
  · rintro x ⟨t,ht,rfl⟩
    obtain ⟨s,hs⟩ := intervalSegment_surjective_interval u v huv t ht
    exact ⟨s,congrArg γ hs⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PlanarDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

@[simp] theorem det2_self (u : Plane) : det2 u u = 0 := by
  dsimp [det2]
  ring

@[simp] theorem det2_zero_left (u : Plane) : det2 0 u = 0 := by simp [det2]
@[simp] theorem det2_zero_right (u : Plane) : det2 u 0 = 0 := by simp [det2]

end Zarankiewicz

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

def rotateQuarter (v : Plane) : Plane := (-v.2,v.1)
def squaredLength (v : Plane) : ℝ := v.1^2+v.2^2

theorem squaredLength_pos (v : Plane) (hv : v ≠ 0) : 0 < squaredLength v := by
  have hx := sq_nonneg v.1
  have hy := sq_nonneg v.2
  have hnon : 0 ≤ squaredLength v := by dsimp [squaredLength]; linarith
  rcases eq_or_lt_of_le hnon with hzero | hpos
  · have h₁ : v.1=0 := by dsimp [squaredLength] at hzero; nlinarith
    have h₂ : v.2=0 := by dsimp [squaredLength] at hzero; nlinarith
    exact False.elim (hv (Prod.ext h₁ h₂))
  · exact hpos

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentSymmetries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem segmentsCrossProperly_swap (a b c d : Plane) :
    SegmentsCrossProperly c d a b ↔ SegmentsCrossProperly a b c d := by
  constructor
  · rintro ⟨hn,t,ht,u,hu,he⟩
    refine ⟨?_,u,hu,t,ht,he.symm⟩
    rw [det2_swap] at hn
    exact neg_ne_zero.mp hn
  · rintro ⟨hn,t,ht,u,hu,he⟩
    refine ⟨?_,u,hu,t,ht,he.symm⟩
    rw [det2_swap]
    exact neg_ne_zero.mpr hn

theorem openSegment_intersection_subsingleton (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) : (openSegmentTrace a b ∩ openSegmentTrace c d).Subsingleton := by
  rintro x ⟨⟨t,ht,htx⟩,⟨u,hu,hux⟩⟩ y ⟨⟨t',ht',hty⟩,⟨u',hu',huy⟩⟩
  have hh := segment_intersection_parameters_unique a b c d hn t u t' u'
    (htx.trans hux.symm) (hty.trans huy.symm)
  rw [← htx, ← hty, hh.1]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def firstIntersectionParameter (a b c d : Plane) : ℝ :=
  det2 (d-c) (a-c) / det2 (b-a) (d-c)

def secondIntersectionParameter (a b c d : Plane) : ℝ :=
  -det2 (b-a) (c-a) / det2 (b-a) (d-c)

theorem intersection_parameters_eq (a b c d : Plane) (hn : det2 (b-a) (d-c) ≠ 0) :
    segmentPoint a b (firstIntersectionParameter a b c d) =
      segmentPoint c d (secondIntersectionParameter a b c d) := by
  apply Prod.ext
  · change (1-firstIntersectionParameter a b c d)*a.1+firstIntersectionParameter a b c d*b.1 =
      (1-secondIntersectionParameter a b c d)*c.1+secondIntersectionParameter a b c d*d.1
    unfold firstIntersectionParameter secondIntersectionParameter
    field_simp
    dsimp [det2]
    ring
  · change (1-firstIntersectionParameter a b c d)*a.2+firstIntersectionParameter a b c d*b.2 =
      (1-secondIntersectionParameter a b c d)*c.2+secondIntersectionParameter a b c d*d.2
    unfold firstIntersectionParameter secondIntersectionParameter
    field_simp
    dsimp [det2]
    ring

theorem segmentsCrossProperly_iff_parameters (a b c d : Plane) (hn : det2 (b-a) (d-c) ≠ 0) :
    SegmentsCrossProperly a b c d ↔
      firstIntersectionParameter a b c d ∈ Set.Ioo (0 : ℝ) 1 ∧
      secondIntersectionParameter a b c d ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · rintro ⟨_,t,ht,u,hu,he⟩
    have hh := segment_intersection_parameters_unique a b c d hn t u
      (firstIntersectionParameter a b c d) (secondIntersectionParameter a b c d)
      he (intersection_parameters_eq a b c d hn)
    exact ⟨hh.1 ▸ ht,hh.2 ▸ hu⟩
  · rintro ⟨ht,hu⟩
    exact ⟨hn,_,ht,_,hu,intersection_parameters_eq a b c d hn⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentSides
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def orient2 (a b c : Plane) : ℝ := det2 (b-a) (c-a)

theorem orient2_self_segment (a b : Plane) (t : ℝ) : orient2 a b (segmentPoint a b t) = 0 := by
  dsimp [orient2, det2, segmentPoint]
  ring

theorem orient2_segment (a b c d : Plane) (u : ℝ) :
    orient2 a b (segmentPoint c d u) = (1-u)*orient2 a b c+u*orient2 a b d := by
  dsimp [orient2,det2,segmentPoint]
  ring

theorem orient2_difference (a b c d : Plane) :
    orient2 a b d-orient2 a b c = det2 (b-a) (d-c) := by
  dsimp [orient2,det2]
  ring

theorem orient2_other_difference (a b c d : Plane) :
    orient2 c d a-orient2 c d b = det2 (b-a) (d-c) := by
  dsimp [orient2,det2]
  ring

theorem segmentCrossingSign_of_positive_sides (a b c d : Plane)
    (hc : orient2 a b c < 0) (hd : 0 < orient2 a b d)
    (ha : 0 < orient2 c d a) (hb : orient2 c d b < 0) :
    segmentCrossingSign a b c d = 1 := by
  have hdiff := orient2_difference a b c d
  have hother := orient2_other_difference a b c d
  have hdet : 0 < det2 (b-a) (d-c) := by linarith
  have hcros : SegmentsCrossProperly a b c d := by
    apply (segmentsCrossProperly_iff_parameters a b c d (ne_of_gt hdet)).mpr
    constructor
    · change 0 < orient2 c d a / det2 (b-a) (d-c) ∧ orient2 c d a / det2 (b-a) (d-c) < 1
      exact ⟨div_pos ha hdet, (div_lt_one hdet).mpr (by linarith)⟩
    · change 0 < -orient2 a b c / det2 (b-a) (d-c) ∧ -orient2 a b c / det2 (b-a) (d-c) < 1
      exact ⟨div_pos (neg_pos.mpr hc) hdet, (div_lt_one hdet).mpr (by linarith)⟩
  simp [segmentCrossingSign,hcros,hdet]

theorem not_segmentsCrossProperly_of_same_side (a b c d : Plane)
    (hside : (0 < orient2 a b c ∧ 0 < orient2 a b d) ∨
      (orient2 a b c < 0 ∧ orient2 a b d < 0)) : ¬ SegmentsCrossProperly a b c d := by
  rintro ⟨_,t,ht,u,hu,he⟩
  have hzero := congrArg (orient2 a b) he
  rw [orient2_self_segment,orient2_segment] at hzero
  have hpos : 0 < 1-u := by linarith [hu.2]
  rcases hside with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · have := add_pos (mul_pos hpos hc) (mul_pos hu.1 hd)
    linarith
  · have := add_neg (mul_neg_of_pos_of_neg hpos hc) (mul_neg_of_pos_of_neg hu.1 hd)
    linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ParallelDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

def dot2 (u v : Plane) : ℝ := u.1*v.1+u.2*v.2

theorem planar_vector_decomposition (u v : Plane) :
    squaredLength u • v = dot2 u v • u+det2 u v • rotateQuarter u := by
  apply Prod.ext <;> dsimp [squaredLength,dot2,det2,rotateQuarter] <;> ring

theorem vector_parallel_of_det_zero (u v : Plane) (hu : u ≠ 0) (h : det2 u v=0) :
    v = (dot2 u v/squaredLength u) • u := by
  have hs := ne_of_gt (squaredLength_pos u hu)
  have hh := planar_vector_decomposition u v
  rw [h,zero_smul,add_zero] at hh
  calc
    v = (squaredLength u)⁻¹ • (squaredLength u • v) := by rw [smul_smul,inv_mul_cancel₀ hs,one_smul]
    _ = (squaredLength u)⁻¹ • (dot2 u v • u) := by rw [hh]
    _ = _ := by rw [smul_smul,div_eq_mul_inv,mul_comm]

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

def trackDirection (v : ℕ → Plane) (i : ℕ) : Plane := v (i+1)-v i

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

def SegmentPairTransverse (a b c d : Plane) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
    segmentPoint a b t = segmentPoint c d u →
      det2 (b-a) (d-c) ≠ 0 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalParametrization
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
-- module Solutions.OAIQ4_Cc.Crossing_PolygonComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def joinedSequence (v w : ℕ → Plane) (n : ℕ) (i : ℕ) : Plane :=
  if i<n then v i else w (i-n)

theorem joinedSequence_left (v w : ℕ → Plane) (n : ℕ) (h : v n=w 0)
    (i : ℕ) (hi : i≤n) : joinedSequence v w n i=v i := by
  unfold joinedSequence
  by_cases hin : i<n
  · rw [ite_eq_left hin]
  · have he : i=n := by omega
    subst i
    simp [h]

theorem joinedSequence_right (v w : ℕ → Plane) (n j : ℕ) :
    joinedSequence v w n (n+j)=w j := by
  simp [joinedSequence,show ¬ n+j<n by omega]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChainExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygonalArcPath_range_subset (v : ℕ → Plane) (O : Set Plane) (h0 : v 0 ∈ O) :
    (n : ℕ) → (∀ i, i < n → segment ℝ (v i) (v (i+1)) ⊆ O) →
      Set.range (polygonalArcPath v n) ⊆ O
  | 0, _ => by rintro x ⟨t,rfl⟩; exact h0
  | 1, h => by
    rw [polygonalArcPath,Path.range_segment]
    exact h 0 (by omega)
  | n+2, h => by
    rw [polygonalArcPath,Path.trans_range,Set.union_subset_iff]
    refine ⟨polygonalArcPath_range_subset v O h0 (n+1) (fun i hi => h i (by omega)),?_⟩
    rw [Path.range_segment]
    exact h (n+1) (by omega)

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
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChainOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b c : Plane}

theorem vertex_mem (P : PolygonalChain O a b) (i : ℕ) (hi : i ≤ P.pieces) : P.vertices i ∈ O := by
  by_cases h0 : i=0
  · subst i
    rw [P.first]
    exact P.start_mem
  · have hp : 0 < i := by omega
    have hh := P.inside (i-1) (by omega) (right_mem_segment ℝ (P.vertices (i-1)) (P.vertices (i-1+1)))
    simpa [Nat.sub_add_cancel (show 1 ≤ i by omega)] using hh

def single (O : Set Plane) (a b : Plane) (ha : a ∈ O) (h : segment ℝ a b ⊆ O) : PolygonalChain O a b where
  pieces := 1
  vertices := fun i => if i=0 then a else b
  first := by simp
  last := by simp
  start_mem := ha
  inside := by
    intro i hi
    have he : i = 0 := by omega
    subst i
    simpa using h

def take (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : PolygonalChain O a (P.vertices k) where
  pieces := k
  vertices := P.vertices
  first := P.first
  last := rfl
  start_mem := P.start_mem
  inside := fun i hi => P.inside i (by omega)

def drop (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : PolygonalChain O (P.vertices k) b where
  pieces := P.pieces-k
  vertices := fun i => P.vertices (k+i)
  first := by simp
  last := by simpa [Nat.add_sub_of_le hk] using P.last
  start_mem := P.vertex_mem k hk
  inside := by
    intro i hi
    simpa [Nat.add_assoc] using P.inside (k+i) (by omega)

def join (P : PolygonalChain O a b) (Q : PolygonalChain O b c) : PolygonalChain O a c where
  pieces := P.pieces+Q.pieces
  vertices := joinedSequence P.vertices Q.vertices P.pieces
  first := (joinedSequence_left _ _ _ (P.last.trans Q.first.symm) 0 (Nat.zero_le _)).trans P.first
  last := (joinedSequence_right _ _ P.pieces Q.pieces).trans Q.last
  start_mem := P.start_mem
  inside := by
    intro i hi
    have hglue : P.vertices P.pieces=Q.vertices 0 := P.last.trans Q.first.symm
    by_cases hin : i < P.pieces
    · rw [joinedSequence_left _ _ _ hglue i (by omega),joinedSequence_left _ _ _ hglue (i+1) (by omega)]
      exact P.inside i hin
    · have hbase : i=P.pieces+(i-P.pieces) := by omega
      have hnext : i+1=P.pieces+((i-P.pieces)+1) := by omega
      have h₀ : joinedSequence P.vertices Q.vertices P.pieces i = Q.vertices (i-P.pieces) := by
        conv_lhs => rw [hbase]
        exact joinedSequence_right _ _ _ _
      have h₁ : joinedSequence P.vertices Q.vertices P.pieces (i+1) = Q.vertices ((i-P.pieces)+1) := by
        rw [hnext, joinedSequence_right]
      rw [h₀,h₁]
      exact Q.inside (i-P.pieces) (by omega)

@[simp] theorem pieces_single (ha : a ∈ O) (h : segment ℝ a b ⊆ O) : (single O a b ha h).pieces=1 := rfl
@[simp] theorem pieces_take (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : (P.take k hk).pieces=k := rfl
@[simp] theorem pieces_drop (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : (P.drop k hk).pieces=P.pieces-k := rfl
@[simp] theorem pieces_join (P : PolygonalChain O a b) (Q : PolygonalChain O b c) : (P.join Q).pieces=P.pieces+Q.pieces := rfl

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

theorem path_meeting_parameters {X : Type*} [TopologicalSpace X] {a b c : X}
    (γ : Path a b) (η : Path b c) (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hm : ∀ x, x ∈ Set.range γ → x ∈ Set.range η → x=b)
    (s t : unitInterval) (he : γ s=η t) : s=1 ∧ t=0 := by
  have hx : γ s=b := hm _ ⟨s,rfl⟩ ⟨t,he.symm⟩
  exact ⟨hγ (hx.trans γ.target.symm),hη (he.symm.trans (hx.trans η.source.symm))⟩

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

def graphWalkPath {V : Type*} {G : SimpleGraph V} (pos : V → Plane) {a b : V} (p : G.Walk a b) :
    Path (pos a) (pos b) :=
  (polygonalArcPath (fun i => pos (p.getVert i)) p.length).cast
    (congrArg pos p.getVert_zero).symm (congrArg pos p.getVert_length).symm

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

def pieceTrace (P : PolygonalParametrization γ) (i : Fin P.pieces) : Set Plane :=
  segment ℝ (γ (P.knot i.castSucc)) (γ (P.knot i.succ))

theorem pieceTrace_parameter (P : PolygonalParametrization γ) (i : Fin P.pieces)
    (x : Plane) (hx : x ∈ P.pieceTrace i) :
    ∃ t : unitInterval, γ (intervalSegment (P.knot i.castSucc) (P.knot i.succ) t)=x := by
  rw [pieceTrace,← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  refine ⟨t,(P.affine i t).trans ?_⟩
  simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht

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

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_GraphSequenceWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

def graphSequenceWalk {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (∀ i, i < k → G.Adj (v i) (v (i+1))) → G.Walk (v 0) (v k)
  | 0, _ => .nil
  | k+1, h => (graphSequenceWalk G v k (fun i hi => h i (by omega))).concat (h k (by omega))

theorem graphSequenceWalk_length {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (h : ∀ i, i < k → G.Adj (v i) (v (i+1))) → (graphSequenceWalk G v k h).length=k
  | 0, _ => rfl
  | k+1, h => by rw [graphSequenceWalk,SimpleGraph.Walk.length_concat,graphSequenceWalk_length]

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
-- module Solutions.OAIQ4_Cc.Crossing_RoundDiskClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical Topology

def closedRoundDisk (z : Plane) (r : ℝ) : Set Plane := {x | squaredLength (x-z) ≤ r^2}

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_DiskPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

structure DiskPassage {a b : Plane} (γ : Path a b) (z : Plane) (r : ℝ) (τ : unitInterval) where
  enter : unitInterval
  leave : unitInterval
  enter_le_mark : enter ≤ τ
  mark_le_leave : τ ≤ leave
  enter_mem : γ enter ∈ closedRoundDisk z r
  leave_mem : γ leave ∈ closedRoundDisk z r
  all_visits : ∀ t, γ t ∈ closedRoundDisk z r → enter ≤ t ∧ t ≤ leave
  enter_boundary : 0 < enter → squaredLength (γ enter-z)=r^2
  leave_boundary : leave < 1 → squaredLength (γ leave-z)=r^2
  strict_enter : 0 < τ → enter < τ
  strict_leave : τ < 1 → τ < leave

namespace DiskPassage
variable {a b z : Plane} {γ : Path a b} {r : ℝ} {τ : unitInterval}

theorem enter_lt_leave (P : DiskPassage γ z r τ) : P.enter < P.leave := by
  by_cases ht : τ=0
  · exact P.enter_le_mark.trans_lt (P.strict_leave (by rw [ht]; exact zero_lt_one))
  · exact (P.strict_enter (lt_of_le_of_ne (show 0 ≤ τ from τ.property.1) (Ne.symm ht))).trans_le P.mark_le_leave

end DiskPassage
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_OrderedPassages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def retainedSubarc {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ)
    (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i)) (i : Fin k) :
    Path (γ (P i.castSucc).leave) (γ (P i.succ).enter) :=
  pathSubarc γ (P i.castSucc).leave (P i.succ).enter

theorem ordered_passage_enter_strictMono {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter) :
    StrictMono (fun i => (P i).enter) := by
  intro i j hij
  exact (P i).enter_lt_leave.trans (hsep i j hij)

theorem retained_interval_no_mark {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (hτ : StrictMono τ) (h0 : τ 0=0)
    (h1 : τ (Fin.last k)=1) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (i : Fin k) (t : unitInterval)
    (ht : t ∈ Set.Icc (P i.castSucc).leave (P i.succ).enter) : t ∉ Set.range τ := by
  rintro ⟨j,hj⟩
  have hleft : τ i.castSucc < 1 := by
    rw [← h1]
    exact hτ (show i.castSucc < Fin.last k from i.isLt)
  have hright : 0 < τ i.succ := by
    rw [← h0]
    exact hτ (show (0 : Fin (k+1)) < i.succ by change 0 < i.val+1; omega)
  by_cases hji : j ≤ i.castSucc
  · have hh := (hτ.monotone hji).trans_lt ((P i.castSucc).strict_leave hleft)
    exact hh.not_ge (ht.1.trans_eq hj.symm)
  · have hij : i.succ ≤ j := by
      change i.val+1 ≤ j.val
      have hh : ¬ j.val ≤ i.val := hji
      omega
    have hh := ((P i.succ).strict_enter hright).trans_le (hτ.monotone hij)
    exact hh.not_ge (hj.trans_le ht.2)

theorem retained_interval_pair_disjoint {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter)
    (i j : Fin k) (hij : i < j) :
    Disjoint (Set.Icc (P i.castSucc).leave (P i.succ).enter)
      (Set.Icc (P j.castSucc).leave (P j.succ).enter) := by
  have hi : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
  have hgap := ((ordered_passage_enter_strictMono γ τ r P hsep).monotone hi).trans_lt (P j.castSucc).enter_lt_leave
  apply Set.disjoint_left.mpr
  intro t ht hu
  exact hgap.not_ge (hu.1.trans ht.2)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_RadialExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem squaredLength_add_smul (u v : Plane) (t : ℝ) :
    squaredLength (u+t • v)=squaredLength u+2*t*dot2 u v+t^2*squaredLength v := by
  dsimp [squaredLength,dot2]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FiniteDiskCollar
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
-- module Solutions.OAIQ4_Cc.Crossing_CircleChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem orient2_cycle (a b c : Plane) : orient2 b c a = orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem orient2_swap_ends (a b c : Plane) : orient2 a c b = -orient2 a b c := by
  exact det2_swap (b-a) (c-a)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ChordTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentPairTransverse_of_noncollinear_endpoints (a b c d : Plane)
    (ha : orient2 c d a ≠ 0) (hb : orient2 c d b ≠ 0)
    (hc : orient2 a b c ≠ 0) (hd : orient2 a b d ≠ 0) :
    SegmentPairTransverse a b c d := by
  intro t ht u hu he
  have hdet : det2 (b-a) (d-c) ≠ 0 := by
    intro hz
    have hdiff := orient2_difference a b c d
    have heq : orient2 a b c=orient2 a b d := by linarith
    have hh := congrArg (orient2 a b) he
    rw [orient2_self_segment,orient2_segment,← heq] at hh
    apply hc
    nlinarith
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    rw [segmentPoint_zero] at he
    exact ha (by rw [he,orient2_self_segment])
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    rw [segmentPoint_one] at he
    exact hb (by rw [he,orient2_self_segment])
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    rw [segmentPoint_zero] at he
    exact hc (by rw [← he,orient2_self_segment])
  have hu1 : u ≠ 1 := by
    intro h
    subst u
    rw [segmentPoint_one] at he
    exact hd (by rw [← he,orient2_self_segment])
  exact ⟨hdet,⟨lt_of_le_of_ne ht.1 ht0.symm,lt_of_le_of_ne ht.2 ht1⟩,
    ⟨lt_of_le_of_ne hu.1 hu0.symm,lt_of_le_of_ne hu.2 hu1⟩⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_RoundCircleChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem round_circle_line_two_points (z a b c : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hab : a ≠ b)
    (hd : det2 (b-a) (c-a)=0) : c=a ∨ c=b := by
  have hlen := squaredLength_pos (b-a) (sub_ne_zero.mpr (Ne.symm hab))
  let t := dot2 (b-a) (c-a)/squaredLength (b-a)
  have hp : c-a=t • (b-a) := vector_parallel_of_det_zero (b-a) (c-a)
    (sub_ne_zero.mpr (Ne.symm hab)) hd
  have hba : (a-z)+(b-a)=b-z := by abel
  have hca : c-z=(a-z)+t • (b-a) := by rw [← hp]; abel
  have h₁ := squaredLength_add_smul (a-z) (b-a) 1
  simp only [one_smul,hba,ha,hb,one_pow,one_mul] at h₁
  rw [hca,squaredLength_add_smul,ha] at hc
  have hh : t*(t-1)*squaredLength (b-a)=0 := by linear_combination hc+t*h₁
  have ht := (mul_eq_zero.mp hh).resolve_right (ne_of_gt hlen)
  rcases mul_eq_zero.mp ht with ht | ht
  · left
    rw [ht,zero_smul] at hp
    exact sub_eq_zero.mp hp
  · right
    have ht1 : t=1 := sub_eq_zero.mp ht
    rw [ht1,one_smul] at hp
    exact sub_left_injective hp

theorem round_circle_orient_ne_zero (z a b c : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient2 a b c ≠ 0 := by
  intro hd
  exact (round_circle_line_two_points z a b c r ha hb hc hab hd).elim
    (fun h => hac h.symm) (fun h => hbc h.symm)

theorem round_circle_chords_transverse (z a b c d : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hd : squaredLength (d-z)=r^2)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    SegmentPairTransverse a b c d := by
  exact segmentPairTransverse_of_noncollinear_endpoints a b c d
    (round_circle_orient_ne_zero z c d a r hc hd ha hcd hac.symm had.symm)
    (round_circle_orient_ne_zero z c d b r hc hd hb hcd hbc.symm hbd.symm)
    (round_circle_orient_ne_zero z a b c r ha hb hc hab hac hbc)
    (round_circle_orient_ne_zero z a b d r ha hb hd hab had hbd)

theorem round_chord_in_open_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hab : a ≠ b) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    squaredLength (segmentPoint a b t-z) < r^2 := by
  have he : squaredLength (segmentPoint a b t-z)=
      (1-t)*squaredLength (a-z)+t*squaredLength (b-z)-t*(1-t)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hp := mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2))
    (squaredLength_pos (b-a) (sub_ne_zero.mpr hab.symm))
  rw [he,ha,hb]
  linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_VertexDiskSpokes
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
-- module Solutions.OAIQ4_Cc.Crossing_SegmentIntersectionUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem transverse_segment_intersection_subsingleton (a b c d : Plane)
    (h : SegmentPairTransverse a b c d) :
    (Set.range (Path.segment a b) ∩ Set.range (Path.segment c d)).Subsingleton := by
  intro x hx y hy
  obtain ⟨⟨s,hs⟩,⟨t,ht⟩⟩ := hx
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := hy
  have hxs : segmentPoint a b s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have hxt : segmentPoint c d t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have hyu : segmentPoint a b u.val=y := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hu
  have hyv : segmentPoint c d v.val=y := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hv
  have hdet := (h s.val s.property t.val t.property (hxs.trans hxt.symm)).1
  have he := segment_intersection_parameters_unique a b c d hdet s.val t.val u.val v.val
    (hxs.trans hxt.symm) (hyu.trans hyv.symm)
  exact hxs.symm.trans ((congrArg (segmentPoint a b) he.1).trans hyu)

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

def alternatingPath (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) : (n : ℕ) → Path (a 0) (b n)
  | 0 => p 0
  | n+1 => ((alternatingPath a b p q n).trans (q n)).trans (p (n+1))

theorem alternatingPath_range_iff (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) : (n : ℕ) → ∀ x,
    x ∈ Set.range (alternatingPath a b p q n) ↔
      (∃ i, i ≤ n ∧ x ∈ Set.range (p i)) ∨ (∃ i, i < n ∧ x ∈ Set.range (q i))
  | 0, x => by
    constructor
    · intro h
      exact Or.inl ⟨0,le_rfl,h⟩
    · rintro (⟨i,hi,h⟩ | ⟨i,hi,h⟩)
      · have he : i=0 := by omega
        subst i
        exact h
      · omega
  | n+1, x => by
    rw [alternatingPath,Path.trans_range,Path.trans_range,Set.mem_union,Set.mem_union,
      alternatingPath_range_iff a b p q n]
    constructor
    · intro hx
      rcases hx with hx | hx
      · rcases hx with hx | hx
        · rcases hx with ⟨i,hi,h⟩ | ⟨i,hi,h⟩
          · exact Or.inl ⟨i,by omega,h⟩
          · exact Or.inr ⟨i,by omega,h⟩
        · exact Or.inr ⟨n,by omega,hx⟩
      · exact Or.inl ⟨n+1,le_rfl,hx⟩
    · rintro (⟨i,hi,h⟩ | ⟨i,hi,h⟩)
      · by_cases he : i=n+1
        · subst i
          exact Or.inr h
        · exact Or.inl (Or.inl (Or.inl ⟨i,by omega,h⟩))
      · by_cases he : i=n
        · subst i
          exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (Or.inr ⟨i,by omega,h⟩))

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

theorem chart_image_mem_iff (e : OpenPartialHomeomorph Plane Plane) (A L : Set Plane)
    (h : e '' (e.source ∩ A)=e.target ∩ L) (x : Plane) (hx : x ∈ e.source) :
    x ∈ A ↔ e x ∈ L := by
  constructor
  · intro ha
    have hh : e x ∈ e '' (e.source ∩ A) := ⟨x,⟨hx,ha⟩,rfl⟩
    rw [h] at hh
    exact hh.2
  · intro hl
    have hh : e x ∈ e '' (e.source ∩ A) := h.symm ▸ ⟨e.map_source hx,hl⟩
    obtain ⟨y,hy,he⟩ := hh
    have hyx : y=x := e.injOn hy.1 hx he
    exact hyx ▸ hy.2

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CrossingCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def crossingCoordinates (o u v x : Plane) : Plane :=
  (det2 (x-o) v/det2 u v,det2 u (x-o)/det2 u v)

def crossingCoordinateInverse (o u v s : Plane) : Plane := o+s.1 • u+s.2 • v

theorem crossingCoordinates_left_inverse (o u v : Plane) (h : det2 u v ≠ 0) (x : Plane) :
    crossingCoordinateInverse o u v (crossingCoordinates o u v x)=x := by
  have hc := mul_inv_cancel₀ h
  apply Prod.ext
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination (x.1-o.1)*hc
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination (x.2-o.2)*hc

theorem crossingCoordinates_right_inverse (o u v : Plane) (h : det2 u v ≠ 0) (s : Plane) :
    crossingCoordinates o u v (crossingCoordinateInverse o u v s)=s := by
  have hc := mul_inv_cancel₀ h
  apply Prod.ext
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination s.1*hc
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination s.2*hc

theorem crossingCoordinates_continuous (o u v : Plane) : Continuous (crossingCoordinates o u v) := by
  unfold crossingCoordinates det2
  fun_prop

theorem crossingCoordinateInverse_continuous (o u v : Plane) : Continuous (crossingCoordinateInverse o u v) := by
  unfold crossingCoordinateInverse
  fun_prop

def crossingCoordinateChart (o u v : Plane) (h : det2 u v ≠ 0)
    (U : Set Plane) (hU : IsOpen U) : OpenPartialHomeomorph Plane Plane where
  toFun := crossingCoordinates o u v
  invFun := crossingCoordinateInverse o u v
  source := crossingCoordinates o u v ⁻¹' U
  target := U
  map_source' := fun {_} hx => hx
  map_target' := fun {s} hs => by
    change crossingCoordinates o u v (crossingCoordinateInverse o u v s) ∈ U
    rw [crossingCoordinates_right_inverse o u v h]
    exact hs
  left_inv' := fun {x} _ => crossingCoordinates_left_inverse o u v h x
  right_inv' := fun {s} _ => crossingCoordinates_right_inverse o u v h s
  continuousOn_toFun := (crossingCoordinates_continuous o u v).continuousOn
  continuousOn_invFun := (crossingCoordinateInverse_continuous o u v).continuousOn
  open_source := hU.preimage (crossingCoordinates_continuous o u v)
  open_target := hU

@[simp] theorem crossingCoordinates_origin (o u v : Plane) : crossingCoordinates o u v o=(0,0) := by
  simp [crossingCoordinates]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentCrossingCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem inverseCoordinates_first_segment (a b c d o : Plane) (t s : ℝ)
    (ho : o=segmentPoint a b t) :
    crossingCoordinateInverse o (b-a) (d-c) (s-t,0)=segmentPoint a b s := by
  rw [ho]
  apply Prod.ext <;> dsimp [crossingCoordinateInverse,segmentPoint] <;> ring

theorem inverseCoordinates_second_segment (a b c d o : Plane) (t s : ℝ)
    (ho : o=segmentPoint c d t) :
    crossingCoordinateInverse o (b-a) (d-c) (0,s-t)=segmentPoint c d s := by
  rw [ho]
  apply Prod.ext <;> dsimp [crossingCoordinateInverse,segmentPoint] <;> ring

theorem crossingCoordinates_first_segment (a b c d o : Plane) (t s : ℝ)
    (hd : det2 (b-a) (d-c) ≠ 0) (ho : o=segmentPoint a b t) :
    crossingCoordinates o (b-a) (d-c) (segmentPoint a b s)=(s-t,0) := by
  rw [← inverseCoordinates_first_segment a b c d o t s ho]
  exact crossingCoordinates_right_inverse o (b-a) (d-c) hd _

theorem crossingCoordinates_second_segment (a b c d o : Plane) (t s : ℝ)
    (hd : det2 (b-a) (d-c) ≠ 0) (ho : o=segmentPoint c d t) :
    crossingCoordinates o (b-a) (d-c) (segmentPoint c d s)=(0,s-t) := by
  rw [← inverseCoordinates_second_segment a b c d o t s ho]
  exact crossingCoordinates_right_inverse o (b-a) (d-c) hd _

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ProperSegmentCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem properCrossing_openSegments (a b c d x : Plane) (hd : det2 (b-a) (d-c) ≠ 0)
    (hx : x ∈ openSegmentTrace a b) (hy : x ∈ openSegmentTrace c d) :
    ProperCrossing (openSegmentTrace a b) (openSegmentTrace c d) x := by
  obtain ⟨t,ht,hxt⟩ := hx
  obtain ⟨u,hu,hxu⟩ := hy
  let U : Set Plane := Set.Ioo (-t) (1-t) ×ˢ Set.Ioo (-u) (1-u)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  let chart := crossingCoordinateChart x (b-a) (d-c) hd U hU
  have hzero : (0,0) ∈ U := ⟨⟨by linarith [ht.1],by linarith [ht.2]⟩,
    ⟨by linarith [hu.1],by linarith [hu.2]⟩⟩
  have hsource : x ∈ chart.source := by
    change crossingCoordinates x (b-a) (d-c) x ∈ U
    rw [crossingCoordinates_origin]
    exact hzero
  refine ⟨chart,hsource,crossingCoordinates_origin x (b-a) (d-c),?_,?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      refine ⟨chart.map_source hz.1,?_⟩
      obtain ⟨s,hs,he⟩ := hz.2
      rw [← he]
      change (crossingCoordinates x (b-a) (d-c) (segmentPoint a b s)).2=0
      rw [crossingCoordinates_first_segment a b c d x t s hd hxt.symm]
    · rintro y ⟨hy,hy0⟩
      have hs : t+y.1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1.1],by linarith [hy.1.2]⟩
      have he : chart (segmentPoint a b (t+y.1))=y := by
        change crossingCoordinates x (b-a) (d-c) (segmentPoint a b (t+y.1))=y
        rw [crossingCoordinates_first_segment a b c d x t (t+y.1) hd hxt.symm]
        apply Prod.ext
        · dsimp
          ring
        · exact hy0.symm
      refine ⟨segmentPoint a b (t+y.1),⟨?_,⟨t+y.1,hs,rfl⟩⟩,he⟩
      change chart (segmentPoint a b (t+y.1)) ∈ U
      rw [he]
      exact hy
  · apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      refine ⟨chart.map_source hz.1,?_⟩
      obtain ⟨s,hs,he⟩ := hz.2
      rw [← he]
      change (crossingCoordinates x (b-a) (d-c) (segmentPoint c d s)).1=0
      rw [crossingCoordinates_second_segment a b c d x u s hd hxu.symm]
    · rintro y ⟨hy,hy0⟩
      have hs : u+y.2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hy.2.1],by linarith [hy.2.2]⟩
      have he : chart (segmentPoint c d (u+y.2))=y := by
        change crossingCoordinates x (b-a) (d-c) (segmentPoint c d (u+y.2))=y
        rw [crossingCoordinates_second_segment a b c d x u (u+y.2) hd hxu.symm]
        apply Prod.ext
        · exact hy0.symm
        · dsimp
          ring
      refine ⟨segmentPoint c d (u+y.2),⟨?_,⟨u+y.2,hs,rfl⟩⟩,he⟩
      change chart (segmentPoint c d (u+y.2)) ∈ U
      rw [he]
      exact hy

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_DrawingMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked subdivision parameters, incidence graphs, and edge walks. -/

section

/-! The actual finite marks and marked parameters of a continuous drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
def drawingMarks (D : FiniteIntersectionDrawing graph) : Set Plane :=
  Set.range D.vertex ∪ Paper170.crossingPoints D.toContinuousDrawing

theorem crossing_not_vertex (D : FiniteIntersectionDrawing graph) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing) (v : Vertex) : x ≠ D.vertex v := by
  obtain ⟨e,f,hef,⟨t,ht,he⟩,hf⟩ := hx
  intro hh
  exact D.interior_avoids_vertices e t ht v (he.trans hh)

theorem marked_parameter_zero (D : FiniteIntersectionDrawing graph) (e : Edge) :
    (0 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨graph.src e,(D.edge e).source.symm⟩

theorem marked_parameter_one (D : FiniteIntersectionDrawing graph) (e : Edge) :
    (1 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨graph.dst e,(D.edge e).target.symm⟩

theorem unmarked_edge_point_interior (D : FiniteIntersectionDrawing graph) (e : Edge)
    (t : unitInterval) (ht : D.edge e t ∉ drawingMarks D) : t ∈ Set.Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    exact ht (marked_parameter_zero D e)
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    exact ht (marked_parameter_one D e)
  exact ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩

theorem unmarked_intersection_same_edge (D : FiniteIntersectionDrawing graph)
    (e f : Edge) (s t : unitInterval)
    (he : D.edge e s=D.edge f t) (hs : D.edge e s ∉ drawingMarks D) : e=f := by
  by_contra hef
  have hsi := unmarked_edge_point_interior D e s hs
  have hti := unmarked_edge_point_interior D f t (he ▸ hs)
  exact hs (Or.inr ⟨e,f,hef,⟨s,hsi,rfl⟩,⟨t,hti,he.symm⟩⟩)

end Paper170Geometry

end
end

section

/-! Refined segments of the actual drawing meet only at common subdivision endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

abbrev DrawingPiece {D : Paper170.AdmissibleDrawing graph} (P : ∀ e, PolygonalParametrization (D.edge e)) :=
  (e : Edge) × Fin (P e).pieces

def drawingPieceStart {D : Paper170.AdmissibleDrawing graph} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.castSucc)

def drawingPieceEnd {D : Paper170.AdmissibleDrawing graph} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.succ)

theorem drawingPiece_endpoints_ne {D : Paper170.AdmissibleDrawing graph}
    (P : ∀ e, PolygonalParametrization (D.edge e)) (i : DrawingPiece P) :
    drawingPieceStart P i ≠ drawingPieceEnd P i := by
  intro he
  have hh := D.edge_injective i.1 he
  exact ((P i.1).increasing (show i.2.castSucc < i.2.succ by change i.2.val < i.2.val+1; omega)).ne hh

end Paper170Geometry

end
end

section

/-! The actual straight embedded graph formed by refined drawing segments. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}

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

end Paper170Geometry

end
end

section

/-! Each actual subdivided drawing edge is a simple walk of the constructed embedded graph. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}

theorem drawingEdgeSequence_adj (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (i : ℕ) (hi : i < (P e).pieces) :
    (drawingSubdivisionGraph P).Adj ((P e).vertices i) ((P e).vertices (i+1)) := by
  let j : Fin (P e).pieces := ⟨i,hi⟩
  have h0 : (P e).vertices i=drawingPieceStart P ⟨e,j⟩ := (P e).vertices_at j.castSucc
  have h1 : (P e).vertices (i+1)=drawingPieceEnd P ⟨e,j⟩ := (P e).vertices_at j.succ
  rw [h0,h1]
  exact drawingSubdivisionGraph_piece_adj P ⟨e,j⟩

def drawingEdgeWalk (P : ∀ e, PolygonalParametrization (D.edge e)) (e : Edge) :
    (drawingSubdivisionGraph P).Walk (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))) :=
  (graphSequenceWalk (drawingSubdivisionGraph P) (P e).vertices (P e).pieces
    (drawingEdgeSequence_adj P e)).copy (P e).vertices_first (P e).vertices_last

theorem drawingEdgeWalk_length (P : ∀ e, PolygonalParametrization (D.edge e)) (e : Edge) :
    (drawingEdgeWalk P e).length=(P e).pieces := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.length_copy,graphSequenceWalk_length]

theorem drawingEdgeWalk_getVert (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (i : ℕ) (hi : i ≤ (P e).pieces) :
    (drawingEdgeWalk P e).getVert i=(P e).vertices i := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.getVert_copy]
  exact graphSequenceWalk_getVert _ _ _ _ i hi

end Paper170Geometry

end
end

section

/-! Exact parameter-side control of actual graph-walk prefixes and suffixes. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem graphWalkPath_range_cases {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) (x : Plane) (hx : x ∈ Set.range (graphWalkPath pos p)) :
    x=pos a ∨ ∃ i, i < p.length ∧ x ∈ segment ℝ (pos (p.getVert i)) (pos (p.getVert (i+1))) := by
  by_cases hp : p.length=0
  · change x ∈ Set.range (polygonalArcPath (fun i => pos (p.getVert i)) p.length) at hx
    rw [hp] at hx
    obtain ⟨t,ht⟩ := hx
    exact Or.inl (by simpa [polygonalArcPath,p.getVert_zero] using ht.symm)
  · exact Or.inr (polygonalArcPath_range_piece _ _ (by omega) x hx)

variable  {D : Paper170.AdmissibleDrawing graph}

theorem drawingEdgeWalk_take_trace (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (k : Fin ((P e).pieces+1)) :
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
    (e : Edge) (k : Fin ((P e).pieces+1)) :
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

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Ports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isolated drawing disks, retained arcs, and boundary ports. -/

section

/-! The actual finite vertex/crossing marks supply the normalization disk family. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
abbrev DrawingMark (D : FiniteIntersectionDrawing graph) := ↥(drawingMarks D)

end Paper170Geometry

end
end

section

/-! Constructed finite marked-passage decomposition of the given actual drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
/-- Geometric cut data for the original drawing. Existence is proved below;
this record asserts no crossing bound or drawing-normalization conclusion. -/
structure DrawingPassages (D : FiniteIntersectionDrawing graph) where
  radius : ℝ
  radius_pos : 0 < radius
  disks_disjoint : ∀ x y : DrawingMark D, x ≠ y →
    Disjoint (closedRoundDisk x.val radius) (closedRoundDisk y.val radius)
  count : Edge → ℕ
  count_pos : ∀ e, 0 < count e
  node : ∀ e, Fin (count e+1) → unitInterval
  increasing : ∀ e, StrictMono (node e)
  first : ∀ e, node e 0=0
  last : ∀ e, node e (Fin.last (count e))=1
  node_range : ∀ e, Set.range (node e)=(D.edge e) ⁻¹' drawingMarks D
  passage : ∀ e i, DiskPassage (D.edge e) (D.edge e (node e i)) radius (node e i)
  separated : ∀ e i j, i < j → (passage e i).leave < (passage e j).enter
  visited_mark_on_edge : ∀ e (x : DrawingMark D) t,
    D.edge e t ∈ closedRoundDisk x.val radius → ∃ u, D.edge e u=x.val

end Paper170Geometry

end
end

section

/-! Actual retained middle arcs: endpoint circles and avoidance of every disk and mark. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

abbrev ArcIndex (C : DrawingPassages D) := (e : Edge) × Fin (C.count e)

theorem node_mark (C : DrawingPassages D) (e : Edge) (i : Fin (C.count e+1)) :
    D.edge e (C.node e i) ∈ drawingMarks D := by
  change C.node e i ∈ (D.edge e) ⁻¹' drawingMarks D
  rw [← C.node_range e]
  exact ⟨i,rfl⟩

def arcStartMark (C : DrawingPassages D) (i : C.ArcIndex) : DrawingMark D :=
  ⟨D.edge i.1 (C.node i.1 i.2.castSucc),C.node_mark i.1 i.2.castSucc⟩

def arcEndMark (C : DrawingPassages D) (i : C.ArcIndex) : DrawingMark D :=
  ⟨D.edge i.1 (C.node i.1 i.2.succ),C.node_mark i.1 i.2.succ⟩

def arcStart (C : DrawingPassages D) (i : C.ArcIndex) : Plane :=
  D.edge i.1 (C.passage i.1 i.2.castSucc).leave

def arcEnd (C : DrawingPassages D) (i : C.ArcIndex) : Plane :=
  D.edge i.1 (C.passage i.1 i.2.succ).enter

def arc (C : DrawingPassages D) (i : C.ArcIndex) : Path (C.arcStart i) (C.arcEnd i) :=
  retainedSubarc (D.edge i.1) (C.node i.1) C.radius (C.passage i.1) i.2

theorem arc_gap (C : DrawingPassages D) (i : C.ArcIndex) :
    (C.passage i.1 i.2.castSucc).leave < (C.passage i.1 i.2.succ).enter :=
  C.separated i.1 i.2.castSucc i.2.succ (by change i.2.val < i.2.val+1; omega)

theorem arc_endpoints_ne (C : DrawingPassages D) (i : C.ArcIndex) : C.arcStart i ≠ C.arcEnd i := by
  intro he
  exact (C.arc_gap i).ne (D.edge_injective i.1 he)

theorem arc_range (C : DrawingPassages D) (i : C.ArcIndex) :
    Set.range (C.arc i)=D.edge i.1 '' Set.Icc (C.passage i.1 i.2.castSucc).leave (C.passage i.1 i.2.succ).enter :=
  pathSubarc_range (D.edge i.1) _ _ (C.arc_gap i)

theorem arc_avoids_marks (C : DrawingPassages D) (i : C.ArcIndex) (x : Plane)
    (hx : x ∈ Set.range (C.arc i)) : x ∉ drawingMarks D := by
  rw [C.arc_range] at hx
  obtain ⟨t,ht,rfl⟩ := hx
  intro hh
  have hp : t ∈ Set.range (C.node i.1) := by rw [C.node_range]; exact hh
  exact retained_interval_no_mark (D.edge i.1) (C.node i.1) (C.increasing i.1)
    (C.first i.1) (C.last i.1) C.radius (C.passage i.1) i.2 t ht hp

theorem arc_start_on_circle (C : DrawingPassages D) (i : C.ArcIndex) :
    squaredLength (C.arcStart i-(C.arcStartMark i).val)=C.radius^2 := by
  exact (C.passage i.1 i.2.castSucc).leave_boundary
    ((C.arc_gap i).trans_le (show (C.passage i.1 i.2.succ).enter ≤ 1 from (C.passage i.1 i.2.succ).enter.property.2))

theorem arc_end_on_circle (C : DrawingPassages D) (i : C.ArcIndex) :
    squaredLength (C.arcEnd i-(C.arcEndMark i).val)=C.radius^2 := by
  exact (C.passage i.1 i.2.succ).enter_boundary
    ((show 0 ≤ (C.passage i.1 i.2.castSucc).leave from (C.passage i.1 i.2.castSucc).leave.property.1).trans_lt (C.arc_gap i))

end Paper170Geometry.DrawingPassages

end
end

section

/-! The retained actual compact arcs are pairwise disjoint, including on the same edge. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem arcs_pairwise_disjoint (C : DrawingPassages D) (p q : C.ArcIndex) (hpq : p ≠ q) :
    Disjoint (Set.range (C.arc p)) (Set.range (C.arc q)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hxm := C.arc_avoids_marks p x hx
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  rw [C.arc_range] at hx hy
  obtain ⟨s,hs,hsx⟩ := hx
  obtain ⟨t,ht,htx⟩ := hy
  have hef : e=f := unmarked_intersection_same_edge D e f s t (hsx.trans htx.symm)
    (hsx.symm ▸ hxm)
  subst f
  have hst : s=t := D.edge_injective e (hsx.trans htx.symm)
  rw [← hst] at ht
  have hij : i ≠ j := by
    intro he
    subst j
    exact hpq rfl
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Set.disjoint_left.mp
      (retained_interval_pair_disjoint (D.edge e) (C.node e) C.radius (C.passage e) (C.separated e) i j hij) hs ht
  · exact Set.disjoint_left.mp
      (retained_interval_pair_disjoint (D.edge e) (C.node e) C.radius (C.passage e) (C.separated e) j i hji) ht hs

end Paper170Geometry.DrawingPassages

end
end

section

/-! The actual distinct disk-boundary endpoints of all retained arcs. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

abbrev Port (C : DrawingPassages D) := C.ArcIndex × Bool

def portPoint (C : DrawingPassages D) (p : C.Port) : Plane :=
  if p.2 then C.arcEnd p.1 else C.arcStart p.1

def portMark (C : DrawingPassages D) (p : C.Port) : DrawingMark D :=
  if p.2 then C.arcEndMark p.1 else C.arcStartMark p.1

theorem portPoint_mem_arc (C : DrawingPassages D) (p : C.Port) :
    C.portPoint p ∈ Set.range (C.arc p.1) := by
  rcases p with ⟨i,flag⟩
  cases flag
  · exact ⟨0,(C.arc i).source⟩
  · exact ⟨1,(C.arc i).target⟩

theorem portPoint_injective (C : DrawingPassages D) : Function.Injective C.portPoint := by
  rintro ⟨i,s⟩ ⟨j,t⟩ he
  have hij : i=j := by
    by_contra h
    exact Set.disjoint_left.mp (C.arcs_pairwise_disjoint i j h)
      (C.portPoint_mem_arc (i,s)) (he.symm ▸ C.portPoint_mem_arc (j,t))
  subst j
  have hst : s=t := by
    cases s <;> cases t
    · rfl
    · exact False.elim (C.arc_endpoints_ne i he)
    · exact False.elim (C.arc_endpoints_ne i he.symm)
    · rfl
  subst t
  rfl

theorem portPoint_on_circle (C : DrawingPassages D) (p : C.Port) :
    squaredLength (C.portPoint p-(C.portMark p).val)=C.radius^2 := by
  rcases p with ⟨i,flag⟩
  cases flag
  · exact C.arc_start_on_circle i
  · exact C.arc_end_on_circle i

abbrev PortsAt (C : DrawingPassages D) (x : DrawingMark D) := {p : C.Port // C.portMark p=x}

theorem portsAt_on_circle (C : DrawingPassages D) (x : DrawingMark D) (p : C.PortsAt x) :
    squaredLength (C.portPoint p.val-x.val)=C.radius^2 := by
  simpa only [p.property] using C.portPoint_on_circle p.val

end Paper170Geometry.DrawingPassages

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_DiskFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior disk passages, vertex ports, filling containment, and crossing uniqueness. -/

section

/-! The actual internal marked passages and their two boundary endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

abbrev InnerIndex (C : DrawingPassages D) :=
  (e : Edge) × {i : Fin (C.count e+1) // 0 < i.val ∧ i.val < C.count e}

def innerMark (C : DrawingPassages D) (p : C.InnerIndex) : DrawingMark D :=
  ⟨D.edge p.1 (C.node p.1 p.2.val),C.node_mark p.1 p.2.val⟩

def incomingArc (C : DrawingPassages D) (p : C.InnerIndex) : C.ArcIndex :=
  ⟨p.1,⟨p.2.val.val-1,by have h := p.2.property; omega⟩⟩

def outgoingArc (C : DrawingPassages D) (p : C.InnerIndex) : C.ArcIndex :=
  ⟨p.1,⟨p.2.val.val,p.2.property.2⟩⟩

def incomingPort (C : DrawingPassages D) (p : C.InnerIndex) : C.Port := (C.incomingArc p,true)
def outgoingPort (C : DrawingPassages D) (p : C.InnerIndex) : C.Port := (C.outgoingArc p,false)

theorem incoming_node (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.incomingArc p).2.succ=p.2.val := by
  apply Fin.ext
  change p.2.val.val-1+1=p.2.val.val
  have h := p.2.property.1
  omega

theorem incomingPort_mark (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portMark (C.incomingPort p)=C.innerMark p := by
  apply Subtype.ext
  change D.edge p.1 (C.node p.1 (C.incomingArc p).2.succ)=D.edge p.1 (C.node p.1 p.2.val)
  rw [C.incoming_node]

theorem outgoingPort_mark (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portMark (C.outgoingPort p)=C.innerMark p := rfl

theorem incomingPort_point (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portPoint (C.incomingPort p)=D.edge p.1 (C.passage p.1 p.2.val).enter := by
  change D.edge p.1 (C.passage p.1 (C.incomingArc p).2.succ).enter=_
  rw [C.incoming_node]

theorem outgoingPort_point (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portPoint (C.outgoingPort p)=D.edge p.1 (C.passage p.1 p.2.val).leave := rfl

theorem inner_parameter_interior (C : DrawingPassages D) (p : C.InnerIndex) :
    C.node p.1 p.2.val ∈ Set.Ioo (0 : unitInterval) 1 := by
  constructor
  · rw [← C.first p.1]
    exact C.increasing p.1 (show (0 : Fin (C.count p.1+1)) < p.2.val from p.2.property.1)
  · rw [← C.last p.1]
    exact C.increasing p.1 (show p.2.val < Fin.last (C.count p.1) from p.2.property.2)

theorem innerMark_is_crossing (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.innerMark p).val ∈ Paper170.crossingPoints D.toContinuousDrawing := by
  have hm := (C.innerMark p).property
  rcases hm with ⟨v,hv⟩ | hcross
  · exact False.elim (D.interior_avoids_vertices p.1 (C.node p.1 p.2.val)
      (C.inner_parameter_interior p) v hv.symm)
  · exact hcross

def crossingChord (C : DrawingPassages D) (p : C.InnerIndex) :
    Path (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) :=
  Path.segment _ _

theorem crossingChord_injective (C : DrawingPassages D) (p : C.InnerIndex) :
    Function.Injective (C.crossingChord p) := by
  apply Path.segment_injective_of_ne
  intro he
  rw [C.incomingPort_point,C.outgoingPort_point] at he
  exact (C.passage p.1 p.2.val).enter_lt_leave.ne (D.edge_injective p.1 he)

end Paper170Geometry.DrawingPassages

end
end

section

/-! Actual replacement vertices and all incident straight-spoke directions. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

def vertexMark (_C : DrawingPassages D) (v : Vertex) : DrawingMark D :=
  ⟨D.vertex v,Or.inl ⟨v,rfl⟩⟩

theorem vertexMark_injective (C : DrawingPassages D) : Function.Injective C.vertexMark := by
  intro v w he
  exact D.vertex_injective (congrArg Subtype.val he)

theorem vertex_spoke_injective (C : DrawingPassages D) (v : Vertex → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : Vertex) (p : C.PortsAt (C.vertexMark i)) :
    Function.Injective (Path.segment (v i) (C.portPoint p.val)) := by
  apply Path.segment_injective_of_ne
  intro he
  have h := hv i
  have hp : squaredLength (C.portPoint p.val-D.vertex i)=C.radius^2 := C.portsAt_on_circle (C.vertexMark i) p
  rw [he,hp] at h
  exact lt_irrefl _ h

theorem vertex_spoke_interior (C : DrawingPassages D) (v : Vertex → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : Vertex) (p : C.PortsAt (C.vertexMark i)) (t : unitInterval)
    (ht : t < 1) : squaredLength ((Path.segment (v i) (C.portPoint p.val)) t-D.vertex i) < C.radius^2 := by
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact spoke_in_open_disk (D.vertex i) (v i) (C.portPoint p.val) C.radius (hv i)
    (C.portsAt_on_circle (C.vertexMark i) p) t.val ⟨t.property.1,ht⟩

end Paper170Geometry.DrawingPassages

end
end

section

/-! Actual crossing-disk chord incidence, with no triples inherited from the original drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem innerIndex_eq_of_edge_mark (C : DrawingPassages D) (p q : C.InnerIndex)
    (he : p.1=q.1) (hm : C.innerMark p=C.innerMark q) : p=q := by
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  change e=f at he
  subst f
  congr 1
  apply Subtype.ext
  exact (C.increasing e).injective (D.edge_injective e (congrArg Subtype.val hm))

theorem incomingPort_injective (C : DrawingPassages D) : Function.Injective C.incomingPort := by
  intro p q he
  apply C.innerIndex_eq_of_edge_mark p q (congrArg (fun x : C.Port => x.1.1) he)
  have hh := congrArg C.portMark he
  simpa only [C.incomingPort_mark] using hh

theorem outgoingPort_injective (C : DrawingPassages D) : Function.Injective C.outgoingPort := by
  intro p q he
  apply C.innerIndex_eq_of_edge_mark p q (congrArg (fun x : C.Port => x.1.1) he)
  have hh := congrArg C.portMark he
  simpa only [C.outgoingPort_mark] using hh

theorem incomingPort_ne_outgoingPort (C : DrawingPassages D) (p q : C.InnerIndex) :
    C.incomingPort p ≠ C.outgoingPort q := by
  intro he
  have hh : true=false := congrArg Prod.snd he
  cases hh

theorem incomingPoint_on_circle (C : DrawingPassages D) (p : C.InnerIndex) :
    squaredLength (C.portPoint (C.incomingPort p)-(C.innerMark p).val)=C.radius^2 := by
  simpa only [C.incomingPort_mark] using C.portPoint_on_circle (C.incomingPort p)

theorem outgoingPoint_on_circle (C : DrawingPassages D) (p : C.InnerIndex) :
    squaredLength (C.portPoint (C.outgoingPort p)-(C.innerMark p).val)=C.radius^2 := by
  simpa only [C.outgoingPort_mark] using C.portPoint_on_circle (C.outgoingPort p)

theorem crossing_chords_transverse_at_mark (C : DrawingPassages D) (p q : C.InnerIndex)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    SegmentPairTransverse (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) := by
  apply round_circle_chords_transverse (C.innerMark p).val _ _ _ _ C.radius
  · exact C.incomingPoint_on_circle p
  · exact C.outgoingPoint_on_circle p
  · simpa only [hm] using C.incomingPoint_on_circle q
  · simpa only [hm] using C.outgoingPoint_on_circle q
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p p)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort q q)
  · exact C.portPoint_injective.ne (C.incomingPort_injective.ne hpq)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p q)
  · exact C.portPoint_injective.ne (Ne.symm (C.incomingPort_ne_outgoingPort q p))
  · exact C.portPoint_injective.ne (C.outgoingPort_injective.ne hpq)

theorem innerMark_no_triples (C : DrawingPassages D) (p q r : C.InnerIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpqM : C.innerMark p=C.innerMark q) (hprM : C.innerMark p=C.innerMark r) : False := by
  have heq : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hpqM)
  have her : p.1 ≠ r.1 := fun he => hpr (C.innerIndex_eq_of_edge_mark p r he hprM)
  have hqrM : C.innerMark q=C.innerMark r := hpqM.symm.trans hprM
  have hfr : q.1 ≠ r.1 := fun he => hqr (C.innerIndex_eq_of_edge_mark q r he hqrM)
  have hp : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing p.1 :=
    ⟨C.node p.1 p.2.val,C.inner_parameter_interior p,rfl⟩
  have hq : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing q.1 := by
    rw [hpqM]
    exact ⟨C.node q.1 q.2.val,C.inner_parameter_interior q,rfl⟩
  have hr : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing r.1 := by
    rw [hprM]
    exact ⟨C.node r.1 r.2.val,C.inner_parameter_interior r,rfl⟩
  have hmem : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing p.1 ∩
      Paper170.edgeInterior D.toContinuousDrawing q.1 ∩ Paper170.edgeInterior D.toContinuousDrawing r.1 := ⟨⟨hp,hq⟩,hr⟩
  rw [D.no_triples p.1 q.1 r.1 heq her hfr] at hmem
  exact hmem

end Paper170Geometry.DrawingPassages

end
end

section

/-! The actual first and last retained ports attach to the prescribed graph vertices. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

def firstArc (C : DrawingPassages D) (e : Edge) : C.ArcIndex :=
  ⟨e,⟨0,C.count_pos e⟩⟩

def lastArc (C : DrawingPassages D) (e : Edge) : C.ArcIndex :=
  ⟨e,⟨C.count e-1,by have h := C.count_pos e; omega⟩⟩

theorem lastArc_node (C : DrawingPassages D) (e : Edge) :
    (C.lastArc e).2.succ=Fin.last (C.count e) := by
  apply Fin.ext
  have h := C.count_pos e
  change C.count e-1+1=C.count e
  omega

theorem firstArc_mark (C : DrawingPassages D) (e : Edge) :
    C.arcStartMark (C.firstArc e)=C.vertexMark (graph.src e) := by
  apply Subtype.ext
  change D.edge e (C.node e 0)=D.vertex (graph.src e)
  rw [C.first,Path.source]

theorem lastArc_mark (C : DrawingPassages D) (e : Edge) :
    C.arcEndMark (C.lastArc e)=C.vertexMark (graph.dst e) := by
  apply Subtype.ext
  change D.edge e (C.node e (C.lastArc e).2.succ)=D.vertex (graph.dst e)
  rw [C.lastArc_node,C.last,Path.target]

def startPortAt (C : DrawingPassages D) (e : Edge) : C.PortsAt (C.vertexMark (graph.src e)) :=
  ⟨(C.firstArc e,false),C.firstArc_mark e⟩

def endPortAt (C : DrawingPassages D) (e : Edge) : C.PortsAt (C.vertexMark (graph.dst e)) :=
  ⟨(C.lastArc e,true),C.lastArc_mark e⟩

end Paper170Geometry.DrawingPassages

end
end

section

/-! Actual closed-disk containment and strict interior containment of disk fillings. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem round_chord_in_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    squaredLength (segmentPoint a b t-z) ≤ r^2 := by
  have he : squaredLength (segmentPoint a b t-z)=
      (1-t)*squaredLength (a-z)+t*squaredLength (b-z)-t*(1-t)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hnon : 0 ≤ t*(1-t)*squaredLength (b-a) := by
    apply mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    dsimp [squaredLength]
    positivity
  rw [he,ha,hb]
  linarith

namespace DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem crossingChord_range_subset_disk (C : DrawingPassages D) (p : C.InnerIndex) :
    Set.range (C.crossingChord p) ⊆ closedRoundDisk (C.innerMark p).val C.radius := by
  rintro x ⟨t,rfl⟩
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) ≤ C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_disk _ _ _ _ (C.incomingPoint_on_circle p) (C.outgoingPoint_on_circle p) t.val t.property

theorem crossingChord_interior_in_disk (C : DrawingPassages D) (p : C.InnerIndex)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    squaredLength (C.crossingChord p t-(C.innerMark p).val) < C.radius^2 := by
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) < C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_open_disk _ _ _ _ (C.incomingPoint_on_circle p) (C.outgoingPoint_on_circle p)
    (C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p p)) t.val ht

theorem crossingChords_disjoint_of_marks_ne (C : DrawingPassages D) (p q : C.InnerIndex)
    (hm : C.innerMark p ≠ C.innerMark q) :
    Disjoint (Set.range (C.crossingChord p)) (Set.range (C.crossingChord q)) :=
  (C.disks_disjoint _ _ hm).mono (C.crossingChord_range_subset_disk p) (C.crossingChord_range_subset_disk q)

theorem portPoint_outside_other_disk (C : DrawingPassages D) (p : C.Port) (x : DrawingMark D)
    (hx : C.portMark p ≠ x) : C.radius^2 < squaredLength (C.portPoint p-x.val) := by
  apply lt_of_not_ge
  intro hh
  have hp : C.portPoint p ∈ closedRoundDisk (C.portMark p).val C.radius := (C.portPoint_on_circle p).le
  exact Set.disjoint_left.mp (C.disks_disjoint _ _ hx) hp hh

theorem portPoint_outside_open_disks (C : DrawingPassages D) (p : C.Port) (x : DrawingMark D) :
    C.radius^2 ≤ squaredLength (C.portPoint p-x.val) := by
  by_cases he : C.portMark p=x
  · have hp := C.portPoint_on_circle p
    rw [he] at hp
    exact hp.ge
  · exact (C.portPoint_outside_other_disk p x he).le

theorem crossingChord_avoids_vertex_disks (C : DrawingPassages D) (p : C.InnerIndex)
    (v : Vertex) :
    Disjoint (Set.range (C.crossingChord p)) (closedRoundDisk (D.vertex v) C.radius) := by
  have hn : C.innerMark p ≠ C.vertexMark v := by
    intro he
    exact crossing_not_vertex D (C.innerMark p).val (C.innerMark_is_crossing p) v (congrArg Subtype.val he)
  exact (C.disks_disjoint _ _ hn).mono (C.crossingChord_range_subset_disk p) Set.Subset.rfl

end DrawingPassages
end Paper170Geometry

end
end

section

/-! At most one actual chord crossing point in each original crossing disk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem innerIndex_at_mark_pair (C : DrawingPassages D) (p q r : C.InnerIndex)
    (hpq : p ≠ q) (hpqM : C.innerMark p=C.innerMark q) (hprM : C.innerMark p=C.innerMark r) :
    r=p ∨ r=q := by
  by_cases hrp : r=p
  · exact Or.inl hrp
  by_cases hrq : r=q
  · exact Or.inr hrq
  exact False.elim (C.innerMark_no_triples p q r hpq (Ne.symm hrp) (Ne.symm hrq) hpqM hprM)

def chordCrossingsAt (C : DrawingPassages D) (w : DrawingMark D) : Set Plane :=
  {x | ∃ p q : C.InnerIndex, p ≠ q ∧ C.innerMark p=w ∧ C.innerMark q=w ∧
    x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q)}

theorem chordCrossingsAt_subsingleton (C : DrawingPassages D) (w : DrawingMark D) :
    (C.chordCrossingsAt w).Subsingleton := by
  rintro x ⟨p,q,hpq,hp,hq,hxp,hxq⟩ y ⟨r,s,hrs,hr,hs,hyr,hys⟩
  have hpm : C.innerMark p=C.innerMark q := hp.trans hq.symm
  have hrpair := C.innerIndex_at_mark_pair p q r hpq hpm (hp.trans hr.symm)
  have hspair := C.innerIndex_at_mark_pair p q s hpq hpm (hp.trans hs.symm)
  have hunique := transverse_segment_intersection_subsingleton _ _ _ _
    (C.crossing_chords_transverse_at_mark p q hpq hpm)
  rcases hrpair with rfl | rfl <;> rcases hspair with rfl | rfl
  · exact False.elim (hrs rfl)
  · exact hunique ⟨hxp,hxq⟩ ⟨hyr,hys⟩
  · exact hunique ⟨hxp,hxq⟩ ⟨hys,hyr⟩
  · exact False.elim (hrs rfl)

theorem chord_meeting_marks_eq (C : DrawingPassages D) (p q : C.InnerIndex) {x : Plane}
    (hp : x ∈ Set.range (C.crossingChord p)) (hq : x ∈ Set.range (C.crossingChord q)) :
    C.innerMark p=C.innerMark q := by
  by_contra h
  exact Set.disjoint_left.mp (C.crossingChords_disjoint_of_marks_ne p q h) hp hq

def chordCrossings (C : DrawingPassages D) : Set Plane :=
  {x | ∃ p q : C.InnerIndex, p ≠ q ∧ x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q)}

theorem chord_crossing_original_mark (C : DrawingPassages D) {x : Plane} (hx : x ∈ C.chordCrossings) :
    ∃ w : DrawingMark D, w.val ∈ Paper170.crossingPoints D.toContinuousDrawing ∧ x ∈ C.chordCrossingsAt w := by
  obtain ⟨p,q,hpq,hp,hq⟩ := hx
  refine ⟨C.innerMark p,C.innerMark_is_crossing p,p,q,hpq,rfl,?_,hp,hq⟩
  exact (C.chord_meeting_marks_eq p q hp hq).symm

end Paper170Geometry.DrawingPassages

end
end

section

/-! Count actual spatial chord crossings by their original crossing disks. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
open scoped Classical
variable  {D : FiniteIntersectionDrawing graph}

def chordCrossingOrigin (C : DrawingPassages D) (x : Plane) : Plane :=
  if hx : x ∈ C.chordCrossings then (C.chord_crossing_original_mark hx).choose.val else 0

theorem chordCrossingOrigin_mapsTo (C : DrawingPassages D) :
    Set.MapsTo C.chordCrossingOrigin C.chordCrossings (Paper170.crossingPoints D.toContinuousDrawing) := by
  intro x hx
  have hh := (C.chord_crossing_original_mark hx).choose_spec.1
  simpa only [chordCrossingOrigin,dite_eq_left hx] using hh

theorem chordCrossingOrigin_injOn (C : DrawingPassages D) :
    Set.InjOn C.chordCrossingOrigin C.chordCrossings := by
  intro x hx y hy he
  let w : DrawingMark D := (C.chord_crossing_original_mark hx).choose
  let v : DrawingMark D := (C.chord_crossing_original_mark hy).choose
  have hwx : x ∈ C.chordCrossingsAt w := (C.chord_crossing_original_mark hx).choose_spec.2
  have hvy : y ∈ C.chordCrossingsAt v := (C.chord_crossing_original_mark hy).choose_spec.2
  have hvw : w=v := by
    apply Subtype.ext
    simpa only [chordCrossingOrigin,dite_eq_left hx,dite_eq_left hy] using he
  rw [← hvw] at hvy
  exact (C.chordCrossingsAt_subsingleton w) hwx hvy

theorem chordCrossings_finite (C : DrawingPassages D) : C.chordCrossings.Finite :=
  Set.Finite.of_injOn C.chordCrossingOrigin_mapsTo C.chordCrossingOrigin_injOn D.crossings_finite

end Paper170Geometry.DrawingPassages

end
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

/-! Constructed polygonal exterior paths, packaged with their actual geometric properties. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : FiniteIntersectionDrawing graph}

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

theorem avoids_new_vertices (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : C.ArcIndex) (t : unitInterval) (j : Vertex) : (E.chain i).path t ≠ v j := by
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
end Paper170Geometry

end
end

section

/-! Exterior pieces and crossing chords meet only at their assigned endpoint joins. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Exterior paths meet vertex spokes only at their assigned boundary endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem exterior_spoke_meeting_parameters (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (i : C.ArcIndex) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Ordered actual exterior paths and the internal chords of a fixed edge. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

def orderedArc (C : DrawingPassages D) (e : Edge) (i : ℕ) : C.ArcIndex :=
  ⟨e,⟨min i (C.count e-1),by have h := C.count_pos e; omega⟩⟩

theorem orderedArc_val (C : DrawingPassages D) (e : Edge) (i : ℕ)
    (hi : i < C.count e) : (C.orderedArc e i).2.val=i := by
  change min i (C.count e-1)=i
  omega

theorem orderedArc_inj (C : DrawingPassages D) (e : Edge) (i j : ℕ)
    (hi : i < C.count e) (hj : j < C.count e)
    (h : C.orderedArc e i=C.orderedArc e j) : i=j := by
  have hh := congrArg (fun p : C.ArcIndex => p.2.val) h
  simpa only [C.orderedArc_val e i hi,C.orderedArc_val e j hj] using hh

theorem orderedArc_first (C : DrawingPassages D) (e : Edge) :
    C.orderedArc e 0=C.firstArc e := by
  simp [orderedArc,firstArc]

theorem orderedArc_last (C : DrawingPassages D) (e : Edge) :
    C.orderedArc e (C.count e-1)=C.lastArc e := by
  simp [orderedArc,lastArc]

def orderedInner (C : DrawingPassages D) (e : Edge) (j : ℕ)
    (hj : j+1 < C.count e) : C.InnerIndex :=
  ⟨e,⟨⟨j+1,by omega⟩,⟨Nat.succ_pos j,hj⟩⟩⟩

theorem orderedInner_incoming (C : DrawingPassages D) (e : Edge)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.incomingArc (C.orderedInner e j hj)=C.orderedArc e j := by
  unfold incomingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1-1=min j (C.count e-1)
  omega

theorem orderedInner_outgoing (C : DrawingPassages D) (e : Edge)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.outgoingArc (C.orderedInner e j hj)=C.orderedArc e (j+1) := by
  unfold outgoingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1=min (j+1) (C.count e-1)
  omega

theorem orderedInner_inj (C : DrawingPassages D) (e : Edge) (i j : ℕ)
    (hi : i+1 < C.count e) (hj : j+1 < C.count e)
    (h : C.orderedInner e i hi=C.orderedInner e j hj) : i=j := by
  have hh : i+1=j+1 := congrArg (fun p : C.InnerIndex => p.2.val.val) h
  omega

end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

def orderedPath (E : PolygonalExterior C) (e : Edge) (i : ℕ) :
    Path (C.arcStart (C.orderedArc e i)) (C.arcEnd (C.orderedArc e i)) :=
  (E.chain (C.orderedArc e i)).path

def orderedBridge (C : DrawingPassages D) (e : Edge) (i : ℕ) :
    Path (C.arcEnd (C.orderedArc e i)) (C.arcStart (C.orderedArc e (i+1))) := Path.segment _ _

theorem orderedBridge_apply (e : Edge) (j : ℕ) (hj : j+1 < C.count e)
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

theorem orderedBridge_range (e : Edge) (j : ℕ) (hj : j+1 < C.count e) :
    Set.range (orderedBridge C e j)=Set.range (C.crossingChord (C.orderedInner e j hj)) := by
  congr 1
  funext t
  exact orderedBridge_apply e j hj t

def middlePath (E : PolygonalExterior C) (e : Edge) :
    Path (C.arcStart (C.orderedArc e 0)) (C.arcEnd (C.orderedArc e (C.count e-1))) :=
  alternatingPath (fun i => C.arcStart (C.orderedArc e i))
    (fun i => C.arcEnd (C.orderedArc e i)) (E.orderedPath e) (orderedBridge C e) (C.count e-1)

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! A constructed middle path meets a vertex spoke only at its boundary port. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem vertex_spoke_range_in_disk (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j : Vertex) (p : C.PortsAt (C.vertexMark j)) :
    Set.range (Path.segment (v j) (C.portPoint p.val)) ⊆ closedRoundDisk (D.vertex j) C.radius := by
  rintro x ⟨t,rfl⟩
  by_cases ht : t=1
  · subst t
    rw [Path.target]
    exact (C.portsAt_on_circle (C.vertexMark j) p).le
  · exact (C.vertex_spoke_interior v hv j p t
      (lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht)).le

theorem vertex_spokes_disjoint_of_vertices_ne (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : Vertex) (hjk : j ≠ k)
    (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k)) :
    Disjoint (Set.range (Path.segment (v j) (C.portPoint p.val)))
      (Set.range (Path.segment (v k) (C.portPoint q.val))) :=
  (C.disks_disjoint _ _ (C.vertexMark_injective.ne hjk)).mono
    (C.vertex_spoke_range_in_disk v hv j p) (C.vertex_spoke_range_in_disk v hv k q)

end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

def anchoredMiddle (E : PolygonalExterior C) (e : Edge) :
    Path (C.arcStart (C.firstArc e)) (C.arcEnd (C.lastArc e)) :=
  (E.middlePath e).cast (congrArg C.arcStart (C.orderedArc_first e).symm)
    (congrArg C.arcEnd (C.orderedArc_last e).symm)

theorem anchoredMiddle_range (E : PolygonalExterior C) (e : Edge) :
    Set.range (E.anchoredMiddle e)=Set.range (E.middlePath e) := rfl

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

def startSpoke (C : DrawingPassages D) (v : Vertex → Plane) (e : Edge) :
    Path (v (graph.src e)) (C.arcStart (C.firstArc e)) := Path.segment _ _

def endSpoke (C : DrawingPassages D) (v : Vertex → Plane) (e : Edge) :
    Path (C.arcEnd (C.lastArc e)) (v (graph.dst e)) := (Path.segment _ _).symm

def assembledEdge (E : PolygonalExterior C) (v : Vertex → Plane)
    (e : Edge) : Path (v (graph.src e)) (v (graph.dst e)) :=
  ((startSpoke C v e).trans (E.anchoredMiddle e)).trans (endSpoke C v e)

theorem startSpoke_injective (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge) :
    Function.Injective (startSpoke C v e) := C.vertex_spoke_injective v hv _ (C.startPortAt e)

theorem endSpoke_range (v : Vertex → Plane) (e : Edge) :
    Set.range (endSpoke C v e)=Set.range (Path.segment (v (graph.dst e)) (C.portPoint (C.endPortAt e).val)) := by
  exact Path.symm_range _

theorem endSpoke_injective (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge) :
    Function.Injective (endSpoke C v e) := by
  intro s t he
  have hh := C.vertex_spoke_injective v hv _ (C.endPortAt e) he
  have hval := congrArg Subtype.val hh
  apply Subtype.ext
  change 1-s.val=1-t.val at hval
  linarith

end Paper170Geometry.PolygonalExterior

end
end

section

/-! The assembled replacement is an actual continuous drawing with simple, vertex-avoiding edges. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem vertex_spoke_vertex_eq (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : Vertex) (p : C.PortsAt (C.vertexMark j))
    (hk : v k ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : k=j := by
  by_contra hkj
  have hd := C.disks_disjoint _ _ (C.vertexMark_injective.ne (Ne.symm hkj))
  exact Set.disjoint_left.mp hd (C.vertex_spoke_range_in_disk v hv j p hk) (hv k).le

end DrawingPassages
end Paper170Geometry

end
end

section

/-! Every nonvertex intersection of assembled edges is an actual crossing-disk chord intersection. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem vertex_spokes_meeting (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (j k : Vertex) (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k))
    (hpq : p.val ≠ q.val) (x : Plane)
    (hx : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val)))
    (hy : x ∈ Set.range (Path.segment (v k) (C.portPoint q.val))) : x=v j := by
  by_cases hjk : j=k
  · subst k
    exact spokes_meet_only_at_center _ _ _ (hdet j p q (fun he => hpq (congrArg Subtype.val he)))
      (by simpa only [Path.range_segment] using hx) (by simpa only [Path.range_segment] using hy)
  · exact False.elim (Set.disjoint_left.mp (C.vertex_spokes_disjoint_of_vertices_ne v hv j k hjk p q) hx hy)

end DrawingPassages
end Paper170Geometry

end
end

section

/-! Each actual boundary port belongs to exactly its assigned assembled edge. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem portPoint_mem_exterior (E : PolygonalExterior C) (p : C.Port) :
    C.portPoint p ∈ Set.range (E.chain p.1).path := by
  rcases p with ⟨i,b⟩
  cases b
  · exact ⟨0,(E.chain i).path.source⟩
  · exact ⟨1,(E.chain i).path.target⟩

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
namespace DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

def crossingDisk (C : DrawingPassages D) (p : C.InnerIndex) : Set Plane :=
  {x | squaredLength (x-(C.innerMark p).val) < C.radius^2}

theorem crossingDisk_isOpen (C : DrawingPassages D) (p : C.InnerIndex) : IsOpen (C.crossingDisk p) := by
  apply isOpen_lt _ continuous_const
  unfold squaredLength
  fun_prop

theorem crossingDisk_subset_closed (C : DrawingPassages D) (p : C.InnerIndex) :
    C.crossingDisk p ⊆ closedRoundDisk (C.innerMark p).val C.radius := by
  intro x hx
  exact (show squaredLength (x-(C.innerMark p).val) < C.radius^2 from hx).le

theorem crossingDisk_disjoint_vertex_disk (C : DrawingPassages D) (p : C.InnerIndex)
    (j : Vertex) :
    Disjoint (C.crossingDisk p) (closedRoundDisk (D.vertex j) C.radius) := by
  have hn : C.innerMark p ≠ C.vertexMark j := by
    intro he
    exact crossing_not_vertex D (C.innerMark p).val (C.innerMark_is_crossing p) j (congrArg Subtype.val he)
  exact (C.disks_disjoint _ _ hn).mono (C.crossingDisk_subset_closed p) Set.Subset.rfl

theorem crossingChord_openTrace_iff (C : DrawingPassages D) (p : C.InnerIndex)
    (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Set.range (C.crossingChord p) ↔
      x ∈ openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) := by
  constructor
  · rintro ⟨t,ht⟩
    have ht0 : t ≠ 0 := by
      intro he
      subst t
      rw [Path.source] at ht
      change squaredLength (x-(C.innerMark p).val) < C.radius^2 at hx
      rw [← ht,C.incomingPoint_on_circle] at hx
      exact lt_irrefl _ hx
    have ht1 : t ≠ 1 := by
      intro he
      subst t
      rw [Path.target] at ht
      change squaredLength (x-(C.innerMark p).val) < C.radius^2 at hx
      rw [← ht,C.outgoingPoint_on_circle] at hx
      exact lt_irrefl _ hx
    refine ⟨t.val,⟨?_,?_⟩,?_⟩
    · exact lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
    · exact lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
    · simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  · rintro ⟨t,ht,he⟩
    refine ⟨⟨t,ht.1.le,ht.2.le⟩,?_⟩
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he

end DrawingPassages
end Paper170Geometry

end
end

section

/-! All admissibility conditions and spatial crossing-count nonincrease for the assembled drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem crossingChord_meeting_proper (C : DrawingPassages D) (p q : C.InnerIndex)
    (hpq : p ≠ q) (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ C.crossingDisk p ∧
      Paper170.ProperCrossing
        (openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)))
        (openSegmentTrace (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) x := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have hst : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val =
      segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val := by
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property hst
  refine ⟨?_,?_⟩
  · rw [← hs]
    exact C.crossingChord_interior_in_disk p s hsi
  · constructor
    apply properCrossing_openSegments _ _ _ _ x hd
    · exact ⟨s.val,hsi,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs⟩
    · exact ⟨t.val,hti,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht⟩

end DrawingPassages
end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CrossingReconnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem crossingCoordinates_affine (o u v a b : Plane) (t : ℝ) :
    crossingCoordinates o u v (segmentPoint a b t)=
      segmentPoint (crossingCoordinates o u v a) (crossingCoordinates o u v b) t := by
  apply Prod.ext <;> dsimp [crossingCoordinates,segmentPoint,det2] <;>
    simp only [div_eq_mul_inv] <;> ring

theorem convex_combination_pos (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < (1-t)*a+t*b := by
  have hm : 0 < min a b := lt_min ha hb
  have hl := mul_le_mul_of_nonneg_left (min_le_left a b) (sub_nonneg.mpr ht.2)
  have hr := mul_le_mul_of_nonneg_left (min_le_right a b) ht.1
  nlinarith

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
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Reconnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Crossing reconnection chords and avoidance of vertices and retained arcs. -/

section

/-! The two actual disjoint chords used in an adjacent-crossing surgery disk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : Paper170.AdmissibleDrawing graph}

def reconnectionStart (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) : Plane :=
  if i then C.portPoint (C.incomingPort p) else C.portPoint (C.incomingPort q)

def reconnectionEnd (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) : Plane :=
  if i then C.portPoint (C.outgoingPort q) else C.portPoint (C.outgoingPort p)

theorem reconnection_endpoints_ne (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) :
    C.reconnectionStart p q i ≠ C.reconnectionEnd p q i := by
  cases i
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort q p)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p q)

theorem crossingChord_meeting_segmentsCrossProperly (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hpq : p ≠ q) (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have he : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val=
      segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val := by
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property he
  exact ⟨hd,s.val,hsi,t.val,hti,he⟩

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

theorem reconnection_endpoints_on_circle (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    squaredLength (C.reconnectionStart p q i-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.reconnectionEnd p q i-(C.innerMark p).val)=C.radius^2 := by
  cases i
  · change squaredLength (C.portPoint (C.incomingPort q)-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.portPoint (C.outgoingPort p)-(C.innerMark p).val)=C.radius^2
    exact ⟨by simpa only [hm] using C.incomingPoint_on_circle q,C.outgoingPoint_on_circle p⟩
  · change squaredLength (C.portPoint (C.incomingPort p)-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.portPoint (C.outgoingPort q)-(C.innerMark p).val)=C.radius^2
    exact ⟨C.incomingPoint_on_circle p,by simpa only [hm] using C.outgoingPoint_on_circle q⟩

theorem reconnection_open_in_disk (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    openSegmentTrace (C.reconnectionStart p q i) (C.reconnectionEnd p q i) ⊆ C.crossingDisk p := by
  rintro x ⟨t,ht,rfl⟩
  exact round_chord_in_open_disk _ _ _ _ (C.reconnection_endpoints_on_circle p q hm i).1
    (C.reconnection_endpoints_on_circle p q hm i).2 (C.reconnection_endpoints_ne p q i) t ht

end Paper170Geometry.DrawingPassages

end
end

section

/-! The new closed chords stay in their crossing disk and avoid all placed vertices. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : Paper170.AdmissibleDrawing graph}

theorem reconnection_segment_in_disk (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) ⊆
      closedRoundDisk (C.innerMark p).val C.radius := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  rw [← ht]
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) ≤ C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_disk _ _ _ _ (C.reconnection_endpoints_on_circle p q hm i).1
    (C.reconnection_endpoints_on_circle p q hm i).2 t.val t.property

theorem reconnection_segment_avoids_vertices (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (i : Bool) (j : Vertex) :
    v j ∉ segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) := by
  intro hx
  have hn : C.innerMark p ≠ C.vertexMark j := by
    intro he
    exact crossing_not_vertex D.toFiniteIntersectionDrawing (C.innerMark p).val (C.innerMark_is_crossing p) j (congrArg Subtype.val he)
  exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
    (C.reconnection_segment_in_disk p q hm i hx) (hv j).le

end Paper170Geometry.DrawingPassages

end
end

section

/-! Neither reconnection segment contains the actual point being removed. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem segment_avoids_of_affine_positive (f : Plane → ℝ) (a b x : Plane)
    (hf : ∀ t, f (segmentPoint a b t)=(1-t)*f a+t*f b)
    (ha : 0 < f a) (hb : 0 < f b) (hx : f x=0) : x ∉ segment ℝ a b := by
  intro h
  rw [← Path.range_segment] at h
  obtain ⟨t,ht⟩ := h
  have ht' : segmentPoint a b t.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have hp := convex_combination_pos (f a) (f b) t.val ha hb t.property
  rw [← hf t.val,ht',hx] at hp
  exact lt_irrefl 0 hp

theorem crossing_reconnections_avoid_point (a b c d x : Plane)
    (hd : det2 (b-a) (d-c) ≠ 0) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x=segmentPoint a b s) (hy : x=segmentPoint c d t) :
    x ∉ segment ℝ c b ∧ x ∉ segment ℝ a d := by
  let F := crossingCoordinates x (b-a) (d-c)
  have hFa : F a=(-s,0) := by
    simpa only [segmentPoint_zero,zero_sub] using crossingCoordinates_first_segment a b c d x s 0 hd hx
  have hFb : F b=(1-s,0) := by
    simpa only [segmentPoint_one] using crossingCoordinates_first_segment a b c d x s 1 hd hx
  have hFc : F c=(0,-t) := by
    simpa only [segmentPoint_zero,zero_sub] using crossingCoordinates_second_segment a b c d x t 0 hd hy
  have hFd : F d=(0,1-t) := by
    simpa only [segmentPoint_one] using crossingCoordinates_second_segment a b c d x t 1 hd hy
  have hF (u v : Plane) (r : ℝ) : F (segmentPoint u v r)=segmentPoint (F u) (F v) r :=
    crossingCoordinates_affine x (b-a) (d-c) u v r
  have hzero : F x=(0,0) := crossingCoordinates_origin x (b-a) (d-c)
  constructor
  · apply segment_avoids_of_affine_positive (fun z => (F z).1-(F z).2) c b x
    · intro r
      rw [hF]
      dsimp [segmentPoint]
      ring
    · rw [hFc]
      dsimp
      linarith [ht.1]
    · rw [hFb]
      dsimp
      linarith [hs.2]
    · rw [hzero]
      norm_num
  · apply segment_avoids_of_affine_positive (fun z => (F z).2-(F z).1) a d x
    · intro r
      rw [hF]
      dsimp [segmentPoint]
      ring
    · rw [hFa]
      dsimp
      linarith [hs.1]
    · rw [hFd]
      dsimp
      linarith [ht.2]
    · rw [hzero]
      norm_num

theorem DrawingPassages.reconnection_avoids_chord_meeting  {D : Paper170.AdmissibleDrawing graph}
    (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ C.crossingDisk p ∧ ∀ i : Bool,
      x ∉ segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have hs' : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val=x := by
    simpa only [DrawingPassages.crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val=x := by
    simpa only [DrawingPassages.crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property
    (hs'.trans ht'.symm)
  constructor
  · change squaredLength (x-(C.innerMark p).val) < C.radius^2
    rw [← hs]
    exact C.crossingChord_interior_in_disk p s hsi
  · have ha := crossing_reconnections_avoid_point _ _ _ _ x hd s.val t.val hsi hti hs'.symm ht'.symm
    intro i
    cases i
    · exact ha.1
    · exact ha.2

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ExteriorSegmentGraph
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
-- module Solutions.OAIQ4_Cc.Crossing_DrawingWalkCutTraces
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

end Zarankiewicz

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

def crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) : SimpleGraph Plane :=
  segmentAugmentedGraph (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p))
    (C.reconnectionStart p q) (C.reconnectionEnd p q) (C.reconnection_endpoints_ne p q)

theorem exterior_le_crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) :
    exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p) ≤ crossingSurgeryGraph C P p q :=
  le_segmentAugmentedGraph _ _ _ _

end Paper170Geometry

end
end

section

/-! Actual prefix and suffix walks transferred to the constructed surgery graph. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

def surgeryPrefixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (i : ℕ) (hi : (drawingEdgeWalk P r.1).getVert i=C.portPoint (C.incomingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src r.1))) (C.portPoint (C.incomingPort r)) :=
  ((exteriorGraphWalk ((drawingEdgeWalk P r.1).take i) (C.crossingDisk p) hout).mapLe
    (exterior_le_crossingSurgeryGraph C P p q)).copy rfl hi

def surgerySuffixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (j : ℕ) (hj : (drawingEdgeWalk P r.1).getVert j=C.portPoint (C.outgoingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex ((graph.dst r.1))) :=
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

end Paper170Geometry

end
end

section

/-! Ordered actual cut data, whose existence is proved for the constructed normalization. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

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
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src r.1))) (C.portPoint (C.incomingPort r)) :=
  surgeryPrefixWalk C P p q r K.first.val K.first_point (by
    simpa only [DrawingPassages.crossingDisk,hr] using K.prefix_outside)

def suffixInSurgery (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex ((graph.dst r.1))) :=
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
end Paper170Geometry

end
end

section

/-! Simple actual polygonal paths obtained from transferred tracks and one new chord. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

def walkThroughChord {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) : G.Walk a b :=
  (A.append h.toWalk).append B

end Paper170Geometry

end
end

section

/-! Actual drawing prefixes and suffixes meet vertices only at their retained endpoint. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

namespace ExteriorCrossingCut
variable {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {r : C.InnerIndex}

theorem first_parameter_lt_one (K : ExteriorCrossingCut C P r) : (P r.1).knot K.first < 1 := by
  rw [← (P r.1).last]
  exact (P r.1).increasing (K.ordered.trans_le (Fin.le_last _))

theorem last_parameter_pos (K : ExteriorCrossingCut C P r) : 0 < (P r.1).knot K.last := by
  rw [← (P r.1).first]
  exact (P r.1).increasing ((Fin.zero_le K.first).trans_lt K.ordered)

theorem prefix_vertex_eq (K : ExteriorCrossingCut C P r) (v : Vertex)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val))) :
    v=(graph.src r.1) := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨_,hv⟩ | ⟨ht1,_⟩
  · exact hv
  · exact False.elim ((ht1 ▸ ht.2).not_gt K.first_parameter_lt_one)

theorem suffix_vertex_eq (K : ExteriorCrossingCut C P r) (v : Vertex)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val))) :
    v=(graph.dst r.1) := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨ht0,_⟩ | ⟨_,hv⟩
  · exact False.elim ((ht0 ▸ ht.1).not_gt K.last_parameter_pos)
  · exact hv

end ExteriorCrossingCut
end Paper170Geometry

end
end

section

/-! Actual retained cuts are disjoint and contain only their own boundary port. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.ExteriorCrossingCut
variable  {D D' : Paper170.AdmissibleDrawing graph}
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

end Paper170Geometry.ExteriorCrossingCut

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

/-! Replacement of two actual drawing routes with proved simple, vertex-avoiding paths. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170.ContinuousDrawing
def replaceTwoRoutes (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (g : Edge) : Path (D.vertex ((graph.src g))) (D.vertex ((graph.dst g))) := by
  classical
  exact if h : g=e then γ.cast (congrArg (fun k : Edge => D.vertex ((graph.src k))) h)
    (congrArg (fun k : Edge => D.vertex ((graph.dst k))) h)
  else if h : g=f then δ.cast (congrArg (fun k : Edge => D.vertex ((graph.src k))) h)
    (congrArg (fun k : Edge => D.vertex ((graph.dst k))) h)
  else D.edge g

theorem replaceTwoRoutes_first (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f)))) :
    D.replaceTwoRoutes e f γ δ e=γ := by
  simp only [replaceTwoRoutes,dite_eq_left rfl,Path.cast_rfl_rfl]

theorem replaceTwoRoutes_second (D : Paper170.ContinuousDrawing graph) (e f : Edge) (hef : e ≠ f)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f)))) :
    D.replaceTwoRoutes e f γ δ f=δ := by
  simp only [replaceTwoRoutes,dite_eq_right (Ne.symm hef),dite_eq_left rfl,Path.cast_rfl_rfl]

theorem replaceTwoRoutes_other (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (g : Edge) (hge : g ≠ e) (hgf : g ≠ f) :
    D.replaceTwoRoutes e f γ δ g=D.edge g := by
  simp only [replaceTwoRoutes,dite_eq_right hge,dite_eq_right hgf]

def replaceTwoEdges (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hvγ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, γ t ≠ D.vertex j)
    (hvδ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, δ t ≠ D.vertex j) :
    Paper170.ContinuousDrawing graph where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.replaceTwoRoutes e f γ δ
  edge_injective := by
    intro g
    classical
    by_cases hge : g=e
    · subst g
      rw [replaceTwoRoutes_first]
      exact hγ
    by_cases hgf : g=f
    · subst g
      rw [replaceTwoRoutes_second _ _ _ (Ne.symm hge)]
      exact hδ
    · rw [replaceTwoRoutes_other _ _ _ _ _ _ hge hgf]
      exact D.edge_injective g
  interior_avoids_vertices := by
    intro g t ht j
    classical
    by_cases hge : g=e
    · subst g
      rw [replaceTwoRoutes_first]
      exact hvγ t ht j
    by_cases hgf : g=f
    · subst g
      rw [replaceTwoRoutes_second _ _ _ (Ne.symm hge)]
      exact hvδ t ht j
    · rw [replaceTwoRoutes_other _ _ _ _ _ _ hge hgf]
      exact D.interior_avoids_vertices g t ht j

end Paper170.ContinuousDrawing

end
end

section

/-! Trace case analysis for the actual two-route replacement. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170.ContinuousDrawing
theorem replaceTwoRoutes_range_cases (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (g : Edge) (x : Plane) (hx : x ∈ Set.range (D.replaceTwoRoutes e f γ δ g)) :
    (g=e ∧ x ∈ Set.range γ) ∨ (g=f ∧ x ∈ Set.range δ) ∨
      (g ≠ e ∧ g ≠ f ∧ x ∈ Set.range (D.edge g)) := by
  classical
  by_cases hge : g=e
  · subst g
    exact Or.inl ⟨rfl,by simpa only [replaceTwoRoutes_first] using hx⟩
  by_cases hgf : g=f
  · subst g
    exact Or.inr (Or.inl ⟨rfl,by simpa only [replaceTwoRoutes_second D e f (Ne.symm hge)] using hx⟩)
  · exact Or.inr (Or.inr ⟨hge,hgf,by simpa only [replaceTwoRoutes_other D e f γ δ g hge hgf] using hx⟩)

end Paper170.ContinuousDrawing

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_NodeMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def nodePolynomial (node : ι → ℝ) : ℝ[X] := ∏ i, (X-C (node i))

def derivativeAtNode (node : ι → ℝ) (i : ι) : ℝ :=
  (nodePolynomial node).derivative.eval (node i)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_AlgebraDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial spaces, interpolation weights, crossing tensors, and support evaluation. -/

section

/-! Polynomial spaces and crossing tensors for complete graphs.

These definitions contain no mathematical theorem assumptions. -/

open scoped BigOperators Classical

noncomputable section

namespace Paper170

abbrev Poly2 := MvPolynomial (Fin 2) ℝ
abbrev Poly4 := MvPolynomial (Fin 4) ℝ

def nodeWeight {ι : Type*} [Fintype ι] (node : ι → ℝ) (i : ι) : ℝ :=
  (Zarankiewicz.derivativeAtNode node i)⁻¹

def omittedNodePolynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (i : ι) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (node j))

def rectangle (a b : ℕ) : Submodule ℝ Poly2 :=
  MvPolynomial.degreesLE ℝ (Fin 2)
    (Multiset.replicate a 0 + Multiset.replicate b 1)

def box4 (d : ℕ) : Submodule ℝ Poly4 :=
  MvPolynomial.degreesLE ℝ (Fin 4) (d • (Finset.univ : Finset (Fin 4)).val)

def swapFirstPair : Poly4 →ₗ[ℝ] Poly4 :=
  (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 1)).toLinearMap

def swapSecondPair : Poly4 →ₗ[ℝ] Poly4 :=
  (MvPolynomial.rename (Equiv.swap (2 : Fin 4) 3)).toLinearMap

def endpointSymmetricSpace (s : ℕ) : Submodule ℝ Poly4 :=
  box4 (s - 2) ⊓ LinearMap.ker (swapFirstPair - LinearMap.id) ⊓
    LinearMap.ker (swapSecondPair - LinearMap.id)

def evalTwo (u v : ℝ) : Poly2 →ₗ[ℝ] ℝ :=
  (MvPolynomial.aeval ![u, v]).toLinearMap

def evalFour (x u y v : ℝ) : Poly4 →ₗ[ℝ] ℝ :=
  (MvPolynomial.aeval ![x, u, y, v]).toLinearMap

/-- The manuscript's one-based L_s, translated to zero-based Fin indices. -/
def evenTriangle (s : ℕ) : Finset (Fin (2 * s) × Fin (2 * s)) :=
  Finset.univ.filter fun pq =>
    (pq.1.val < s ∧ pq.2 < pq.1) ∨ (s ≤ pq.1.val ∧ pq.1 < pq.2)

abbrev EvenTriangleCoord (s : ℕ) := ↥(evenTriangle s)

def triangleEvaluation (s a b : ℕ) (node : Fin (2 * s) → ℝ) :
    rectangle a b →ₗ[ℝ] (EvenTriangleCoord s → ℝ) :=
  LinearMap.pi fun pq =>
    (evalTwo (node pq.val.1) (node pq.val.2)).comp (rectangle a b).subtype

def halfOrder {ι : Type*} (order : LinearOrder ι) (p q : ι) : ℝ :=
  letI := order
  if p < q then 1 / 2 else if q < p then -(1 / 2) else 0

def weightedPairing {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (K : ι → ι → ℝ) (A B : Poly2) : ℝ :=
  ∑ p, ∑ q, K p q * (node p - node q) /
    (Zarankiewicz.derivativeAtNode node p * Zarankiewicz.derivativeAtNode node q) *
    evalTwo (node p) (node q) A * evalTwo (node p) (node q) B

def orderPairing {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (order : LinearOrder ι) (A B : Poly2) : ℝ :=
  weightedPairing node (halfOrder order) A B

abbrev CrossingTensor (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

def chainBoundary {n : ℕ} (z : Fin n → Fin n → ℝ) (v : Fin n) : ℝ :=
  (∑ i, z i v) - ∑ p, z v p

def chainPairing {n : ℕ} (J : CrossingTensor n)
    (z z' : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ p, ∑ k, ∑ q, J i p k q * z i p * z' k q

def polynomialTest {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (H : Poly4) : ℝ :=
  ∑ i, ∑ p, ∑ k, ∑ q, J i p k q * nodeWeight node i * nodeWeight node p *
    nodeWeight node k * nodeWeight node q * evalFour (node i) (node p) (node k) (node q) H

/-- Canonical orientation within each edge; the two edges remain ordered. -/
def supportedPairs {n : ℕ} (J : CrossingTensor n) :
    Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
  Finset.univ.filter fun a =>
    a.1.1 < a.1.2 ∧ a.2.1 < a.2.2 ∧
    a.1.1 ≠ a.2.1 ∧ a.1.1 ≠ a.2.2 ∧
    a.1.2 ≠ a.2.1 ∧ a.1.2 ≠ a.2.2 ∧
    J a.1.1 a.1.2 a.2.1 a.2.2 ≠ 0

abbrev SupportCoord {n : ℕ} (J : CrossingTensor n) := ↥(supportedPairs J)

def supportEvaluation {n : ℕ} (s : ℕ) (node : Fin n → ℝ) (J : CrossingTensor n) :
    endpointSymmetricSpace s →ₗ[ℝ] (SupportCoord J → ℝ) :=
  LinearMap.pi fun a => (evalFour (node a.val.1.1) (node a.val.1.2)
    (node a.val.2.1) (node a.val.2.2)).comp (endpointSymmetricSpace s).subtype

/-- C=(x-y)(x-v)(u-y)(u-v), with coordinates x,u,y,v. -/
def collisionFactor : Poly4 :=
  (MvPolynomial.X 0 - MvPolynomial.X 2) *
  (MvPolynomial.X 0 - MvPolynomial.X 3) *
  (MvPolynomial.X 1 - MvPolynomial.X 2) *
  (MvPolynomial.X 1 - MvPolynomial.X 3)

/-- The complete six-difference product in the source's stated order. -/
def fullDifference : Poly4 :=
  (MvPolynomial.X 0 - MvPolynomial.X 1) *
  (MvPolynomial.X 2 - MvPolynomial.X 3) * collisionFactor

/-- Substitute x=y=t, leaving u,v as the two variables. -/
def vertexSpecialization (t : ℝ) : Poly4 →ₐ[ℝ] Poly2 :=
  MvPolynomial.aeval ![MvPolynomial.C t, MvPolynomial.X 0,
    MvPolynomial.C t, MvPolynomial.X 1]

/-- Substitute y=x, leaving x,u,v as three variables. -/
def diagonalSpecialization : Poly4 →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1,
    MvPolynomial.X 0, MvPolynomial.X 2]

def supportDiagonal {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (a : SupportCoord J) : ℝ :=
  J a.val.1.1 a.val.1.2 a.val.2.1 a.val.2.2 *
    nodeWeight node a.val.1.1 * nodeWeight node a.val.1.2 *
    nodeWeight node a.val.2.1 * nodeWeight node a.val.2.2 *
    evalFour (node a.val.1.1) (node a.val.1.2) (node a.val.2.1) (node a.val.2.2)
      fullDifference

def supportBilinear {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) :
    LinearMap.BilinForm ℝ (SupportCoord J → ℝ) :=
  Matrix.toBilin' (Matrix.diagonal (supportDiagonal node J))

def weightedChain {n : ℕ} (node : Fin n → ℝ) (a b : ℕ) (i p : Fin n) : ℝ :=
  nodeWeight node i * nodeWeight node p * node i ^ a * node p ^ b

def collisionFactors : Fin 4 → Poly4 :=
  ![MvPolynomial.X 0 - MvPolynomial.X 2,
    MvPolynomial.X 0 - MvPolynomial.X 3,
    MvPolynomial.X 1 - MvPolynomial.X 2,
    MvPolynomial.X 1 - MvPolynomial.X 3]

def liftUnivariate (i : Fin 4) (U : Polynomial ℝ) : Poly4 :=
  Polynomial.aeval (MvPolynomial.X i) U

def liftBivariate (i j : Fin 4) (B : Poly2) : Poly4 :=
  MvPolynomial.aeval ![MvPolynomial.X i, MvPolynomial.X j] B

def localTestPolynomial (P : Poly4) (U V : Polynomial ℝ) (B : Poly2) : Poly4 :=
  P * (MvPolynomial.X 1 - MvPolynomial.X 3) *
    (MvPolynomial.X 1 - MvPolynomial.X 2) * (MvPolynomial.X 3 - MvPolynomial.X 0) *
    liftUnivariate 0 U * liftUnivariate 2 V * liftBivariate 1 3 B

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Plane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Planar segment geometry, affine parametrizations, and oriented arc directions. -/

section

/-! Generic planar ingredients reused through exact definitions of actual paths. -/
noncomputable section
open Set
open scoped BigOperators Classical

namespace Paper170

theorem segmentPoint_eq (a b : Plane) (t : ℝ) :
    segmentPoint a b t = Zarankiewicz.segmentPoint a b t := rfl

/-- Transfer a genuine affine parametrization, retaining the identical path and knots. -/
def ofZarankiewiczParametrization {a b : Plane} {γ : Path a b}
    (P : Zarankiewicz.PolygonalParametrization γ) : PolygonalParametrization γ where
  pieces := P.pieces
  positive := by
    by_contra hn
    have hp : P.pieces = 0 := by omega
    have hi : (0 : Fin (P.pieces+1)) = Fin.last P.pieces := by
      apply Fin.ext
      exact hp.symm
    have he := P.first.symm.trans ((congrArg P.knot hi).trans P.last)
    exact zero_ne_one he
  knot := P.knot
  increasing := P.increasing
  first := P.first
  last := P.last
  affine := by
    intro i t hlo hhi
    have hlt : P.knot i.castSucc < P.knot i.succ := P.increasing Fin.castSucc_lt_succ
    obtain ⟨u,hu⟩ := Zarankiewicz.intervalSegment_surjective_interval
      (P.knot i.castSucc) (P.knot i.succ) hlt t ⟨hlo,hhi⟩
    have he := P.affine i u
    rw [hu] at he
    have hp := congrArg Subtype.val hu
    have hd : (P.knot i.succ : ℝ) - P.knot i.castSucc ≠ 0 := sub_ne_zero.mpr (ne_of_gt (show (P.knot i.castSucc : ℝ) < P.knot i.succ from hlt))
    have hquot : ((t : ℝ) - P.knot i.castSucc) /
        ((P.knot i.succ : ℝ) - P.knot i.castSucc) = (u : ℝ) := by
      apply (div_eq_iff hd).mpr
      dsimp [Zarankiewicz.intervalSegment] at hp
      nlinarith
    rw [hquot]
    exact he

theorem squaredLength_pos {x : Plane} (hx : x ≠ 0) : 0 < squaredLength x := by
  have h0 : 0 ≤ x.1^2 := sq_nonneg x.1
  have h1 : 0 ≤ x.2^2 := sq_nonneg x.2
  change 0 < x.1^2 + x.2^2
  by_contra hh
  have ha : x.1 = 0 := by nlinarith
  have hb : x.2 = 0 := by nlinarith
  exact hx (Prod.ext ha hb)

theorem inversion_involutive : Function.Involutive inversion := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [inversion, squaredLength]
  · have hq : squaredLength x ≠ 0 := ne_of_gt (squaredLength_pos hx)
    have hlen : squaredLength (inversion x) = (squaredLength x)⁻¹ := by
      change (x.1 / squaredLength x)^2 + (x.2 / squaredLength x)^2 = _
      rw [div_pow, div_pow, ← add_div]
      change squaredLength x / squaredLength x ^ 2 = (squaredLength x)⁻¹
      field_simp [hq]
    rw [inversion, hlen]
    apply Prod.ext <;> simp [inversion, hq]

theorem inversion_fixes_circle (x : Plane) (hx : squaredLength x = 1) : inversion x = x := by
  simp [inversion, hx]

end Paper170

end
end

section

/-! The frozen subdivision and the reused geometric subdivision describe the same path. -/
noncomputable section
open Set
open scoped Classical
namespace Paper170

def toZarankiewiczParametrization {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : Zarankiewicz.PolygonalParametrization γ where
  pieces := P.pieces
  knot := P.knot
  increasing := P.increasing
  first := P.first
  last := P.last
  affine := by
    intro i t
    have hlt : P.knot i.castSucc < P.knot i.succ := P.increasing Fin.castSucc_lt_succ
    have hlohi := Zarankiewicz.intervalSegment_between
      (P.knot i.castSucc) (P.knot i.succ) t hlt.le
    have he := P.affine i _ hlohi.1 hlohi.2
    have hd : (P.knot i.succ : ℝ) - P.knot i.castSucc ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt (show (P.knot i.castSucc : ℝ) < P.knot i.succ from hlt))
    have hquot : (((Zarankiewicz.intervalSegment (P.knot i.castSucc) (P.knot i.succ) t :
        unitInterval) : ℝ) - P.knot i.castSucc) /
          ((P.knot i.succ : ℝ) - P.knot i.castSucc) = (t : ℝ) := by
      apply (div_eq_iff hd).mpr
      dsimp [Zarankiewicz.intervalSegment]
      ring
    rw [hquot] at he
    exact he

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_OrientedSimilarity
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
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Angles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spoke angles, circle angles, scaling, and coordinate frames. -/

section

noncomputable section
open scoped Classical
namespace Paper170

def complexPoint (a : Plane) : ℂ := ⟨a.1, a.2⟩

@[simp] lemma complexPoint_zero : complexPoint 0 = 0 := rfl

@[simp] lemma complexPoint_smul (r : ℝ) (a : Plane) :
    complexPoint (r • a) = (r : ℂ) * complexPoint a := by
  apply Complex.ext <;> simp [complexPoint]

end Paper170

end
end

section

noncomputable section
open scoped Classical
namespace Paper170

def angleRotation (cut : ℝ) (a : Plane) : Plane :=
  Zarankiewicz.similarityPoint 0
    ((Complex.exp (-(cut : ℂ) * Complex.I)).re, (Complex.exp (-(cut : ℂ) * Complex.I)).im) a

end Paper170

end
end

section

noncomputable section
open Zarankiewicz
namespace Paper170

def angleCoordinateFrame (cut radius : ℝ) : Plane :=
  radius • (((Complex.exp (-(cut:ℂ)*Complex.I))⁻¹).re,
    ((Complex.exp (-(cut:ℂ)*Complex.I))⁻¹).im)

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Hill
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harary–Hill arithmetic, residue-page definitions, and the even-order deletion inequality. -/

section

/-! The Harary–Hill formula and two-page crossing counts.

-/

open scoped BigOperators
noncomputable section
namespace Paper170

/-- The two contiguous residue blocks used by the explicit drawing. -/
def residueColor (n r : ℕ) : Bool := decide (r % n < n / 2)

/-- Increasing four-tuples whose alternating edges occupy the same page. -/
def crossingTuples (n : ℕ) : Finset (Fin 4 → Fin n) := by
  classical
  exact Finset.univ.filter (fun v => StrictMono v ∧
    residueColor n ((v 0).val + (v 2).val) =
      residueColor n ((v 1).val + (v 3).val))

/-- Residues with the same color after a cyclic shift by k. -/
def sameColorResidues (n k : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun r => residueColor n r = residueColor n (r + k))

/-- Cyclic starting points and the first two positive gaps in the source count. -/
def sameColorGapTuples (n k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range n) ×ˢ ((Finset.Icc 1 (k - 1)) ×ˢ (Finset.Icc 1 (n - k - 1)))).filter
    (fun v => residueColor n (2 * v.1 + v.2.1 + v.2.2) =
      residueColor n (2 * v.1 + v.2.1 + v.2.2 + k))

/-- Starting labels producing a prescribed diagonal-sum residue. -/
def residueFiber (n b r : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a => (2 * a + b) % n = r)

/-- One parity class of the same-color residues. -/
def sameColorResiduesParity (n k p : ℕ) : Finset ℕ :=
  (sameColorResidues n k).filter (fun r => r % 2 = p)

/-- One parity class of the first-gap choices after a fixed offset. -/
def firstGapParity (k b p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (k - 1)).filter (fun g => (g + b) % 2 = p)

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CircleArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle segments, inversion, continuous paths, and admissibility of two-page arcs. -/

section

/-! Exact circle and inversion routes for the source's two-page drawing.

 -/

noncomputable section
open Set
open scoped Classical

namespace Paper170

def chordInterior {n : ℕ} (p : Fin n → Plane) (e : CompleteEdge n) : Set Plane :=
  (segmentPoint (p e.val.1) (p e.val.2)) '' Ioo (0 : ℝ) 1

/-- The source's generic circle placement, stated only in geometric terms. -/
structure CircleConfiguration (n : ℕ) where
  point : Fin n → Plane
  injective : Function.Injective point
  on_circle : ∀ i, squaredLength (point i) = 1
  cyclic_order : ∀ i j k, i < j → j < k →
    0 < det2 (point j - point i) (point k - point i)
  no_antipodal : ∀ i j, i ≠ j → point i + point j ≠ 0
  no_triple_chords : ∀ e f g : CompleteEdge n, e ≠ f → e ≠ g → f ≠ g →
    chordInterior point e ∩ chordInterior point f ∩ chordInterior point g = ∅

def twoPageRoute {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n)
    (t : unitInterval) : Plane :=
  let x := segmentPoint (C.point e.val.1) (C.point e.val.2) t.val
  if residueColor n (e.val.1.val + e.val.2.val) then x else inversion x

/-- Equality with the actual circle/chord/inversion construction. -/
structure TwoPageDrawing {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) : Prop where
  vertex_eq : D.vertex = C.point
  edge_eq : ∀ e t, D.edge e t = twoPageRoute C e t

def lineIntersectionPoint (a b c d : Plane) : Plane :=
  a + (det2 (c - a) (d - c) / det2 (b - a) (d - c)) • (b - a)

def crossingTuplePoint {n : ℕ} (C : CircleConfiguration n) (v : Fin 4 → Fin n) : Plane :=
  let x := lineIntersectionPoint (C.point (v 0)) (C.point (v 2))
    (C.point (v 1)) (C.point (v 3))
  if residueColor n ((v 0).val + (v 2).val) then x else inversion x

end Paper170

end
end

section

noncomputable section
open Set
namespace Paper170

theorem chordInterior_eq_unitIntervalImage {n : ℕ} (p : Fin n → Plane) (e : CompleteEdge n) :
    chordInterior p e =
      (fun t : unitInterval => segmentPoint (p e.val.1) (p e.val.2) t.val) ''
        Ioo (0 : unitInterval) 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht.1.le, ht.2.le⟩, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.val, ht, rfl⟩

theorem twoPageRoute_image {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    twoPageRoute C e '' Ioo (0 : unitInterval) 1 =
      if residueColor n (e.val.1.val + e.val.2.val) then chordInterior C.point e
      else inversion '' chordInterior C.point e := by
  change (fun t => twoPageRoute C e t) '' _ = _
  cases hc : residueColor n (e.val.1.val + e.val.2.val) <;>
    simp [twoPageRoute, hc, chordInterior_eq_unitIntervalImage, Set.image_image]

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem circle_points_noncollinear {n : ℕ} (p : Fin n → Plane)
    (hp : Function.Injective p) (hc : ∀ i, squaredLength (p i) = 1)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Zarankiewicz.orient2 (p i) (p j) (p k) ≠ 0 := by
  apply Zarankiewicz.round_circle_orient_ne_zero 0 (p i) (p j) (p k) 1
  · simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using hc i
  · simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using hc j
  · simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using hc k
  · exact hp.ne hij
  · exact hp.ne hik
  · exact hp.ne hjk

theorem open_chord_reverse {a b x : Plane} (hx : x ∈ Zarankiewicz.openSegmentTrace a b) :
    x ∈ Zarankiewicz.openSegmentTrace b a := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    Zarankiewicz.segmentPoint_reverse a b t⟩

theorem open_chords_common_start {a b c x : Plane}
    (hn : Zarankiewicz.orient2 a b c ≠ 0)
    (hx : x ∈ Zarankiewicz.openSegmentTrace a b)
    (hy : x ∈ Zarankiewicz.openSegmentTrace a c) : False := by
  obtain ⟨t, ht, he⟩ := hx
  obtain ⟨u, hu, hf⟩ := hy
  have hz := congrArg (Zarankiewicz.orient2 a b) (he.trans hf.symm)
  rw [Zarankiewicz.orient2_self_segment, Zarankiewicz.orient2_segment] at hz
  have ha : Zarankiewicz.orient2 a b a = 0 := by simp [Zarankiewicz.orient2, Zarankiewicz.det2]
  rw [ha, mul_zero, zero_add] at hz
  exact hn ((mul_eq_zero.mp hz.symm).resolve_left (ne_of_gt hu.1))

theorem circle_chord_endpoints_distinct {n : ℕ} (p : Fin n → Plane)
    (hp : Function.Injective p) (hc : ∀ i, squaredLength (p i) = 1)
    (e f : CompleteEdge n) (hef : e ≠ f) (x : Plane)
    (he : x ∈ chordInterior p e) (hf : x ∈ chordInterior p f) :
    e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2 ∧ e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2 := by
  have he' : x ∈ Zarankiewicz.openSegmentTrace (p e.val.1) (p e.val.2) := he
  have hf' : x ∈ Zarankiewicz.openSegmentTrace (p f.val.1) (p f.val.2) := hf
  have hei : e.val.1 < e.val.2 := e.property
  have hfi : f.val.1 < f.val.2 := f.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hother : e.val.2 ≠ f.val.2 := by
      intro hh
      exact hef (Subtype.ext (Prod.ext h hh))
    have hn := circle_points_noncollinear p hp hc (ne_of_lt hei)
      (show e.val.1 ≠ f.val.2 by rw [h]; exact ne_of_lt hfi) hother
    rw [← h] at hf'
    exact open_chords_common_start hn he' hf'
  · intro h
    have hn := circle_points_noncollinear p hp hc (ne_of_lt hei)
      (show e.val.1 ≠ f.val.1 by rw [h]; exact ne_of_gt hfi) (by omega)
    have hf'' := open_chord_reverse hf'
    rw [← h] at hf''
    exact open_chords_common_start hn he' hf''
  · intro h
    have hn := circle_points_noncollinear p hp hc (ne_of_gt hei)
      (show e.val.2 ≠ f.val.2 by rw [h]; exact ne_of_lt hfi) (by omega)
    have he'' := open_chord_reverse he'
    rw [← h] at hf'
    exact open_chords_common_start hn he'' hf'
  · intro h
    have hother : e.val.1 ≠ f.val.1 := by
      intro hh
      exact hef (Subtype.ext (Prod.ext hh h))
    have hn := circle_points_noncollinear p hp hc (ne_of_gt hei)
      (show e.val.2 ≠ f.val.1 by rw [h]; exact ne_of_gt hfi) hother
    have he'' := open_chord_reverse he'
    have hf'' := open_chord_reverse hf'
    rw [← h] at hf''
    exact open_chords_common_start hn he'' hf''

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem CircleConfiguration.orient_inside {n : ℕ} (C : CircleConfiguration n)
    {i j k : Fin n} (hik : i < k) (hkj : k < j) :
    Zarankiewicz.orient2 (C.point i) (C.point j) (C.point k) < 0 := by
  rw [Zarankiewicz.orient2_swap_ends]
  exact neg_neg_of_pos (C.cyclic_order i k j hik hkj)

theorem CircleConfiguration.orient_outside {n : ℕ} (C : CircleConfiguration n)
    {i j k : Fin n} (hij : i < j) (hk : k < i ∨ j < k) :
    0 < Zarankiewicz.orient2 (C.point i) (C.point j) (C.point k) := by
  rcases hk with hk | hk
  · rw [Zarankiewicz.orient2_cycle (C.point k) (C.point i) (C.point j)]
    exact C.cyclic_order k i j hk hij
  · exact C.cyclic_order i j k hij hk

theorem CircleConfiguration.alternating_cross {n : ℕ} (C : CircleConfiguration n)
    {i k j l : Fin n} (hik : i < k) (hkj : k < j) (hjl : j < l) :
    Zarankiewicz.SegmentsCrossProperly (C.point i) (C.point j) (C.point k) (C.point l) := by
  have hsign := Zarankiewicz.segmentCrossingSign_of_positive_sides
    (C.point i) (C.point j) (C.point k) (C.point l)
    (C.orient_inside hik hkj) (C.orient_outside (hik.trans hkj) (Or.inr hjl))
    (C.orient_outside (hkj.trans hjl) (Or.inl hik)) (C.orient_inside hkj hjl)
  by_contra h
  simp [Zarankiewicz.segmentCrossingSign, h] at hsign

theorem lineIntersectionPoint_eq_parameter (a b c d : Plane) :
    lineIntersectionPoint a b c d =
      Zarankiewicz.segmentPoint a b (Zarankiewicz.firstIntersectionParameter a b c d) := by
  have hnum : det2 (c - a) (d - c) = Zarankiewicz.det2 (d - c) (a - c) := by
    dsimp [det2, Zarankiewicz.det2]
    ring
  unfold lineIntersectionPoint
  rw [hnum]
  change a + Zarankiewicz.firstIntersectionParameter a b c d • (b - a) = _
  ext <;> simp [Zarankiewicz.segmentPoint] <;> ring

theorem open_chords_intersection_singleton (a b c d : Plane)
    (h : Zarankiewicz.SegmentsCrossProperly a b c d) :
    Zarankiewicz.openSegmentTrace a b ∩ Zarankiewicz.openSegmentTrace c d =
      {lineIntersectionPoint a b c d} := by
  have ht := (Zarankiewicz.segmentsCrossProperly_iff_parameters a b c d h.1).mp h
  have hp : lineIntersectionPoint a b c d ∈
      Zarankiewicz.openSegmentTrace a b ∩ Zarankiewicz.openSegmentTrace c d := by
    rw [lineIntersectionPoint_eq_parameter]
    exact ⟨⟨_, ht.1, rfl⟩, ⟨_, ht.2, (Zarankiewicz.intersection_parameters_eq a b c d h.1).symm⟩⟩
  ext x
  constructor
  · intro hx
    exact (Zarankiewicz.openSegment_intersection_subsingleton a b c d h.1 hx hp)
  · rintro rfl
    exact hp

theorem circle_chord_intersection {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) :
    chordInterior C.point e ∩ chordInterior C.point f =
      if (e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
         (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2) then
        {lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
          (C.point f.val.1) (C.point f.val.2)}
      else ∅ := by
  by_cases halt : (e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
      (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2)
  · rw [ite_eq_left halt]
    apply open_chords_intersection_singleton
    rcases halt with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
    · exact C.alternating_cross h₁ h₂ h₃
    · exact (Zarankiewicz.segmentsCrossProperly_swap _ _ _ _).mp
        (C.alternating_cross h₁ h₂ h₃)
  · rw [ite_eq_right halt]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨h02, h03, h12, h13⟩ := circle_chord_endpoints_distinct C.point C.injective
      C.on_circle e f hef x hx.1 hx.2
    have hei := e.property
    have hfi := f.property
    have htrans := Zarankiewicz.round_circle_chords_transverse 0
      (C.point e.val.1) (C.point e.val.2) (C.point f.val.1) (C.point f.val.2) 1
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle e.val.1)
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle e.val.2)
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle f.val.1)
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle f.val.2)
      (C.injective.ne (ne_of_lt hei)) (C.injective.ne (ne_of_lt hfi))
      (C.injective.ne h02) (C.injective.ne h03) (C.injective.ne h12) (C.injective.ne h13)
    obtain ⟨t, ht, he⟩ := hx.1
    obtain ⟨u, hu, hf⟩ := hx.2
    have heq := he.trans hf.symm
    have hcross : Zarankiewicz.SegmentsCrossProperly (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2) :=
      ⟨(htrans t ⟨ht.1.le, ht.2.le⟩ u ⟨hu.1.le, hu.2.le⟩ heq).1, t, ht, u, hu, heq⟩
    apply Zarankiewicz.not_segmentsCrossProperly_of_same_side _ _ _ _ _ hcross
    by_cases hinside : e.val.1 < f.val.1 ∧ f.val.1 < e.val.2
    · exact Or.inr ⟨C.orient_inside hinside.1 hinside.2,
        C.orient_inside (by omega) (by omega)⟩
    · exact Or.inl ⟨C.orient_outside hei (by omega), C.orient_outside hei (by omega)⟩

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

@[simp] theorem inversion_zero : inversion 0 = 0 := by
  simp [inversion, squaredLength]

theorem inversion_ne_zero {x : Plane} (hx : x ≠ 0) : inversion x ≠ 0 := by
  intro h
  exact hx ((inversion_involutive x).symm.trans ((congrArg inversion h).trans inversion_zero))

theorem continuous_squaredLength : Continuous squaredLength := by
  unfold squaredLength
  fun_prop

theorem continuousAt_inversion {x : Plane} (hx : x ≠ 0) : ContinuousAt inversion x := by
  have hq := ne_of_gt (squaredLength_pos hx)
  exact (continuous_fst.continuousAt.div continuous_squaredLength.continuousAt hq).prodMk
    (continuous_snd.continuousAt.div continuous_squaredLength.continuousAt hq)

def inversionChart : OpenPartialHomeomorph Plane Plane where
  toFun := inversion
  invFun := inversion
  source := {x | x ≠ 0}
  target := {x | x ≠ 0}
  map_source' := fun _ hx => inversion_ne_zero hx
  map_target' := fun _ hx => inversion_ne_zero hx
  left_inv' := fun x _ => inversion_involutive x
  right_inv' := fun x _ => inversion_involutive x
  continuousOn_toFun := fun _ hx => (continuousAt_inversion hx).continuousWithinAt
  continuousOn_invFun := fun _ hx => (continuousAt_inversion hx).continuousWithinAt
  open_source := isClosed_singleton.isOpen_compl
  open_target := isClosed_singleton.isOpen_compl

theorem inversion_chart_image (c : OpenPartialHomeomorph Plane Plane) (A L : Set Plane)
    (h : c '' (c.source ∩ A) = c.target ∩ L) :
    (inversionChart.trans c) '' ((inversionChart.trans c).source ∩ inversion '' A) =
      (inversionChart.trans c).target ∩ L := by
  let e := inversionChart.trans c
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    have hs : z ≠ 0 ∧ inversion z ∈ c.source := hz.1
    obtain ⟨a, ha, rfl⟩ := hz.2
    have hi : inversion (inversion a) ∈ A := (inversion_involutive a).symm ▸ ha
    exact ⟨e.map_source hz.1,
      (Zarankiewicz.chart_image_mem_iff c A L h _ hs.2).mp hi⟩
  · rintro y ⟨hy, hL⟩
    have hz := e.map_target hy
    have hs : e.symm y ≠ 0 ∧ inversion (e.symm y) ∈ c.source := hz
    have he : c (inversion (e.symm y)) = y := e.right_inv hy
    have ha : inversion (e.symm y) ∈ A :=
      (Zarankiewicz.chart_image_mem_iff c A L h _ hs.2).mpr (he.symm ▸ hL)
    exact ⟨e.symm y, ⟨hz, ⟨inversion (e.symm y), ha, inversion_involutive _⟩⟩,
      e.right_inv hy⟩

theorem ProperCrossing.inverted {A B : Set Plane} {x : Plane}
    (h : ProperCrossing A B x) (hx : x ≠ 0) :
    ProperCrossing (inversion '' A) (inversion '' B) (inversion x) := by
  obtain ⟨c, hs, he, hA, hB⟩ := h.chart_exists
  refine ⟨inversionChart.trans c, ⟨inversion_ne_zero hx, ?_⟩, ?_,
    inversion_chart_image c A _ hA, inversion_chart_image c B _ hB⟩
  · change inversion (inversion x) ∈ c.source
    rwa [inversion_involutive]
  · change c (inversion (inversion x)) = (0, 0)
    rwa [inversion_involutive]

theorem squaredLength_inversion {x : Plane} (hx : x ≠ 0) :
    squaredLength (inversion x) = (squaredLength x)⁻¹ := by
  have hq := ne_of_gt (squaredLength_pos hx)
  change (x.1 / squaredLength x)^2 + (x.2 / squaredLength x)^2 = _
  rw [div_pow, div_pow, ← add_div]
  change squaredLength x / squaredLength x ^ 2 = _
  field_simp

theorem chord_ne_zero {a b : Plane} (ha : squaredLength a = 1)
    (hb : squaredLength b = 1) (hab : a + b ≠ 0) (t : ℝ) :
    segmentPoint a b t ≠ 0 := by
  intro h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  change (1-t)*a.1+t*b.1=0 at h0
  change (1-t)*a.2+t*b.2=0 at h1
  have ht : t = 1/2 := by
    have he : (1-t)^2 * squaredLength a = t^2 * squaredLength b := by
      unfold squaredLength
      linear_combination ((1-t)*a.1-t*b.1)*h0 + ((1-t)*a.2-t*b.2)*h1
    rw [ha, hb] at he
    nlinarith
  apply hab
  ext <;> dsimp <;> rw [ht] at h0 h1 <;> linarith

theorem CircleConfiguration.chord_ne_zero {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) (t : ℝ) :
    segmentPoint (C.point e.val.1) (C.point e.val.2) t ≠ 0 :=
  Paper170.chord_ne_zero (C.on_circle _) (C.on_circle _)
    (C.no_antipodal _ _ (ne_of_lt e.property)) t

theorem CircleConfiguration.chord_inside {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) {x : Plane} (hx : x ∈ chordInterior C.point e) :
    squaredLength x < 1 := by
  obtain ⟨t, ht, rfl⟩ := hx
  simpa only [squaredLength, Zarankiewicz.squaredLength, sub_zero, one_pow, segmentPoint_eq] using
    Zarankiewicz.round_chord_in_open_disk 0 (C.point e.val.1) (C.point e.val.2) 1
      (by simpa only [squaredLength, Zarankiewicz.squaredLength, sub_zero, one_pow] using C.on_circle e.val.1)
      (by simpa only [squaredLength, Zarankiewicz.squaredLength, sub_zero, one_pow] using C.on_circle e.val.2)
      (C.injective.ne (ne_of_lt e.property)) t ht

theorem CircleConfiguration.chord_mem_ne_zero {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) {x : Plane} (hx : x ∈ chordInterior C.point e) : x ≠ 0 := by
  obtain ⟨t, _, rfl⟩ := hx
  exact C.chord_ne_zero e t

theorem CircleConfiguration.inverted_chord_outside {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) {x : Plane} (hx : x ∈ inversion '' chordInterior C.point e) :
    1 < squaredLength x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [squaredLength_inversion (C.chord_mem_ne_zero e hy)]
  exact (one_lt_inv₀ (squaredLength_pos (C.chord_mem_ne_zero e hy))).mpr (C.chord_inside e hy)

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem segmentPoint_injective {a b : Plane} (hab : a ≠ b) :
    Function.Injective (segmentPoint a b) := by
  intro s t h
  apply AffineMap.lineMap_injective ℝ hab
  simpa only [AffineMap.lineMap_apply_module, segmentPoint] using h

theorem continuous_segmentPoint (a b : Plane) : Continuous (segmentPoint a b) := by
  unfold segmentPoint
  fun_prop

theorem continuous_twoPageRoute {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    Continuous (twoPageRoute C e) := by
  have hseg : Continuous (fun t : unitInterval => segmentPoint (C.point e.val.1) (C.point e.val.2) t.val) :=
    (continuous_segmentPoint _ _).comp continuous_subtype_val
  change Continuous (fun t => twoPageRoute C e t)
  cases hc : residueColor n (e.val.1.val + e.val.2.val)
  ·
    simp only [twoPageRoute, hc, Bool.false_eq_true, ↓reduceIte]
    exact continuous_iff_continuousAt.mpr (fun t =>
      (continuousAt_inversion (C.chord_ne_zero e t.val)).comp
        (f := fun u : unitInterval => segmentPoint (C.point e.val.1) (C.point e.val.2) u.val)
        hseg.continuousAt)
  · simpa only [twoPageRoute, hc, ↓reduceIte] using hseg

def twoPagePath {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    Path (C.point e.val.1) (C.point e.val.2) where
  toFun := twoPageRoute C e
  continuous_toFun := continuous_twoPageRoute C e
  source' := by
    simp [twoPageRoute, segmentPoint, inversion_fixes_circle _ (C.on_circle _)]
  target' := by
    simp [twoPageRoute, segmentPoint, inversion_fixes_circle _ (C.on_circle _)]

theorem twoPageRoute_injective {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    Function.Injective (twoPageRoute C e) := by
  have hseg := (segmentPoint_injective (C.injective.ne (ne_of_lt e.property))).comp
    (show Function.Injective (fun t : unitInterval => t.val) from Subtype.val_injective)
  cases hc : residueColor n (e.val.1.val + e.val.2.val)
  · intro s t h
    apply hseg
    change segmentPoint (C.point e.val.1) (C.point e.val.2) s.val =
      segmentPoint (C.point e.val.1) (C.point e.val.2) t.val
    exact inversion_involutive.injective (by simpa only [twoPageRoute, hc, Bool.false_eq_true, ↓reduceIte] using h)
  · intro s t h
    apply hseg
    change segmentPoint (C.point e.val.1) (C.point e.val.2) s.val =
      segmentPoint (C.point e.val.1) (C.point e.val.2) t.val
    simpa only [twoPageRoute, hc, ↓reduceIte] using h

theorem twoPageRoute_avoids_vertices {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) (t : unitInterval) (ht : t ∈ Ioo (0 : unitInterval) 1) (v : Fin n) :
    twoPageRoute C e t ≠ C.point v := by
  have hmem : twoPageRoute C e t ∈ twoPageRoute C e '' Ioo (0 : unitInterval) 1 := ⟨t, ht, rfl⟩
  rw [twoPageRoute_image] at hmem
  intro he
  rw [he] at hmem
  cases hc : residueColor n (e.val.1.val + e.val.2.val)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
    have h := C.inverted_chord_outside e hmem
    rw [C.on_circle] at h
    exact (lt_irrefl _ h)
  · simp only [hc, ↓reduceIte] at hmem
    have h := C.chord_inside e hmem
    rw [C.on_circle] at h
    exact (lt_irrefl _ h)

def twoPageContinuous {n : ℕ} (C : CircleConfiguration n) :
    ContinuousDrawing (completeGraph n) where
  vertex := C.point
  vertex_injective := C.injective
  edge := twoPagePath C
  edge_injective := twoPageRoute_injective C
  interior_avoids_vertices := twoPageRoute_avoids_vertices C

theorem twoPageContinuous_edgeInterior {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    edgeInterior (twoPageContinuous C) e =
      if residueColor n (e.val.1.val + e.val.2.val) then chordInterior C.point e
      else inversion '' chordInterior C.point e :=
  twoPageRoute_image C e

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem CircleConfiguration.chord_proper {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) {x : Plane}
    (hx : x ∈ chordInterior C.point e) (hy : x ∈ chordInterior C.point f) :
    ProperCrossing (chordInterior C.point e) (chordInterior C.point f) x := by
  have hp : x ∈ chordInterior C.point e ∩ chordInterior C.point f := ⟨hx, hy⟩
  rw [circle_chord_intersection C e f hef] at hp
  split_ifs at hp with halt
  · have hcross : Zarankiewicz.SegmentsCrossProperly (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2) := by
      rcases halt with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
      · exact C.alternating_cross h₁ h₂ h₃
      · exact (Zarankiewicz.segmentsCrossProperly_swap _ _ _ _).mp (C.alternating_cross h₁ h₂ h₃)
    exact ⟨Zarankiewicz.properCrossing_openSegments _ _ _ _ x hcross.1 hx hy⟩
  · exact hp.elim

theorem CircleConfiguration.chord_inter_finite {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) :
    (chordInterior C.point e ∩ chordInterior C.point f).Finite := by
  rw [circle_chord_intersection C e f hef]
  split_ifs <;> simp

theorem CircleConfiguration.chord_inverted_disjoint {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) :
    Disjoint (chordInterior C.point e) (inversion '' chordInterior C.point f) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact lt_asymm (C.chord_inside e hx) (C.inverted_chord_outside f hy)

theorem twoPageContinuous_same_color {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) {x : Plane}
    (hx : x ∈ edgeInterior (twoPageContinuous C) e)
    (hy : x ∈ edgeInterior (twoPageContinuous C) f) :
    residueColor n (e.val.1.val + e.val.2.val) =
      residueColor n (f.val.1.val + f.val.2.val) := by
  rw [twoPageContinuous_edgeInterior] at hx hy
  cases he : residueColor n (e.val.1.val + e.val.2.val) <;>
    cases hf : residueColor n (f.val.1.val + f.val.2.val) <;>
    simp only [he, hf, Bool.false_eq_true, ↓reduceIte] at hx hy ⊢
  · exact (lt_asymm (C.inverted_chord_outside e hx) (C.chord_inside f hy)).elim
  · exact (lt_asymm (C.chord_inside e hx) (C.inverted_chord_outside f hy)).elim

theorem twoPageContinuous_inter_finite {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) :
    (edgeInterior (twoPageContinuous C) e ∩ edgeInterior (twoPageContinuous C) f).Finite := by
  rw [twoPageContinuous_edgeInterior, twoPageContinuous_edgeInterior]
  cases he : residueColor n (e.val.1.val + e.val.2.val) <;>
    cases hf : residueColor n (f.val.1.val + f.val.2.val) <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [← Set.image_inter inversion_involutive.injective]
    exact (C.chord_inter_finite e f hef).image _
  · rw [(C.chord_inverted_disjoint f e).symm.inter_eq]
    exact Set.finite_empty
  · rw [(C.chord_inverted_disjoint e f).inter_eq]
    exact Set.finite_empty
  · exact C.chord_inter_finite e f hef

theorem twoPageContinuous_crossings_finite {n : ℕ} (C : CircleConfiguration n) :
    (crossingPoints (twoPageContinuous C)).Finite := by
  have heq : crossingPoints (twoPageContinuous C) =
      ⋃ e : CompleteEdge n, ⋃ f : CompleteEdge n,
        if e = f then ∅ else edgeInterior (twoPageContinuous C) e ∩
          edgeInterior (twoPageContinuous C) f := by
    ext x
    simp only [crossingPoints, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨e, f, hef, hx, hy⟩
      exact ⟨e, f, by rw [ite_eq_right hef]; exact ⟨hx, hy⟩⟩
    · rintro ⟨e, f, hx⟩
      split_ifs at hx with hef
      · exact hx.elim
      · exact ⟨e, f, hef, hx.1, hx.2⟩
  rw [heq]
  apply Set.finite_iUnion
  intro e
  apply Set.finite_iUnion
  intro f
  split_ifs with hef
  · exact Set.finite_empty
  · exact twoPageContinuous_inter_finite C e f hef

theorem twoPageContinuous_proper {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) (x : Plane)
    (hx : x ∈ edgeInterior (twoPageContinuous C) e)
    (hy : x ∈ edgeInterior (twoPageContinuous C) f) :
    ProperCrossing (edgeInterior (twoPageContinuous C) e)
      (edgeInterior (twoPageContinuous C) f) x := by
  have hc := twoPageContinuous_same_color C e f hx hy
  simp only [twoPageContinuous_edgeInterior] at hx hy ⊢
  rw [hc] at hx ⊢
  cases hf : residueColor n (f.val.1.val + f.val.2.val) <;>
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at hx hy ⊢
  · obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, he⟩ := hy
    have hba : b = a := inversion_involutive.injective he
    subst b
    exact (C.chord_proper e f hef ha hb).inverted (C.chord_mem_ne_zero e ha)
  · exact C.chord_proper e f hef hx hy

theorem twoPageContinuous_no_triples {n : ℕ} (C : CircleConfiguration n)
    (e f g : CompleteEdge n) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    edgeInterior (twoPageContinuous C) e ∩ edgeInterior (twoPageContinuous C) f ∩
      edgeInterior (twoPageContinuous C) g = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hcf := twoPageContinuous_same_color C e f hx.1.1 hx.1.2
  have hcg := twoPageContinuous_same_color C e g hx.1.1 hx.2
  simp only [twoPageContinuous_edgeInterior, ← hcf, ← hcg] at hx
  cases he : residueColor n (e.val.1.val + e.val.2.val) <;>
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hx
  · have hm : x ∈ inversion ''
        (chordInterior C.point e ∩ chordInterior C.point f ∩ chordInterior C.point g) := by
      rw [Set.image_inter inversion_involutive.injective,
        Set.image_inter inversion_involutive.injective]
      exact hx
    rw [C.no_triple_chords e f g hef heg hfg, Set.image_empty] at hm
    exact hm.elim
  · rw [C.no_triple_chords e f g hef heg hfg] at hx
    exact hx.elim

def twoPageAdmissible {n : ℕ} (C : CircleConfiguration n) :
    AdmissibleDrawing (completeGraph n) where
  toContinuousDrawing := twoPageContinuous C
  crossings_finite := twoPageContinuous_crossings_finite C
  crossings_proper := twoPageContinuous_proper C
  no_triples := twoPageContinuous_no_triples C

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleOffset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def circleOffset (u : Plane) (δ : ℝ) : Plane := Real.sqrt (1-δ^2) • u+δ • rotateQuarter u

@[simp] theorem circleOffset_zero (u : Plane) : circleOffset u 0=u := by
  simp [circleOffset]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CirclePlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic circular placement, prescribed arcs, restrictions, and existence of drawings. -/

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

variable {V E : Type} {m : ℕ}

def completeEdgeOf (G : Graph V E) (ι : V ↪ Fin m) (e : E) : CompleteEdge m :=
  if h : ι (G.src e) < ι (G.dst e) then ⟨(ι (G.src e), ι (G.dst e)), h⟩
  else ⟨(ι (G.dst e), ι (G.src e)), by change ι (G.dst e) < ι (G.src e); have := ι.injective.ne (G.loopless e); omega⟩

theorem completeEdgeOf_endpoints (G : Graph V E) (ι : V ↪ Fin m) (e : E) :
    ((completeEdgeOf G ι e).val.1 = ι (G.src e) ∧
      (completeEdgeOf G ι e).val.2 = ι (G.dst e)) ∨
    ((completeEdgeOf G ι e).val.1 = ι (G.dst e) ∧
      (completeEdgeOf G ι e).val.2 = ι (G.src e)) := by
  unfold completeEdgeOf
  split_ifs <;> simp

theorem completeEdgeOf_injective (G : Graph V E) (ι : V ↪ Fin m) :
    Function.Injective (completeEdgeOf G ι) := by
  intro e f h
  have h₁ := congrArg (fun a : CompleteEdge m => a.val.1) h
  have h₂ := congrArg (fun a : CompleteEdge m => a.val.2) h
  rcases completeEdgeOf_endpoints G ι e with he | he <;>
    rcases completeEdgeOf_endpoints G ι f with hf | hf
  · exact G.simple e f (Or.inl ⟨ι.injective (he.1.symm.trans (h₁.trans hf.1)),
      ι.injective (he.2.symm.trans (h₂.trans hf.2))⟩)
  · exact G.simple e f (Or.inr ⟨ι.injective (he.1.symm.trans (h₁.trans hf.1)),
      ι.injective (he.2.symm.trans (h₂.trans hf.2))⟩)
  · exact G.simple e f (Or.inr ⟨ι.injective (he.2.symm.trans (h₂.trans hf.2)),
      ι.injective (he.1.symm.trans (h₁.trans hf.1))⟩)
  · exact G.simple e f (Or.inl ⟨ι.injective (he.2.symm.trans (h₂.trans hf.2)),
      ι.injective (he.1.symm.trans (h₁.trans hf.1))⟩)

theorem unitInterval_symm_mem_open {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1) :
    unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 := by
  have h0 : (0 : ℝ) < t.val := ht.1
  have h1 : t.val < (1 : ℝ) := ht.2
  change 0 < 1 - t.val ∧ 1 - t.val < 1
  constructor <;> linarith

theorem path_symm_open_image {a b : Plane} (γ : Path a b) :
    γ.symm '' Ioo (0 : unitInterval) 1 = γ '' Ioo (0 : unitInterval) 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨unitInterval.symm t, unitInterval_symm_mem_open ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨unitInterval.symm t, unitInterval_symm_mem_open ht, ?_⟩
    change γ (unitInterval.symm (unitInterval.symm t)) = γ t
    rw [unitInterval.symm_involutive t]

def restrictedCompletePath (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) :
    Path (D.vertex (ι (G.src e))) (D.vertex (ι (G.dst e))) where
  toFun t := if h : ι (G.src e) < ι (G.dst e) then
    D.edge ⟨(ι (G.src e), ι (G.dst e)), h⟩ t
  else D.edge ⟨(ι (G.dst e), ι (G.src e)),
    by change ι (G.dst e) < ι (G.src e); have := ι.injective.ne (G.loopless e); omega⟩
      (unitInterval.symm t)
  continuous_toFun := by
    split_ifs with h
    · exact (D.edge _).continuous
    · exact (D.edge _).continuous.comp unitInterval.continuous_symm
  source' := by
    split_ifs
    · exact (D.edge _).source
    · rw [unitInterval.symm_zero]
      exact (D.edge _).target
  target' := by
    split_ifs
    · exact (D.edge _).target
    · rw [unitInterval.symm_one]
      exact (D.edge _).source

theorem restrictedCompletePath_injective (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) :
    Function.Injective (restrictedCompletePath G ι D e) := by
  intro s t he
  by_cases h : ι (G.src e) < ι (G.dst e)
  · let f : CompleteEdge m := ⟨(ι (G.src e), ι (G.dst e)), h⟩
    have hpath : (restrictedCompletePath G ι D e : unitInterval → Plane) = D.edge f := by
      funext t
      exact dite_eq_left h
    exact D.edge_injective f ((congrFun hpath s).symm.trans (he.trans (congrFun hpath t)))
  · let f : CompleteEdge m := ⟨(ι (G.dst e), ι (G.src e)),
      by change ι (G.dst e) < ι (G.src e); have := ι.injective.ne (G.loopless e); omega⟩
    have hpath : (restrictedCompletePath G ι D e : unitInterval → Plane) = (D.edge f).symm := by
      funext t
      exact dite_eq_right h
    have he' := (congrFun hpath s).symm.trans (he.trans (congrFun hpath t))
    exact unitInterval.symm_involutive.injective (D.edge_injective _ he')

theorem restrictedCompletePath_interior (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) :
    restrictedCompletePath G ι D e '' Ioo (0 : unitInterval) 1 =
      edgeInterior D.toContinuousDrawing (completeEdgeOf G ι e) := by
  by_cases h : ι (G.src e) < ι (G.dst e)
  · let f : CompleteEdge m := ⟨(ι (G.src e), ι (G.dst e)), h⟩
    have hedge : completeEdgeOf G ι e = f := dite_eq_left h
    have hpath : (restrictedCompletePath G ι D e : unitInterval → Plane) = D.edge f := by
      funext t
      exact dite_eq_left h
    rw [hpath, hedge]
    rfl
  · let f : CompleteEdge m := ⟨(ι (G.dst e), ι (G.src e)),
      by change ι (G.dst e) < ι (G.src e); have := ι.injective.ne (G.loopless e); omega⟩
    have hedge : completeEdgeOf G ι e = f := dite_eq_right h
    have hpath : (restrictedCompletePath G ι D e : unitInterval → Plane) = (D.edge f).symm := by
      funext t
      exact dite_eq_right h
    rw [hpath, hedge]
    exact path_symm_open_image (D.edge f)

theorem restrictedCompletePath_avoids (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) (t : unitInterval)
    (ht : t ∈ Ioo (0 : unitInterval) 1) (v : V) :
    restrictedCompletePath G ι D e t ≠ D.vertex (ι v) := by
  have hm : restrictedCompletePath G ι D e t ∈
      restrictedCompletePath G ι D e '' Ioo (0 : unitInterval) 1 := ⟨t, ht, rfl⟩
  rw [restrictedCompletePath_interior] at hm
  obtain ⟨u, hu, he⟩ := hm
  rw [← he]
  exact D.interior_avoids_vertices _ u hu _

def restrictedCompleteContinuous (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) : ContinuousDrawing G where
  vertex := D.vertex ∘ ι
  vertex_injective := D.vertex_injective.comp ι.injective
  edge := restrictedCompletePath G ι D
  edge_injective := restrictedCompletePath_injective G ι D
  interior_avoids_vertices := restrictedCompletePath_avoids G ι D

theorem restrictedComplete_edgeInterior (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) :
    edgeInterior (restrictedCompleteContinuous G ι D) e =
      edgeInterior D.toContinuousDrawing (completeEdgeOf G ι e) :=
  restrictedCompletePath_interior G ι D e

theorem restrictedComplete_crossings_subset (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) :
    crossingPoints (restrictedCompleteContinuous G ι D) ⊆ crossingPoints D.toContinuousDrawing := by
  rintro x ⟨e, f, hef, hx, hy⟩
  rw [restrictedComplete_edgeInterior] at hx hy
  exact ⟨_, _, (completeEdgeOf_injective G ι).ne hef, hx, hy⟩

def restrictedCompleteAdmissible (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) : AdmissibleDrawing G where
  toContinuousDrawing := restrictedCompleteContinuous G ι D
  crossings_finite := D.crossings_finite.subset (restrictedComplete_crossings_subset G ι D)
  crossings_proper := by
    intro e f hef x hx hy
    simp only [restrictedComplete_edgeInterior] at hx hy ⊢
    exact D.crossings_proper _ _ ((completeEdgeOf_injective G ι).ne hef) x hx hy
  no_triples := by
    intro e f g hef heg hfg
    simp only [restrictedComplete_edgeInterior]
    exact D.no_triples _ _ _ ((completeEdgeOf_injective G ι).ne hef)
      ((completeEdgeOf_injective G ι).ne heg) ((completeEdgeOf_injective G ι).ne hfg)

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

def circleConcurrency {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  (c + d) * e * f - c * d * (e + f) - (a + b) * (e * f - c * d) +
    a * b * (e + f - c - d)

def circleLine (a b : ℝ) (z : Plane) : ℝ :=
  (1 - a * b) * z.1 + (a + b) * z.2 - (1 + a * b)

def circleConcurrencyPolynomial {n : ℕ} (v : Fin 6 → Fin n) : MvPolynomial (Fin n) ℝ :=
  circleConcurrency (MvPolynomial.X (v 0)) (MvPolynomial.X (v 1))
    (MvPolynomial.X (v 2)) (MvPolynomial.X (v 3))
    (MvPolynomial.X (v 4)) (MvPolynomial.X (v 5))

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Residues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residue fibers, same-page residues, and parity counts. -/

section

noncomputable section
namespace Paper170

@[simp] theorem residueColor_mod (n r : ℕ) : residueColor n (r % n) = residueColor n r := by
  simp [residueColor]

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclic gap enumeration and the exact Harary–Hill crossing-tuple count. -/

section

noncomputable section
open scoped BigOperators
namespace Paper170

def naturalCrossingTuples (n : ℕ) : Finset (Fin 4 → ℕ) :=
  (crossingTuples n).image (fun v i => (v i).val)

abbrev CyclicRecord := Σ _ : ℕ, ℕ × ℕ × ℕ

def cyclicRecords (n : ℕ) : Finset CyclicRecord :=
  (Finset.Icc 2 (n - 2)).sigma (fun k => sameColorGapTuples n k)

def cyclicToOrdered (n : ℕ) (p : CyclicRecord) : Fin 4 × (Fin 4 → ℕ) :=
  let k := p.1
  let a := p.2.1
  let b := a + p.2.2.1
  let c := b + p.2.2.2
  let d := a + k + p.2.2.2
  if d < n then (0, ![a, b, c, d])
  else if c < n then (1, ![d - n, a, b, c])
  else if b < n then (2, ![c - n, d - n, a, b])
  else (3, ![b - n, c - n, d - n, a])

def orderedToCyclic (n : ℕ) (q : Fin 4 × (Fin 4 → ℕ)) : CyclicRecord :=
  let v := q.2
  match q.1.val with
  | 0 => ⟨(v 1 - v 0) + (v 3 - v 2), v 0, v 1 - v 0, v 2 - v 1⟩
  | 1 => ⟨(v 2 - v 1) + (v 0 + n - v 3), v 1, v 2 - v 1, v 3 - v 2⟩
  | 2 => ⟨(v 3 - v 2) + (v 1 - v 0), v 2, v 3 - v 2, v 0 + n - v 3⟩
  | _ => ⟨(v 0 + n - v 3) + (v 2 - v 1), v 3, v 0 + n - v 3, v 1 - v 0⟩

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

def startingLabels (n k b : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a =>
    residueColor n (2 * a + b) = residueColor n (2 * a + b + k))

end Paper170

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

/-! Linear properties of actual oriented simple cycles. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E : Type} {G : Graph V E}
namespace SimpleCycle

def next (C : SimpleCycle G) (i : Fin C.length) : Fin C.length :=
  ⟨(i.val+1)%C.length, Nat.mod_lt _ (by have := C.three_le; omega)⟩

end SimpleCycle
end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

omit [Fintype V] in
lemma incoming_has_outgoing (z : E → ℝ) (hz : ∀ v, boundary G z v = 0)
    (v : V) (e : E)
    (he : (G.dst e = v ∧ 0 < z e) ∨ (G.src e = v ∧ z e < 0)) :
    ∃ f, ((G.src f = v ∧ 0 < z f) ∨ (G.dst f = v ∧ z f < 0)) := by
  by_contra hn
  have hn' (f : E) : ¬ ((G.src f = v ∧ 0 < z f) ∨ (G.dst f = v ∧ z f < 0)) := fun hf => hn ⟨f, hf⟩
  let term := fun f : E => z f * ((if G.dst f = v then 1 else 0) -
    (if G.src f = v then 1 else 0))
  have hnonneg (f : E) : 0 ≤ term f := by
    by_cases hdst : G.dst f = v
    · by_cases hsrc : G.src f = v
      · exact (G.loopless f (hsrc.trans hdst.symm)).elim
      · have hf : 0 ≤ z f := by
          by_contra! h
          exact hn' f (Or.inr ⟨hdst, h⟩)
        simpa [term, hdst, hsrc] using hf
    · by_cases hsrc : G.src f = v
      · have hf : z f ≤ 0 := by
          by_contra! h
          exact hn' f (Or.inl ⟨hsrc, h⟩)
        simpa [term, hdst, hsrc] using neg_nonneg.mpr hf
      · simp [term, hdst, hsrc]
  have hpos : 0 < term e := by
    rcases he with ⟨hdst, he⟩ | ⟨hsrc, he⟩
    · have hsrc : G.src e ≠ v := fun h => G.loopless e (h.trans hdst.symm)
      simpa [term, hdst, hsrc] using he
    · have hdst : G.dst e ≠ v := fun h => G.loopless e (hsrc.trans h.symm)
      simpa [term, hdst, hsrc] using neg_pos.mpr he
  have ht : 0 < ∑ f, term f := Finset.sum_pos' (fun f _ => hnonneg f)
    ⟨e, Finset.mem_univ e, hpos⟩
  have hzero : (∑ f, term f) = 0 := hz v
  linarith

abbrev FlowVertex (z : E → ℝ) := {v : V // ∃ e, ((G.src e = v ∧ 0 < z e) ∨ (G.dst e = v ∧ z e < 0))}

omit [Fintype V] in
lemma flow_successor_exists (z : E → ℝ) (hz : ∀ v, boundary G z v = 0)
    (v : FlowVertex G z) : ∃ w : FlowVertex G z, ∃ e, ((G.src e = v.val ∧ G.dst e = w.val ∧ 0 < z e) ∨
    (G.dst e = v.val ∧ G.src e = w.val ∧ z e < 0)) := by
  obtain ⟨e, he⟩ := v.property
  rcases he with ⟨hsrc, he⟩ | ⟨hdst, he⟩
  · refine ⟨⟨G.dst e, incoming_has_outgoing G z hz (G.dst e) e (Or.inl ⟨rfl, he⟩)⟩,
      e, Or.inl ⟨hsrc, rfl, he⟩⟩
  · refine ⟨⟨G.src e, incoming_has_outgoing G z hz (G.src e) e (Or.inr ⟨rfl, he⟩)⟩,
      e, Or.inr ⟨hdst, rfl, he⟩⟩

def flowNext (z : E → ℝ) (hz : ∀ v, boundary G z v = 0) (v : FlowVertex G z) :
    FlowVertex G z := (flow_successor_exists G z hz v).choose

def flowEdge (z : E → ℝ) (hz : ∀ v, boundary G z v = 0) (v : FlowVertex G z) : E :=
  (flow_successor_exists G z hz v).choose_spec.choose

end Paper170

end
end

section

/-! Directed traversals of the fixed edges of an arbitrary finite simple graph. -/
noncomputable section
namespace Paper170Geometry
variable {V E : Type} {G : Paper170.Graph V E}

structure OrientedDart (G : Paper170.Graph V E) where
  edge : E
  forward : Bool

namespace OrientedDart

def fst (d : OrientedDart G) : V := if d.forward then G.src d.edge else G.dst d.edge

def snd (d : OrientedDart G) : V := if d.forward then G.dst d.edge else G.src d.edge

end OrientedDart

end Paper170Geometry

end
end

section

/-! Support reduction spans the real kernel of the graph boundary map by simple cycles. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E : Type} [Fintype E] (G : Graph V E)

def boundaryLinear : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun z := boundary G z
  map_add' z w := by
    funext v
    simp [boundary, add_mul, Finset.sum_add_distrib]
  map_smul' a z := by
    funext v
    simp [boundary, mul_assoc, Finset.mul_sum]

def chainSupport (z : E → ℝ) : Finset E := Finset.univ.filter fun e => z e≠0

end Paper170

end
end

section

/-! A frozen simple cycle gives a periodic sequence of actual oriented edge traversals. -/
noncomputable section
open scoped Classical
namespace Paper170.SimpleCycle
open Paper170Geometry
variable {V E : Type} {G : Graph V E}

def dart (C : SimpleCycle G) (i : Fin C.length) : OrientedDart G :=
  ⟨C.edge i,decide (G.src (C.edge i)=C.vertex i)⟩

def modIndex (C : SimpleCycle G) (i : ℕ) : Fin C.length :=
  ⟨i % C.length,Nat.mod_lt _ (by have := C.three_le; omega)⟩

def cyclicDart (C : SimpleCycle G) (i : ℕ) : OrientedDart G := C.dart (C.modIndex i)

end Paper170.SimpleCycle

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_LocalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local straightness and transversality of normalized drawings. -/

section

/-! Actual local line and adjacency properties used in the cycle-intersection proof. -/
noncomputable section
open Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

structure NoAdjacentCrossings (D : Paper170.AdmissibleDrawing graph) : Prop where
  eq_empty : ∀ e f : Edge, e≠f →
    (graph.src e=graph.src f ∨ graph.src e=graph.dst f ∨
      graph.dst e=graph.src f ∨ graph.dst e=graph.dst f) →
    Paper170.edgeInterior D.toContinuousDrawing e ∩
      Paper170.edgeInterior D.toContinuousDrawing f = ∅

structure LocallyStraightAt (D : Paper170.ContinuousDrawing graph) (e : Edge) (x : Plane) : Prop where
  exists_line : ∃a b : Plane, a≠b ∧ x∈openSegmentTrace a b ∧
    ∃U : Set Plane, IsOpen U ∧ x∈U ∧
      ∀z∈U, z∈Paper170.edgeInterior D e ↔ z∈openSegmentTrace a b

structure LocallyStraightCrossings (D : Paper170.AdmissibleDrawing graph) : Prop where
  at_crossing : ∀e f : Edge, e≠f → ∀x,
    x∈Paper170.edgeInterior D.toContinuousDrawing e →
    x∈Paper170.edgeInterior D.toContinuousDrawing f →
      LocallyStraightAt D.toContinuousDrawing e x ∧ LocallyStraightAt D.toContinuousDrawing f x

structure LocallyTransverseCrossings (D : Paper170.AdmissibleDrawing graph) : Prop where
  at_crossing : ∀e f : Edge, e≠f → ∀x,
    x∈Paper170.edgeInterior D.toContinuousDrawing e →
    x∈Paper170.edgeInterior D.toContinuousDrawing f →
      ∃a b c d : Plane, det2 (b-a) (d-c)≠0 ∧
        x∈openSegmentTrace a b ∧ x∈openSegmentTrace c d ∧
        ∃U : Set Plane, IsOpen U ∧ x∈U ∧
          (∀z∈U, z∈Paper170.edgeInterior D.toContinuousDrawing e ↔ z∈openSegmentTrace a b) ∧
          (∀z∈U, z∈Paper170.edgeInterior D.toContinuousDrawing f ↔ z∈openSegmentTrace c d)

end Paper170Geometry

end
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
def IncidentEdges (graph : Paper170.Graph Vertex Edge) (j : Vertex) :=
  {e : Edge // j=(graph.src e) ∨ j=(graph.dst e)}

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ReconnectedVertexAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem path_interior_avoids_vertices_of_range {V : Type*} (vertex : V → Plane) (a b : V)
    (γ : Path (vertex a) (vertex b)) (hinj : Function.Injective γ)
    (hrange : ∀ v, vertex v ∈ Set.range γ → v=a ∨ v=b)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (v : V) : γ t ≠ vertex v := by
  intro he
  rcases hrange v ⟨t,he⟩ with rfl | rfl
  · exact ht.1.ne (hinj (he.trans γ.source.symm)).symm
  · exact ht.2.ne (hinj (he.trans γ.target.symm))

end Zarankiewicz

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

/-! Fixed vertex half-order kernels on actual incident edge flags. -/
noncomputable section
open Zarankiewicz
open scoped Classical
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

abbrev IncidentFlag (graph : Paper170.Graph Vertex Edge) := (j : Vertex) × IncidentEdges graph j

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex deletion, its crossing-count identity, and small complete graphs. -/

section

/-! Source-faithful restriction of an actual complete-graph drawing by one vertex. -/
noncomputable section
namespace Paper170

structure VertexDeletion {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) (A : AdmissibleDrawing (completeGraph n)) : Prop where
  vertex_eq : ∀ i, A.vertex i = D.vertex (v.succAbove i)
  edge_eq : ∀ (e : CompleteEdge n) (f : CompleteEdge (n + 1)),
    f.val.1 = v.succAbove e.val.1 → f.val.2 = v.succAbove e.val.2 →
    ∀ t, A.edge e t = D.edge f t

end Paper170

end
end

section

noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170

def deletionEdge {n : ℕ} (v : Fin (n + 1)) (e : CompleteEdge n) : CompleteEdge (n + 1) :=
  ⟨(v.succAbove e.val.1, v.succAbove e.val.2), Fin.strictMono_succAbove v e.property⟩

lemma deletionEdge_injective {n : ℕ} (v : Fin (n + 1)) :
    Function.Injective (deletionEdge v) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.succAbove_right_injective (congrArg (fun a => a.val.1) h)
  · exact Fin.succAbove_right_injective (congrArg (fun a => a.val.2) h)

def deleteContinuousDrawing {n : ℕ} (D : ContinuousDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : ContinuousDrawing (completeGraph n) where
  vertex i := D.vertex (v.succAbove i)
  vertex_injective := D.vertex_injective.comp Fin.succAbove_right_injective
  edge e := D.edge (deletionEdge v e)
  edge_injective e := D.edge_injective (deletionEdge v e)
  interior_avoids_vertices e t ht i :=
    D.interior_avoids_vertices (deletionEdge v e) t ht (v.succAbove i)

lemma deletion_crossings_subset {n : ℕ} (D : ContinuousDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : crossingPoints (deleteContinuousDrawing D v) ⊆ crossingPoints D := by
  rintro x ⟨e, f, hef, he, hf⟩
  exact ⟨deletionEdge v e, deletionEdge v f,
    fun h => hef (deletionEdge_injective v h), he, hf⟩

def deleteDrawing {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : AdmissibleDrawing (completeGraph n) where
  toContinuousDrawing := deleteContinuousDrawing D.toContinuousDrawing v
  crossings_finite := D.crossings_finite.subset (deletion_crossings_subset _ v)
  crossings_proper e f hef x he hf := D.crossings_proper (deletionEdge v e) (deletionEdge v f)
    (fun h => hef (deletionEdge_injective v h)) x he hf
  no_triples e f g hef heg hfg := D.no_triples (deletionEdge v e) (deletionEdge v f)
    (deletionEdge v g) (fun h => hef (deletionEdge_injective v h))
    (fun h => heg (deletionEdge_injective v h)) (fun h => hfg (deletionEdge_injective v h))

end Paper170

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

abbrev BiPoly := PolynomialModule ℝ (PolynomialModule ℝ ℝ)

def flattenBi : BiPoly ≃ₗ[ℝ] (ℕ × ℕ →₀ ℝ) :=
  ((coeffLinearEquiv ℝ ℝ).trans
    (Finsupp.mapRange.linearEquiv (coeffLinearEquiv ℝ ℝ))).trans
    (Finsupp.curryLinearEquiv ℝ).symm

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Interpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bivariate interpolation degrees, spaces, pairings, and polynomial tests. -/

section

/-! Degree conventions and interpolation weights.
 -/

open scoped BigOperators
noncomputable section

namespace Paper170

theorem rectangle_membership (a b : ℕ) (P : Poly2) :
    P ∈ rectangle a b ↔ P.degreeOf 0 ≤ a ∧ P.degreeOf 1 ≤ b := by
  change P.degrees ≤ _ ↔ _
  rw [Multiset.le_iff_count]
  simp [← MvPolynomial.degreeOf_def, Fin.forall_fin_two, Multiset.count_replicate]

theorem box4_membership (d : ℕ) (P : Poly4) :
    P ∈ box4 d ↔ ∀ i, P.degreeOf i ≤ d := by
  change P.degrees ≤ _ ↔ _
  rw [Multiset.le_iff_count]
  simp [← MvPolynomial.degreeOf_def]

theorem symmetric_space_membership (s : ℕ) (P : Poly4) :
    P ∈ endpointSymmetricSpace s ↔
      (∀ i, P.degreeOf i ≤ s - 2) ∧ swapFirstPair P = P ∧ swapSecondPair P = P := by
  simp [endpointSymmetricSpace, box4_membership, sub_eq_zero, and_assoc]

end Paper170

end
end

section

/-! Coefficient spaces for the even-node interpolation argument. -/
noncomputable section
open scoped BigOperators
open Module
namespace Paper170

def exponentPair : (Fin 2 →₀ ℕ) ≃ ℕ × ℕ where
  toFun m := (m 0, m 1)
  invFun p := Finsupp.equivFunOnFinite.symm ![p.1, p.2]
  left_inv m := by
    ext i
    fin_cases i <;> simp
  right_inv p := by simp

@[simp] theorem exponentPair_symm_zero (a b : ℕ) : exponentPair.symm (a,b) 0 = a := rfl
@[simp] theorem exponentPair_symm_one (a b : ℕ) : exponentPair.symm (a,b) 1 = b := rfl

theorem rectangle_eq_restrictSupport (a b : ℕ) :
    rectangle a b = MvPolynomial.restrictSupport ℝ {m | m 0 ≤ a ∧ m 1 ≤ b} := by
  ext P
  rw [rectangle_membership, MvPolynomial.mem_restrictSupport_iff]
  simp only [MvPolynomial.degreeOf_le_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]
  exact ⟨fun h m hm => ⟨h.1 m hm, h.2 m hm⟩,
    fun h => ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩⟩

def rectangleExponentEquiv (a b : ℕ) :
    {m : Fin 2 →₀ ℕ // m 0 ≤ a ∧ m 1 ≤ b} ≃ Fin (a+1) × Fin (b+1) where
  toFun m := (⟨m.val 0, by omega⟩, ⟨m.val 1, by omega⟩)
  invFun p := ⟨exponentPair.symm (p.1.val,p.2.val), by simp; omega⟩
  left_inv m := by
    apply Subtype.ext
    exact exponentPair.symm_apply_apply m.val
  right_inv p := by rfl

def rectangleBasis (a b : ℕ) : Basis (Fin (a+1) × Fin (b+1)) ℝ (rectangle a b) :=
  ((MvPolynomial.basisRestrictSupport ℝ _).reindex (rectangleExponentEquiv a b)).map
    (LinearEquiv.ofEq _ _ (rectangle_eq_restrictSupport a b).symm)

/-- The coefficient-preserving bridge to the existing bivariate interpolation library. -/
def toBiPolynomial : Poly2 ≃ₗ[ℝ] Zarankiewicz.BiPoly :=
  ((MvPolynomial.basisMonomials (Fin 2) ℝ).repr.trans
    (Finsupp.domLCongr exponentPair)).trans Zarankiewicz.flattenBi.symm

end Paper170

end
end

section

/-! Polynomial cycle tests and the span of products of bounded-degree polynomials. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def polynomialTestLinear {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) : Poly4 →ₗ[ℝ] ℝ :=
  ∑ i, ∑ p, ∑ k, ∑ q,
    (J i p k q * nodeWeight node i * nodeWeight node p * nodeWeight node k * nodeWeight node q) •
      evalFour (node i) (node p) (node k) (node q)

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_PairSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric double and quadruple sums over unordered pairs. -/

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

def upperPairSum {α : Type*} [Fintype α] [LinearOrder α] (f : α → α → ℝ) : ℝ :=
  ∑ i, ∑ p, if i < p then f i p else 0

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Polynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate symmetry, polynomial quotients, collision divisibility, and specialization. -/

section

noncomputable section
open MvPolynomial
namespace Paper170

def reinsertDiagonal : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] Poly4 :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 3]

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open Module MvPolynomial
namespace Paper170

abbrev BoundedExponents (d : ℕ) := Fin 4 → Fin (d + 1)

def tupleExponent {d : ℕ} (t : BoundedExponents d) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (t i).val)

@[simp] lemma tupleExponent_apply {d : ℕ} (t : BoundedExponents d) (i : Fin 4) :
    tupleExponent t i = (t i).val := rfl

def boxExponentEquiv (d : ℕ) :
    {m : Fin 4 →₀ ℕ // ∀ i, m i ≤ d} ≃ BoundedExponents d where
  toFun m i := ⟨m.val i, Nat.lt_succ_of_le (m.property i)⟩
  invFun t := ⟨tupleExponent t, fun i => Nat.le_of_lt_succ (t i).isLt⟩
  left_inv m := by apply Subtype.ext; ext i; rfl
  right_inv t := rfl

lemma box_eq_restrictSupport (d : ℕ) :
    box4 d = MvPolynomial.restrictSupport ℝ {m | ∀ i, m i ≤ d} := by
  ext P
  rw [box4_membership, MvPolynomial.mem_restrictSupport_iff]
  simp only [degreeOf_le_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]
  exact ⟨fun h m hm i => h i m hm, fun h i m hm => h m hm i⟩

def boxBasis (d : ℕ) : Basis (BoundedExponents d) ℝ (box4 d) :=
  ((MvPolynomial.basisRestrictSupport ℝ _).reindex (boxExponentEquiv d)).map
    (LinearEquiv.ofEq _ _ (box_eq_restrictSupport d).symm)

@[simp] lemma boxBasis_repr (d : ℕ) (P : box4 d) (t : BoundedExponents d) :
    (boxBasis d).repr P t = P.val.coeff (tupleExponent t) := by
  rfl

end Paper170

end
end

section

noncomputable section
namespace Paper170

@[simp] lemma swapFirstPair_mul (P Q : Poly4) :
    swapFirstPair (P * Q) = swapFirstPair P * swapFirstPair Q := by
  exact map_mul (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 1)) P Q

@[simp] lemma swapSecondPair_mul (P Q : Poly4) :
    swapSecondPair (P * Q) = swapSecondPair P * swapSecondPair Q := by
  exact map_mul (MvPolynomial.rename (Equiv.swap (2 : Fin 4) 3)) P Q

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

def diagonalUnivariate (u v : ℝ) : Poly4 →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C u, Polynomial.X, Polynomial.C v]

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem box_rename {d : ℕ} {P : Poly4} (hP : P ∈ box4 d) (e : Equiv.Perm (Fin 4)) :
    rename e P ∈ box4 d := by
  apply (box4_membership _ _).mpr
  intro i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [degreeOf_rename_of_injective e.injective]
  exact (box4_membership _ _).mp hP j

theorem coeff_rename_tuple {d : ℕ} (e : Equiv.Perm (Fin 4)) (P : Poly4)
    (t : BoundedExponents d) :
    (rename e P).coeff (tupleExponent t) =
      P.coeff (tupleExponent (fun i => t (e i))) := by
  have he : (tupleExponent (fun i => t (e i))).mapDomain e = tupleExponent t := by
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  rw [← he, coeff_rename_mapDomain e e.injective]

theorem box_coeff_ext {d : ℕ} {P Q : Poly4} (hP : P ∈ box4 d) (hQ : Q ∈ box4 d)
    (h : ∀ t : BoundedExponents d, P.coeff (tupleExponent t) = Q.coeff (tupleExponent t)) :
    P = Q := by
  have he : (⟨P, hP⟩ : box4 d) = ⟨Q, hQ⟩ := by
    apply (boxBasis d).repr.injective
    ext t
    exact h t
  exact congrArg Subtype.val he

theorem tuple4_eta {α : Type*} (t : Fin 4 → α) : ![t 0, t 1, t 2, t 3] = t := by
  funext i
  fin_cases i <;> simp

abbrev SymmetricCoordinate (d : ℕ) := Sym2 (Fin (d + 1)) × Sym2 (Fin (d + 1))

def tupleOrbit {d : ℕ} (t : BoundedExponents d) : SymmetricCoordinate d :=
  (s(t 0, t 1), s(t 2, t 3))

theorem tupleOrbit_swap_first {d : ℕ} (t : BoundedExponents d) :
    tupleOrbit (fun i => t (Equiv.swap (0 : Fin 4) 1 i)) = tupleOrbit t := by
  change (s(t 1, t 0), s(t 2, t 3)) = (s(t 0, t 1), s(t 2, t 3))
  exact Prod.ext Sym2.eq_swap rfl

theorem tupleOrbit_swap_second {d : ℕ} (t : BoundedExponents d) :
    tupleOrbit (fun i => t (Equiv.swap (2 : Fin 4) 3 i)) = tupleOrbit t := by
  change (s(t 0, t 1), s(t 3, t 2)) = (s(t 0, t 1), s(t 2, t 3))
  exact Prod.ext rfl Sym2.eq_swap

theorem symmetric_coeff_first {s : ℕ} (P : endpointSymmetricSpace s)
    (a b c d : Fin (s - 2 + 1)) :
    P.val.coeff (tupleExponent ![a, b, c, d]) = P.val.coeff (tupleExponent ![b, a, c, d]) := by
  have he : (fun i => (![a, b, c, d] : BoundedExponents (s - 2))
      (Equiv.swap (0 : Fin 4) 1 i)) = ![b, a, c, d] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.1
  change rename (Equiv.swap (0 : Fin 4) 1) P.val = P.val at hp
  have hc := coeff_rename_tuple (Equiv.swap (0 : Fin 4) 1) P.val ![a, b, c, d]
  rwa [he, hp] at hc

theorem symmetric_coeff_second {s : ℕ} (P : endpointSymmetricSpace s)
    (a b c d : Fin (s - 2 + 1)) :
    P.val.coeff (tupleExponent ![a, b, c, d]) = P.val.coeff (tupleExponent ![a, b, d, c]) := by
  have he : (fun i => (![a, b, c, d] : BoundedExponents (s - 2))
      (Equiv.swap (2 : Fin 4) 3 i)) = ![a, b, d, c] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.2
  change rename (Equiv.swap (2 : Fin 4) 3) P.val = P.val at hp
  have hc := coeff_rename_tuple (Equiv.swap (2 : Fin 4) 3) P.val ![a, b, c, d]
  rwa [he, hp] at hc

def symmetricCoefficients {s : ℕ} (P : endpointSymmetricSpace s) :
    SymmetricCoordinate (s - 2) → ℝ := fun q =>
  Sym2.lift₂ ⟨(fun a b c d => P.val.coeff (tupleExponent ![a, b, c, d])),
    fun a b c d => ⟨symmetric_coeff_first P a b c d, symmetric_coeff_second P a b c d⟩⟩ q.1 q.2

@[simp] theorem symmetricCoefficients_orbit {s : ℕ} (P : endpointSymmetricSpace s)
    (t : BoundedExponents (s - 2)) :
    symmetricCoefficients P (tupleOrbit t) = P.val.coeff (tupleExponent t) := by
  simp [symmetricCoefficients, tupleOrbit, tuple4_eta]

def realizeBox (d : ℕ) (f : SymmetricCoordinate d → ℝ) : box4 d :=
  (boxBasis d).equivFun.symm (fun t => f (tupleOrbit t))

@[simp] theorem realizeBox_coeff (d : ℕ) (f : SymmetricCoordinate d → ℝ)
    (t : BoundedExponents d) :
    (realizeBox d f).val.coeff (tupleExponent t) = f (tupleOrbit t) := by
  change (boxBasis d).equivFun ((boxBasis d).equivFun.symm _) t = _
  rw [LinearEquiv.apply_symm_apply]

theorem realizeBox_symmetric (s : ℕ) (f : SymmetricCoordinate (s - 2) → ℝ) :
    (realizeBox (s - 2) f).val ∈ endpointSymmetricSpace s := by
  apply (symmetric_space_membership _ _).mpr
  refine ⟨(box4_membership _ _).mp (realizeBox (s - 2) f).property, ?_, ?_⟩
  · apply box_coeff_ext (box_rename (realizeBox (s - 2) f).property _)
      (realizeBox (s - 2) f).property
    intro t
    change (rename (Equiv.swap (0 : Fin 4) 1) _).coeff (tupleExponent t) = _
    rw [coeff_rename_tuple, realizeBox_coeff, realizeBox_coeff, tupleOrbit_swap_first]
  · apply box_coeff_ext (box_rename (realizeBox (s - 2) f).property _)
      (realizeBox (s - 2) f).property
    intro t
    change (rename (Equiv.swap (2 : Fin 4) 3) _).coeff (tupleExponent t) = _
    rw [coeff_rename_tuple, realizeBox_coeff, realizeBox_coeff, tupleOrbit_swap_second]

def realizeSymmetric (s : ℕ) (f : SymmetricCoordinate (s - 2) → ℝ) : endpointSymmetricSpace s :=
  ⟨(realizeBox (s - 2) f).val, realizeBox_symmetric s f⟩

def symmetricCoordinatesEquiv (s : ℕ) :
    endpointSymmetricSpace s ≃ₗ[ℝ] (SymmetricCoordinate (s - 2) → ℝ) where
  toFun := symmetricCoefficients
  invFun := realizeSymmetric s
  left_inv P := by
    apply Subtype.ext
    apply box_coeff_ext (realizeBox (s - 2) (symmetricCoefficients P)).property
      ((box4_membership _ _).mpr ((symmetric_space_membership _ _).mp P.property).1)
    intro t
    rw [realizeBox_coeff, symmetricCoefficients_orbit]
  right_inv f := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Sym2.ind
    induction b using Sym2.ind
    simp [symmetricCoefficients, realizeSymmetric, realizeBox_coeff, tupleOrbit]
  map_add' P Q := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Sym2.ind
    induction b using Sym2.ind
    simp [symmetricCoefficients]
  map_smul' c P := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Sym2.ind
    induction b using Sym2.ind
    simp [symmetricCoefficients]

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The support form, injectivity criterion, and support-space dimension. -/

section

noncomputable section
namespace Paper170

@[simp] lemma evalFour_mul (x u y v : ℝ) (P Q : Poly4) :
    evalFour x u y v (P * Q) = evalFour x u y v P * evalFour x u y v Q :=
  map_mul (MvPolynomial.aeval ![x, u, y, v]) P Q

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Isotropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isotropic evaluation image and order-pairing identities. -/

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

def isotropicTerm {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) (P Q : Poly4)
    (i p k q : Fin n) : ℝ :=
  J i p k q * nodeWeight node i * nodeWeight node p * nodeWeight node k * nodeWeight node q *
    evalFour (node i) (node p) (node k) (node q) fullDifference *
    evalFour (node i) (node p) (node k) (node q) P *
    evalFour (node i) (node p) (node k) (node q) Q

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine polygonal subdivisions and chain parametrizations. -/

section

noncomputable section
open Set
open Zarankiewicz
open scoped Classical
namespace Paper170

/-- An affine cover retaining its actual interval endpoints. -/
structure AffineCoverData {a b : Plane} (γ : Path a b) where
  intervals : Finset (unitInterval × unitInterval)
  ordered : ∀ ab ∈ intervals, ab.1 < ab.2
  cover : ∀ t : unitInterval, ∃ ab ∈ intervals, ab.1 ≤ t ∧ t ≤ ab.2
  affine : ∀ ab ∈ intervals, ∀ t : unitInterval,
    γ (intervalSegment ab.1 ab.2 t) = Zarankiewicz.segmentPoint (γ ab.1) (γ ab.2) t.val

def AffineCoverData.segment (a b : Plane) : AffineCoverData (Path.segment a b) where
  intervals := {(0,1)}
  ordered := by
    intro ab hab
    have h : ab = (0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  cover := fun t => ⟨(0,1), Finset.mem_singleton_self _, t.property⟩
  affine := by
    intro ab hab t
    have h : ab = (0,1) := Finset.mem_singleton.mp hab
    subst ab
    simp only [intervalSegment_zero_one, Path.source, Path.target, Path.segment_apply,
      AffineMap.lineMap_apply_module, Zarankiewicz.segmentPoint]

def AffineCoverData.trans {a b c : Plane} {γ : Path a b} {η : Path b c}
    (S : AffineCoverData γ) (T : AffineCoverData η) : AffineCoverData (γ.trans η) where
  intervals := S.intervals.image (fun ab => (intervalLeft ab.1, intervalLeft ab.2)) ∪
    T.intervals.image (fun ab => (intervalRight ab.1, intervalRight ab.2))
  ordered := by
    intro ab hab
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalLeft_strictMono (S.ordered cd hcd)
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalRight_strictMono (T.ordered cd hcd)
  cover := by
    intro t
    by_cases ht : t.val ≤ 1/2
    · let u : unitInterval := ⟨2*t.val, by constructor <;> linarith [t.property.1]⟩
      obtain ⟨ab,hab,ha,hb⟩ := S.cover u
      have hu : intervalLeft u=t := by apply Subtype.ext; change (2*t.val)/2=t.val; ring
      refine ⟨(intervalLeft ab.1,intervalLeft ab.2),
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩), ?_, ?_⟩
      · change intervalLeft ab.1 ≤ t
        rw [←hu]
        exact intervalLeft_strictMono.monotone ha
      · change t ≤ intervalLeft ab.2
        rw [←hu]
        exact intervalLeft_strictMono.monotone hb
    · let u : unitInterval := ⟨2*t.val-1, by constructor <;> linarith [t.property.2]⟩
      obtain ⟨ab,hab,ha,hb⟩ := T.cover u
      have hu : intervalRight u=t := by apply Subtype.ext; change (1+(2*t.val-1))/2=t.val; ring
      refine ⟨(intervalRight ab.1,intervalRight ab.2),
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩), ?_, ?_⟩
      · change intervalRight ab.1 ≤ t
        rw [←hu]
        exact intervalRight_strictMono.monotone ha
      · change t ≤ intervalRight ab.2
        rw [←hu]
        exact intervalRight_strictMono.monotone hb
  affine := by
    intro ab hab t
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      rw [intervalSegment_left, path_trans_intervalLeft, path_trans_intervalLeft, path_trans_intervalLeft]
      exact S.affine cd hcd t
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      rw [intervalSegment_right, path_trans_intervalRight, path_trans_intervalRight, path_trans_intervalRight]
      exact T.affine cd hcd t

end Paper170

end
end

section

noncomputable section
open Set
open Zarankiewicz
open scoped Classical
namespace Paper170

def PolygonalParametrization.cast {a b c d : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (ha : c = a) (hb : d = b) :
    PolygonalParametrization (γ.cast ha hb) where
  pieces := P.pieces
  positive := P.positive
  knot := P.knot
  increasing := P.increasing
  first := P.first
  last := P.last
  affine := P.affine

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reorientation invariance and normalization without adjacent crossings or crossing knots. -/

section

/-! Reversing chosen oriented representatives changes no spatial drawing or crossing count. -/
noncomputable section
open Set
open scoped Classical
namespace Paper170
variable {V E : Type}

def Graph.reorient (G : Graph V E) (reverse : E → Bool) : Graph V E where
  src e := if reverse e = true then G.dst e else G.src e
  dst e := if reverse e = true then G.src e else G.dst e
  loopless e := by
    by_cases h : reverse e = true
    · simpa only [ite_eq_left h] using (G.loopless e).symm
    · simpa only [ite_eq_right h] using G.loopless e
  simple e f h := by
    apply G.simple e f
    by_cases he : reverse e = true <;> by_cases hf : reverse f = true <;>
      simp [he,hf] at h <;> tauto

theorem unitInterval_symm_mem_Ioo (t : unitInterval) :
    unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 ↔ t ∈ Ioo (0 : unitInterval) 1 := by
  change (0 < 1-(t : ℝ) ∧ 1-(t : ℝ) < 1) ↔ (0 < (t : ℝ) ∧ (t : ℝ) < 1)
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith

namespace ContinuousDrawing
variable {G : Graph V E}

def reorientedPath (D : ContinuousDrawing G) (reverse : E → Bool) (e : E) :
    Path (D.vertex ((G.reorient reverse).src e)) (D.vertex ((G.reorient reverse).dst e)) :=
  if h : reverse e = true then (D.edge e).symm.cast
    (by simp only [Graph.reorient,ite_eq_left h]) (by simp only [Graph.reorient,ite_eq_left h])
  else (D.edge e).cast
    (by simp only [Graph.reorient,ite_eq_right h]) (by simp only [Graph.reorient,ite_eq_right h])

theorem reorientedPath_apply (D : ContinuousDrawing G) (reverse : E → Bool) (e : E)
    (t : unitInterval) : D.reorientedPath reverse e t =
      if reverse e = true then D.edge e (unitInterval.symm t) else D.edge e t := by
  unfold reorientedPath
  split <;> rfl

def reorient (D : ContinuousDrawing G) (reverse : E → Bool) :
    ContinuousDrawing (G.reorient reverse) where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.reorientedPath reverse
  edge_injective e := by
    intro s t hst
    rw [reorientedPath_apply,reorientedPath_apply] at hst
    by_cases h : reverse e = true
    · rw [ite_eq_left h,ite_eq_left h] at hst
      exact unitInterval.symm_bijective.1 (D.edge_injective e hst)
    · rw [ite_eq_right h,ite_eq_right h] at hst
      exact D.edge_injective e hst
  interior_avoids_vertices e t ht v := by
    rw [reorientedPath_apply]
    by_cases h : reverse e = true
    · rw [ite_eq_left h]
      exact D.interior_avoids_vertices e _ ((unitInterval_symm_mem_Ioo t).mpr ht) v
    · rw [ite_eq_right h]
      exact D.interior_avoids_vertices e t ht v

theorem reorient_edgeInterior (D : ContinuousDrawing G) (reverse : E → Bool) (e : E) :
    edgeInterior (D.reorient reverse) e = edgeInterior D e := by
  ext x
  by_cases h : reverse e = true
  · constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨unitInterval.symm t,(unitInterval_symm_mem_Ioo t).mpr ht,?_⟩
      change D.reorientedPath reverse e t = x at hx
      simpa only [reorientedPath_apply,ite_eq_left h] using hx
    · rintro ⟨t,ht,hx⟩
      refine ⟨unitInterval.symm t,(unitInterval_symm_mem_Ioo t).mpr ht,?_⟩
      change D.reorientedPath reverse e (unitInterval.symm t) = x
      simpa only [reorientedPath_apply,ite_eq_left h,unitInterval.symm_symm] using hx
  · constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨t,ht,?_⟩
      change D.reorientedPath reverse e t = x at hx
      simpa only [reorientedPath_apply,ite_eq_right h] using hx
    · rintro ⟨t,ht,hx⟩
      refine ⟨t,ht,?_⟩
      change D.reorientedPath reverse e t = x
      simpa only [reorientedPath_apply,ite_eq_right h] using hx

theorem reorient_crossingPoints (D : ContinuousDrawing G) (reverse : E → Bool) :
    crossingPoints (D.reorient reverse) = crossingPoints D := by
  ext x
  simp only [crossingPoints, mem_ofPred_eq, reorient_edgeInterior]

end ContinuousDrawing

namespace AdmissibleDrawing
variable {G : Graph V E}

def reorient (D : AdmissibleDrawing G) (reverse : E → Bool) :
    AdmissibleDrawing (G.reorient reverse) where
  toContinuousDrawing := D.toContinuousDrawing.reorient reverse
  crossings_finite := by
    rw [ContinuousDrawing.reorient_crossingPoints]
    exact D.crossings_finite
  crossings_proper e f hef x he hf := by
    rw [ContinuousDrawing.reorient_edgeInterior] at he hf
    rw [ContinuousDrawing.reorient_edgeInterior,ContinuousDrawing.reorient_edgeInterior]
    exact D.crossings_proper e f hef x he hf
  no_triples e f g hef heg hfg := by
    simp only [ContinuousDrawing.reorient_edgeInterior]
    exact D.no_triples e f g hef heg hfg

end AdmissibleDrawing
end Paper170

end
end

section

/-! Reorientation preserves the minimum property among ordinary drawings. -/
noncomputable section
namespace Paper170
variable {V E : Type}

namespace AdmissibleDrawing
variable {G H : Graph V E}

def castGraph (h : G = H) (D : AdmissibleDrawing G) : AdmissibleDrawing H := h ▸ D

end AdmissibleDrawing
end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

variable {V E : Type} {G : Graph V E}

def reparametrizedContinuous (D : ContinuousDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path) : ContinuousDrawing G where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge e := (P e).path
  edge_injective := hP
  interior_avoids_vertices e t ht v :=
    Zarankiewicz.path_interior_avoids_vertices_of_range D.vertex (G.src e) (G.dst e)
      (P e).path (hP e) (by
        intro w hw
        obtain ⟨s, hs⟩ := (P e).path_range_subset hw
        rcases Paper170Geometry.drawing_edge_vertex_parameter D e s w hs with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2) t ht v

lemma reparametrized_interior (D : ContinuousDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path)
    (htrace : ∀ e, range (P e).path = range (D.edge e)) (e : E) :
    edgeInterior (reparametrizedContinuous D P hP) e = edgeInterior D e := by
  ext x
  constructor
  · intro hx
    apply Paper170Geometry.edgeInterior_of_range_not_vertices D e x
    · rw [← htrace e]
      exact Paper170Geometry.edgeInterior_subset_range _ e hx
    · exact Paper170Geometry.edgeInterior_not_vertex (reparametrizedContinuous D P hP) e x hx
  · intro hx
    apply Paper170Geometry.edgeInterior_of_range_not_vertices (reparametrizedContinuous D P hP) e x
    · change x ∈ range (P e).path
      rw [htrace e]
      exact Paper170Geometry.edgeInterior_subset_range D e hx
    · exact Paper170Geometry.edgeInterior_not_vertex D e x hx

lemma reparametrized_crossings (D : ContinuousDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path)
    (htrace : ∀ e, range (P e).path = range (D.edge e)) :
    crossingPoints (reparametrizedContinuous D P hP) = crossingPoints D := by
  ext x
  simp only [crossingPoints, reparametrized_interior D P hP htrace]

def reparametrizedDrawing (D : AdmissibleDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path)
    (htrace : ∀ e, range (P e).path = range (D.edge e)) : AdmissibleDrawing G where
  toContinuousDrawing := reparametrizedContinuous D.toContinuousDrawing P hP
  crossings_finite := by
    rw [reparametrized_crossings D.toContinuousDrawing P hP htrace]
    exact D.crossings_finite
  crossings_proper := by
    intro e f hef x he hf
    simp only [reparametrized_interior D.toContinuousDrawing P hP htrace] at he hf ⊢
    exact D.crossings_proper e f hef x he hf
  no_triples := by
    intro e f g hef heg hfg
    simp only [reparametrized_interior D.toContinuousDrawing P hP htrace]
    exact D.no_triples e f g hef heg hfg

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Triangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even triangular interpolation and unisolvence. -/

section

/-! The even two-triangle set, as actual ordered interpolation coordinates. -/
noncomputable section
namespace Paper170

theorem mem_evenTriangle (s : ℕ) (p q : Fin (2*s)) :
    (p,q) ∈ evenTriangle s ↔
      (p.val < s ∧ q < p) ∨ (s ≤ p.val ∧ p < q) := by
  simp [evenTriangle]

def evenTriangleOffDiagEquiv (s : ℕ) :
    EvenTriangleCoord s ≃ ↥((Finset.univ : Finset (Fin s)).offDiag) where
  toFun pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    have hpq := (mem_evenTriangle s p q).mp hpq
    by_cases h : p.val < s
    · exact ⟨(⟨p.val, h⟩, ⟨q.val, by rcases hpq with hq | hq <;> omega⟩), by
        simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, ne_eq, Fin.mk.injEq]
        rcases hpq with hq | hq <;> omega⟩
    · exact ⟨(⟨p.val-s, by omega⟩, ⟨q.val-s, by omega⟩), by
        simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, ne_eq, Fin.mk.injEq]
        rcases hpq with hq | hq <;> omega⟩
  invFun pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    have hpq : p ≠ q := (Finset.mem_offDiag.mp hpq).2.2
    by_cases h : q < p
    · exact ⟨(⟨p.val, by omega⟩, ⟨q.val, by omega⟩),
        (mem_evenTriangle s _ _).mpr (Or.inl ⟨p.isLt,h⟩)⟩
    · exact ⟨(⟨p.val+s, by omega⟩, ⟨q.val+s, by omega⟩),
        (mem_evenTriangle s _ _).mpr (Or.inr ⟨by change s ≤ p.val+s; omega,by
          have hpq := Fin.val_ne_of_ne hpq
          change p.val+s < q.val+s
          omega⟩)⟩
  left_inv pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    have hpq := (mem_evenTriangle s p q).mp hpq
    apply Subtype.ext
    dsimp
    split_ifs with h h' h'
    · rfl
    · change ¬q.val < p.val at h'
      simp only [Fin.lt_def] at hpq
      omega
    · change q.val-s < p.val-s at h'
      simp only [Fin.lt_def] at hpq
      omega
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;>
        simp only [Fin.lt_def] at hpq <;> omega
  right_inv pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    apply Subtype.ext
    dsimp
    split_ifs with h h' h'
    · rfl
    · change ¬p.val < s at h'
      omega
    · change p.val+s < s at h'
      omega
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_OrderPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Order-detecting interpolation and its kernel. -/

section

/-! The order pairing as a nonzero diagonal pairing on the even two-triangle set. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def evenTriangleWeight (s : ℕ) (node : Fin (2*s) → ℝ) (a : EvenTriangleCoord s) : ℝ :=
  (if a.val.1.val < s then -1 else 1) * (node a.val.1-node a.val.2) /
    (Zarankiewicz.derivativeAtNode node a.val.1 * Zarankiewicz.derivativeAtNode node a.val.2)

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric crossing tensors, local orders, supports, and bilinear chain pairings. -/

section

/-! The local order in the tensor is the actual order of outward incident edges. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170
variable {V E : Type} {G : Graph V E}

def completeIncidentEdge {n : ℕ} (i : Fin n) (p : {j : Fin n // j ≠ i}) :
    (completeGraph n).IncidentEdge i :=
  if h : i < p.val then ⟨⟨(i,p.val),h⟩,Or.inl rfl⟩
  else ⟨⟨(p.val,i),lt_of_le_of_ne (le_of_not_gt h) p.property⟩,Or.inr rfl⟩

end Paper170

end
end

section

/-! The directed complete-graph chains and the chosen unoriented edge representatives agree. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E A : Type} [Fintype E] [Fintype A]

def liftedChain {n : ℕ} (z : Fin n → Fin n → ℝ) : CompleteEdge n → ℝ :=
  fun e => ∑ i, ∑ p, z i p * completeEdgeVector i p e

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_TwoPage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting actual crossing points of the explicit two-page drawing. -/

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

def tupleFirstEdge {n : ℕ} (v : Fin 4 → Fin n) (hv : StrictMono v) : CompleteEdge n :=
  ⟨(v 0, v 2), hv (by decide)⟩

def tupleSecondEdge {n : ℕ} (v : Fin 4 → Fin n) (hv : StrictMono v) : CompleteEdge n :=
  ⟨(v 1, v 3), hv (by decide)⟩

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_VertexEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex specialization, local interpolation tests, and kernel vanishing. -/

section

/-! The local test polynomial reduces the global tensor sum to its adjacent-edge pairings. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def vertexTestSummand {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) (H : Poly4)
    (i p k q : Fin n) : ℝ :=
  J i p k q * nodeWeight node i * nodeWeight node p * nodeWeight node k * nodeWeight node q *
    evalFour (node i) (node p) (node k) (node q) H

end Paper170

end
end

section

/-! Lagrange isolation of each vertex and the full kernel vertex-vanishing theorem. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def vertexPairingFunctional {n : ℕ} (node : Fin n → ℝ)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i}) (P : Poly4) (B : Poly2) :
    Polynomial ℝ →ₗ[ℝ] ℝ :=
  ∑i, ((nodeWeight node i)^2 *
    orderPairing (fun j : {j : Fin n // j≠i} => node j.val) (orders i)
      (vertexSpecialization (node i) P) B) • (Polynomial.aeval (node i)).toLinearMap

end Paper170

end
end

end OAI
end



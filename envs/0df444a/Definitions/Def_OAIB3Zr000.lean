-- Prove2me | Definitions.Def_OAIB3Zr000
-- name    : OAIB3Zr000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T13:11:37.09952+00:00
-- url     : https://prove2.me/theorems/4110c9fa-6d10-4c8c-85e6-3ea0c08e134e
-- title:
--   Definitions bundle OAIB3Zr000 of the split of OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 237 declarations of OpenAI's Lean: 80 definitions, 5 inductive types or structures and 152 theorems. The definitions and types are `OAI.Zarankiewicz.AdmissibleDrawing.toFiniteIntersectionDrawing`, `OAI.Zarankiewicz.AxisIndependentTriple`, `OAI.Zarankiewicz.BalancedAxisRealization`, `OAI.Zarankiewicz.BalancedAxisRealization.candidateCrossings`, `OAI.Zarankiewicz.BalancedAxisRealization.crossingCandidates`, `OAI.Zarankiewicz.BalancedAxisRealization.drawing`, `OAI.Zarankiewicz.BiBounded`, `OAI.Zarankiewicz.BiExponent`, `OAI.Zarankiewicz.BiPoly`, `OAI.Zarankiewicz.Bounded`, `OAI.Zarankiewicz.ClosedSegmentsMeet`, `OAI.Zarankiewicz.ContinuousDrawing.replaceTwoEdges`, `OAI.Zarankiewicz.ContinuousDrawing.replaceTwoRoutes`, `OAI.Zarankiewicz.DiskPassage`, `OAI.Zarankiewicz.DrawingMark`, `OAI.Zarankiewicz.DrawingPassages`, `OAI.Zarankiewicz.DrawingPassages.ArcIndex`, `OAI.Zarankiewicz.DrawingPassages.InnerIndex`, `OAI.Zarankiewicz.DrawingPassages.Port`, `OAI.Zarankiewicz.DrawingPassages.PortsAt`, `OAI.Zarankiewicz.DrawingPassages.arc`, `OAI.Zarankiewicz.DrawingPassages.arcEnd`, `OAI.Zarankiewicz.DrawingPassages.arcEndMark`, `OAI.Zarankiewicz.DrawingPassages.arcStart`, `OAI.Zarankiewicz.DrawingPassages.arcStartMark`, `OAI.Zarankiewicz.DrawingPassages.chordCrossingOrigin`, `OAI.Zarankiewicz.DrawingPassages.chordCrossings`, `OAI.Zarankiewicz.DrawingPassages.chordCrossingsAt`, `OAI.Zarankiewicz.DrawingPassages.crossingChord`, `OAI.Zarankiewicz.DrawingPassages.crossingDisk`, `OAI.Zarankiewicz.DrawingPassages.endPortAt`, `OAI.Zarankiewicz.DrawingPassages.firstArc`, `OAI.Zarankiewicz.DrawingPassages.incomingArc`, `OAI.Zarankiewicz.DrawingPassages.incomingPort`, `OAI.Zarankiewicz.DrawingPassages.innerMark`, `OAI.Zarankiewicz.DrawingPassages.lastArc`, `OAI.Zarankiewicz.DrawingPassages.orderedArc`, `OAI.Zarankiewicz.DrawingPassages.orderedInner`, `OAI.Zarankiewicz.DrawingPassages.outgoingArc`, `OAI.Zarankiewicz.DrawingPassages.outgoingPort` and 45 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Crossing_AssembledAdmissibleDrawing`, `Crossing_AxisAdmissibility`, `Crossing_AxisConcurrency`, `Crossing_AxisContinuousDrawing`, `Crossing_AxisFiniteCrossings`, `Crossing_AxisGenericPositions`, `Crossing_AxisSegments`, `Crossing_BalancedAxisCrossingCount`, `Crossing_BalancedAxisDrawing`, `Crossing_BalancedAxisIntervals`, `Crossing_BalancedRayPairs`, `Crossing_Bivariate`, `Crossing_BivariateCoefficients`, `Crossing_ChordTransversality`, `Crossing_CircleOffset`, `Crossing_CrossingCoordinates`, `Crossing_CrossingDiskCount`, `Crossing_CrossingDiskIncidence`, `Crossing_CrossingDiskNeighborhood`, `Crossing_CrossingDiskUniqueness`, `Crossing_CrossingIncidence`, `Crossing_CrossingReconnection`, `Crossing_DiskFillingContainment`, `Crossing_DiskPassage`, `Crossing_DrawingDiskIsolation`, `Crossing_DrawingMarks`, `Crossing_DrawingPassages`, `Crossing_DrawingPorts`, `Crossing_DrawingVertexPlacement`, `Crossing_EndpointFlagPairing`, `Crossing_FiniteIntersectionDrawing`, `Crossing_IncidentSpokePorts`, `Crossing_InnerDrawingPassages`, `Crossing_IntervalSegments`, `Crossing_LocallyStraightNormalization`, `Crossing_OffsetVectors`, `Crossing_OrderedExteriorPaths`, `Crossing_OrderedPassages`, `Crossing_ParallelDirection`, `Crossing_PathSubarc`, `Crossing_PlanarDeterminant`, `Crossing_PlanarSegments`, `Crossing_PolygonComposition`, `Crossing_PolygonalChainOperations`, `Crossing_PolygonalChains`, `Crossing_PolynomialKernel`, `Crossing_ProperSegmentCrossing`, `Crossing_RadialExterior`, `Crossing_ReconnectionAvoidance`, `Crossing_ReconnectionChords`, `Crossing_ReconnectionVertexAvoidance`, `Crossing_ReplaceDrawingEdges`, `Crossing_ReplaceDrawingRangeCases`, `Crossing_RetainedArcDisjointness`, `Crossing_RetainedDrawingArcs`, `Crossing_RoundCircleChords`, `Crossing_RoundDiskClearance`, `Crossing_SegmentContinuity`, `Crossing_SegmentCrossingCoordinates`, `Crossing_SegmentIntersectionUnique`, `Crossing_SegmentSides`, `Crossing_VertexEndpointPorts`.
--
--   **Imports.** It imports the published bundle `Def_BipartiteCrossing`.
--
--   **Imported by** (directly, in this split): the bundles `OAIB3Zr002` and `OAIB3Zr003`.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing

section
-- module Solutions.OAIB3_Zar.Compat
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
-- module Solutions.OAIB3_Zar.Crossing_PlanarSegments
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

@[simp] theorem segmentPoint_zero (a b : Plane) : segmentPoint a b 0 = a := by
  simp [segmentPoint]

@[simp] theorem segmentPoint_one (a b : Plane) : segmentPoint a b 1 = b := by
  simp [segmentPoint]

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
-- module Solutions.OAIB3_Zar.Crossing_PlanarDeterminant
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
-- module Solutions.OAIB3_Zar.Crossing_OffsetVectors
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
-- module Solutions.OAIB3_Zar.Crossing_RoundDiskClearance
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
-- module Solutions.OAIB3_Zar.Crossing_CrossingIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

def pairCrossings (D : AdmissibleDrawing m n) (e f : BipartiteEdge m n) : Finset Plane :=
  D.crossings_finite.toFinset.filter (fun x => e ≠ f ∧
    x ∈ edgeInterior D.toContinuousDrawing e ∧ x ∈ edgeInterior D.toContinuousDrawing f)

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

structure FiniteIntersectionDrawing (m n : ℕ) extends ContinuousDrawing m n where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    edgeInterior toContinuousDrawing e ∩ edgeInterior toContinuousDrawing f ∩
      edgeInterior toContinuousDrawing g = ∅

abbrev AdmissibleDrawing.toFiniteIntersectionDrawing {m n : ℕ} (D : AdmissibleDrawing m n) :
    FiniteIntersectionDrawing m n where
  toContinuousDrawing := D.toContinuousDrawing
  crossings_finite := D.crossings_finite
  no_triples := D.no_triples

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_IntervalSegments
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
-- module Solutions.OAIB3_Zar.Crossing_PathSubarc
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
-- module Solutions.OAIB3_Zar.Crossing_DrawingMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def drawingMarks (D : FiniteIntersectionDrawing m n) : Set Plane :=
  Set.range D.vertex ∪ crossingPoints D.toContinuousDrawing

theorem crossing_not_vertex (D : FiniteIntersectionDrawing m n) (x : Plane)
    (hx : x ∈ crossingPoints D.toContinuousDrawing) (v : BipartiteVertex m n) : x ≠ D.vertex v := by
  obtain ⟨e,f,hef,⟨t,ht,he⟩,hf⟩ := hx
  intro hh
  exact D.interior_avoids_vertices e t ht v (he.trans hh)

theorem marked_parameter_zero (D : FiniteIntersectionDrawing m n) (e : BipartiteEdge m n) :
    (0 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨.inl e.1,(D.edge e).source.symm⟩

theorem marked_parameter_one (D : FiniteIntersectionDrawing m n) (e : BipartiteEdge m n) :
    (1 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨.inr e.2,(D.edge e).target.symm⟩

theorem unmarked_edge_point_interior (D : FiniteIntersectionDrawing m n) (e : BipartiteEdge m n)
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

theorem unmarked_intersection_same_edge (D : FiniteIntersectionDrawing m n)
    (e f : BipartiteEdge m n) (s t : unitInterval)
    (he : D.edge e s=D.edge f t) (hs : D.edge e s ∉ drawingMarks D) : e=f := by
  by_contra hef
  have hsi := unmarked_edge_point_interior D e s hs
  have hti := unmarked_edge_point_interior D f t (he ▸ hs)
  exact hs (Or.inr ⟨e,f,hef,⟨s,hsi,rfl⟩,⟨t,hti,he.symm⟩⟩)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingDiskIsolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

abbrev DrawingMark (D : FiniteIntersectionDrawing m n) := ↥(drawingMarks D)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DiskPassage
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
-- module Solutions.OAIB3_Zar.Crossing_OrderedPassages
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
-- module Solutions.OAIB3_Zar.Crossing_DrawingPassages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

structure DrawingPassages (D : FiniteIntersectionDrawing m n) where
  radius : ℝ
  radius_pos : 0 < radius
  disks_disjoint : ∀ x y : DrawingMark D, x ≠ y →
    Disjoint (closedRoundDisk x.val radius) (closedRoundDisk y.val radius)
  count : BipartiteEdge m n → ℕ
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

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ParallelDirection
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
-- module Solutions.OAIB3_Zar.Crossing_RadialExterior
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
-- module Solutions.OAIB3_Zar.Crossing_RetainedDrawingArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

abbrev ArcIndex (C : DrawingPassages D) := (e : BipartiteEdge m n) × Fin (C.count e)

theorem node_mark (C : DrawingPassages D) (e : BipartiteEdge m n) (i : Fin (C.count e+1)) :
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

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RetainedArcDisjointness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

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

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

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

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentSides
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

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentContinuity
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

def SegmentPairTransverse (a b c d : Plane) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
    segmentPoint a b t = segmentPoint c d u →
      det2 (b-a) (d-c) ≠ 0 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ChordTransversality
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
-- module Solutions.OAIB3_Zar.Crossing_RoundCircleChords
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
-- module Solutions.OAIB3_Zar.Crossing_InnerDrawingPassages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

abbrev InnerIndex (C : DrawingPassages D) :=
  (e : BipartiteEdge m n) × {i : Fin (C.count e+1) // 0 < i.val ∧ i.val < C.count e}

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
    (C.innerMark p).val ∈ crossingPoints D.toContinuousDrawing := by
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

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingDiskIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

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
  have hp : (C.innerMark p).val ∈ edgeInterior D.toContinuousDrawing p.1 :=
    ⟨C.node p.1 p.2.val,C.inner_parameter_interior p,rfl⟩
  have hq : (C.innerMark p).val ∈ edgeInterior D.toContinuousDrawing q.1 := by
    rw [hpqM]
    exact ⟨C.node q.1 q.2.val,C.inner_parameter_interior q,rfl⟩
  have hr : (C.innerMark p).val ∈ edgeInterior D.toContinuousDrawing r.1 := by
    rw [hprM]
    exact ⟨C.node r.1 r.2.val,C.inner_parameter_interior r,rfl⟩
  have hmem : (C.innerMark p).val ∈ edgeInterior D.toContinuousDrawing p.1 ∩
      edgeInterior D.toContinuousDrawing q.1 ∩ edgeInterior D.toContinuousDrawing r.1 := ⟨⟨hp,hq⟩,hr⟩
  rw [D.no_triples p.1 q.1 r.1 heq her hfr] at hmem
  exact hmem

end Zarankiewicz.DrawingPassages

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

def vertexMark (_C : DrawingPassages D) (v : BipartiteVertex m n) : DrawingMark D :=
  ⟨D.vertex v,Or.inl ⟨v,rfl⟩⟩

theorem vertexMark_injective (C : DrawingPassages D) : Function.Injective C.vertexMark := by
  intro v w he
  exact D.vertex_injective (congrArg Subtype.val he)

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DiskFillingContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

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
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

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
    (v : BipartiteVertex m n) :
    Disjoint (Set.range (C.crossingChord p)) (closedRoundDisk (D.vertex v) C.radius) := by
  have hn : C.innerMark p ≠ C.vertexMark v := by
    intro he
    exact crossing_not_vertex D (C.innerMark p).val (C.innerMark_is_crossing p) v (congrArg Subtype.val he)
  exact (C.disks_disjoint _ _ hn).mono (C.crossingChord_range_subset_disk p) Set.Subset.rfl

end DrawingPassages
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentIntersectionUnique
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
-- module Solutions.OAIB3_Zar.Crossing_CrossingDiskUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

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
    ∃ w : DrawingMark D, w.val ∈ crossingPoints D.toContinuousDrawing ∧ x ∈ C.chordCrossingsAt w := by
  obtain ⟨p,q,hpq,hp,hq⟩ := hx
  refine ⟨C.innerMark p,C.innerMark_is_crossing p,p,q,hpq,rfl,?_,hp,hq⟩
  exact (C.chord_meeting_marks_eq p q hp hq).symm

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingDiskCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
open scoped Classical
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

def chordCrossingOrigin (C : DrawingPassages D) (x : Plane) : Plane :=
  if hx : x ∈ C.chordCrossings then (C.chord_crossing_original_mark hx).choose.val else 0

theorem chordCrossingOrigin_mapsTo (C : DrawingPassages D) :
    Set.MapsTo C.chordCrossingOrigin C.chordCrossings (crossingPoints D.toContinuousDrawing) := by
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

end Zarankiewicz.DrawingPassages

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

def joinedSequence (v w : ℕ → Plane) (n : ℕ) (i : ℕ) : Plane :=
  if i<n then v i else w (i-n)

theorem joinedSequence_left (v w : ℕ → Plane) (n : ℕ) (h : v n=w 0)
    (i : ℕ) (hi : i≤n) : joinedSequence v w n i=v i := by
  unfold joinedSequence
  by_cases hin : i < n
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
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

structure PolygonalChain (O : Set Plane) (a b : Plane) where
  pieces : ℕ
  vertices : ℕ → Plane
  first : vertices 0=a
  last : vertices pieces=b
  start_mem : a ∈ O
  inside : ∀ i, i < pieces → segment ℝ (vertices i) (vertices (i+1)) ⊆ O

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChainOperations
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
-- module Solutions.OAIB3_Zar.Crossing_VertexEndpointPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

def firstArc (C : DrawingPassages D) (e : BipartiteEdge m n) : C.ArcIndex :=
  ⟨e,⟨0,C.count_pos e⟩⟩

def lastArc (C : DrawingPassages D) (e : BipartiteEdge m n) : C.ArcIndex :=
  ⟨e,⟨C.count e-1,by have h := C.count_pos e; omega⟩⟩

theorem lastArc_node (C : DrawingPassages D) (e : BipartiteEdge m n) :
    (C.lastArc e).2.succ=Fin.last (C.count e) := by
  apply Fin.ext
  have h := C.count_pos e
  change C.count e-1+1=C.count e
  omega

theorem firstArc_mark (C : DrawingPassages D) (e : BipartiteEdge m n) :
    C.arcStartMark (C.firstArc e)=C.vertexMark (.inl e.1) := by
  apply Subtype.ext
  change D.edge e (C.node e 0)=D.vertex (.inl e.1)
  rw [C.first,Path.source]

theorem lastArc_mark (C : DrawingPassages D) (e : BipartiteEdge m n) :
    C.arcEndMark (C.lastArc e)=C.vertexMark (.inr e.2) := by
  apply Subtype.ext
  change D.edge e (C.node e (C.lastArc e).2.succ)=D.vertex (.inr e.2)
  rw [C.lastArc_node,C.last,Path.target]

def startPortAt (C : DrawingPassages D) (e : BipartiteEdge m n) : C.PortsAt (C.vertexMark (.inl e.1)) :=
  ⟨(C.firstArc e,false),C.firstArc_mark e⟩

def endPortAt (C : DrawingPassages D) (e : BipartiteEdge m n) : C.PortsAt (C.vertexMark (.inr e.2)) :=
  ⟨(C.lastArc e,true),C.lastArc_mark e⟩

end Zarankiewicz.DrawingPassages

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
namespace DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

def orderedArc (C : DrawingPassages D) (e : BipartiteEdge m n) (i : ℕ) : C.ArcIndex :=
  ⟨e,⟨min i (C.count e-1),by have h := C.count_pos e; omega⟩⟩

theorem orderedArc_val (C : DrawingPassages D) (e : BipartiteEdge m n) (i : ℕ)
    (hi : i < C.count e) : (C.orderedArc e i).2.val=i := by
  change min i (C.count e-1)=i
  omega

theorem orderedArc_inj (C : DrawingPassages D) (e : BipartiteEdge m n) (i j : ℕ)
    (hi : i < C.count e) (hj : j < C.count e)
    (h : C.orderedArc e i=C.orderedArc e j) : i=j := by
  have hh := congrArg (fun p : C.ArcIndex => p.2.val) h
  simpa only [C.orderedArc_val e i hi,C.orderedArc_val e j hj] using hh

theorem orderedArc_first (C : DrawingPassages D) (e : BipartiteEdge m n) :
    C.orderedArc e 0=C.firstArc e := by
  simp [orderedArc,firstArc]

theorem orderedArc_last (C : DrawingPassages D) (e : BipartiteEdge m n) :
    C.orderedArc e (C.count e-1)=C.lastArc e := by
  simp [orderedArc,lastArc]

def orderedInner (C : DrawingPassages D) (e : BipartiteEdge m n) (j : ℕ)
    (hj : j+1 < C.count e) : C.InnerIndex :=
  ⟨e,⟨⟨j+1,by omega⟩,⟨Nat.succ_pos j,hj⟩⟩⟩

theorem orderedInner_incoming (C : DrawingPassages D) (e : BipartiteEdge m n)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.incomingArc (C.orderedInner e j hj)=C.orderedArc e j := by
  unfold incomingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1-1=min j (C.count e-1)
  omega

theorem orderedInner_outgoing (C : DrawingPassages D) (e : BipartiteEdge m n)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.outgoingArc (C.orderedInner e j hj)=C.orderedArc e (j+1) := by
  unfold outgoingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1=min (j+1) (C.count e-1)
  omega

theorem orderedInner_inj (C : DrawingPassages D) (e : BipartiteEdge m n) (i j : ℕ)
    (hi : i+1 < C.count e) (hj : j+1 < C.count e)
    (h : C.orderedInner e i hi=C.orderedInner e j hj) : i=j := by
  have hh : i+1=j+1 := congrArg (fun p : C.InnerIndex => p.2.val.val) h
  omega

end DrawingPassages
end Zarankiewicz

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
namespace DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

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
    (j : BipartiteVertex m n) :
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
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingCoordinates
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
-- module Solutions.OAIB3_Zar.Crossing_SegmentCrossingCoordinates
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
-- module Solutions.OAIB3_Zar.Crossing_ProperSegmentCrossing
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
-- module Solutions.OAIB3_Zar.Crossing_AssembledAdmissibleDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem crossingChord_meeting_proper (C : DrawingPassages D) (p q : C.InnerIndex)
    (hpq : p ≠ q) (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ C.crossingDisk p ∧
      ProperCrossing
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
  · apply properCrossing_openSegments _ _ _ _ x hd
    · exact ⟨s.val,hsi,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs⟩
    · exact ⟨t.val,hti,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht⟩

end DrawingPassages
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AxisSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def axisSegmentPoint (a b t : ℝ) : Plane := segmentPoint (0,a) (b,0) t

theorem axisSegmentPoint_coordinates (a b t : ℝ) : axisSegmentPoint a b t=(t*b,(1-t)*a) := by
  ext <;> simp [axisSegmentPoint,segmentPoint]

theorem axisSegmentPoint_injective (a b : ℝ) (hb : b ≠ 0) : Function.Injective (axisSegmentPoint a b) := by
  intro t u htu
  have hx := congrArg Prod.fst htu
  simp only [axisSegmentPoint_coordinates] at hx
  exact mul_right_cancel₀ hb hx

theorem axisSegmentPoint_interior_off_axes (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (axisSegmentPoint a b t).1 ≠ 0 ∧ (axisSegmentPoint a b t).2 ≠ 0 := by
  rw [axisSegmentPoint_coordinates]
  exact ⟨mul_ne_zero (ne_of_gt ht.1) hb,mul_ne_zero (ne_of_gt (sub_pos.mpr ht.2)) ha⟩

theorem axisSegmentPoint_same_vertical (a b d t u : ℝ) (ha : a ≠ 0)
    (ht : 0 < t) (h : axisSegmentPoint a b t=axisSegmentPoint a d u) : b=d := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [axisSegmentPoint_coordinates] at hx hy
  have htu : t=u := by have hh := mul_right_cancel₀ ha hy; linarith
  rw [← htu] at hx
  exact mul_left_cancel₀ (ne_of_gt ht) hx

theorem axisSegmentPoint_same_horizontal (a c b t u : ℝ) (hb : b ≠ 0)
    (ht : t < 1) (h : axisSegmentPoint a b t=axisSegmentPoint c b u) : a=c := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [axisSegmentPoint_coordinates] at hx hy
  have htu : t=u := mul_right_cancel₀ hb hx
  rw [← htu] at hy
  exact mul_left_cancel₀ (ne_of_gt (sub_pos.mpr ht)) hy

theorem axisSegmentPoint_meeting_det (a b c d t u : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : (a,b) ≠ (c,d)) (h : axisSegmentPoint a b t=axisSegmentPoint c d u) :
    det2 ((b,0)-(0,a)) ((d,0)-(0,c)) ≠ 0 := by
  intro hz
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [axisSegmentPoint_coordinates] at hx hy
  have hz' : a*d-b*c=0 := by
    dsimp [det2] at hz
    nlinarith [hz]
  have hac : (a-c)*b=0 := by linear_combination b*hy+a*hx+u*hz'
  have he : a=c := sub_eq_zero.mp ((mul_eq_zero.mp hac).resolve_right hb)
  have hbd : a*(d-b)=0 := by rw [← he] at hz'; nlinarith [hz']
  have he' : b=d := (sub_eq_zero.mp ((mul_eq_zero.mp hbd).resolve_left ha)).symm
  exact hne (Prod.ext he he')

theorem axisSegmentPoint_meeting_proper (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : (a,b) ≠ (c,d)) (x : Plane)
    (hx : x ∈ openSegmentTrace (0,a) (b,0)) (hy : x ∈ openSegmentTrace (0,c) (d,0)) :
    ProperCrossing (openSegmentTrace (0,a) (b,0)) (openSegmentTrace (0,c) (d,0)) x := by
  obtain ⟨t,ht,he⟩ := hx
  obtain ⟨u,hu,hf⟩ := hy
  have hmeet : axisSegmentPoint a b t=axisSegmentPoint c d u := he.trans hf.symm
  exact properCrossing_openSegments _ _ _ _ _ (axisSegmentPoint_meeting_det a b c d t u ha hb hne hmeet)
    ⟨t,ht,he⟩ ⟨u,hu,hf⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AxisContinuousDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def axisVertex (a : Fin m → ℝ) (b : Fin n → ℝ) : BipartiteVertex m n → Plane
  | .inl i => (0,a i)
  | .inr p => (b p,0)

theorem axisVertex_injective (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b) (ha : ∀ i, a i ≠ 0) :
    Function.Injective (axisVertex a b) := by
  rintro (i|p) (k|q) he
  · exact congrArg Sum.inl (hai (congrArg Prod.snd he))
  · exact False.elim (ha i (congrArg Prod.snd he))
  · exact False.elim (ha k (congrArg Prod.snd he).symm)
  · exact congrArg Sum.inr (hbi (congrArg Prod.fst he))

def axisContinuousDrawing (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) : ContinuousDrawing m n where
  vertex := axisVertex a b
  vertex_injective := axisVertex_injective a b hai hbi ha
  edge e := Path.segment (0,a e.1) (b e.2,0)
  edge_injective := by
    intro e t u he
    apply Subtype.ext
    apply axisSegmentPoint_injective (a e.1) (b e.2) (hb e.2)
    change AffineMap.lineMap (0,a e.1) (b e.2,0) t.val = AffineMap.lineMap (0,a e.1) (b e.2,0) u.val at he
    simpa only [AffineMap.lineMap_apply_module,axisSegmentPoint,segmentPoint] using he
  interior_avoids_vertices := by
    intro e t ht j he
    have hh := axisSegmentPoint_interior_off_axes (a e.1) (b e.2) t.val (ha e.1) (hb e.2) ⟨ht.1,ht.2⟩
    have hv : axisSegmentPoint (a e.1) (b e.2) t.val=axisVertex a b j := by
      change AffineMap.lineMap (0,a e.1) (b e.2,0) t.val = axisVertex a b j at he
      simpa only [AffineMap.lineMap_apply_module,axisSegmentPoint,segmentPoint] using he
    rcases j with i | p
    · exact hh.1 (congrArg Prod.fst hv)
    · exact hh.2 (congrArg Prod.snd hv)

theorem axisContinuousDrawing_interior (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e : BipartiteEdge m n) :
    edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e=openSegmentTrace (0,a e.1) (b e.2,0) := by
  ext x
  constructor
  · rintro ⟨t,ht,he⟩
    refine ⟨t.val,⟨ht.1,ht.2⟩,?_⟩
    change AffineMap.lineMap (0,a e.1) (b e.2,0) t.val = x at he
    simpa only [AffineMap.lineMap_apply_module,segmentPoint] using he
  · rintro ⟨t,ht,he⟩
    refine ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,⟨ht.1,ht.2⟩,?_⟩
    change AffineMap.lineMap (0,a e.1) (b e.2,0) t = x
    simpa only [AffineMap.lineMap_apply_module,segmentPoint] using he

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AxisFiniteCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem axis_open_intersection_subsingleton (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : (a,b) ≠ (c,d)) :
    (openSegmentTrace (0,a) (b,0) ∩ openSegmentTrace (0,c) (d,0)).Subsingleton := by
  rintro x ⟨⟨t,ht,he⟩,⟨u,hu,hf⟩⟩ y ⟨⟨t',ht',he'⟩,⟨u',hu',hf'⟩⟩
  have hmeet : axisSegmentPoint a b t=axisSegmentPoint c d u := he.trans hf.symm
  have hdet := axisSegmentPoint_meeting_det a b c d t u ha hb hne hmeet
  have hh := segment_intersection_parameters_unique (0,a) (b,0) (0,c) (d,0) hdet t u t' u'
    (he.trans hf.symm) (he'.trans hf'.symm)
  exact he.symm.trans ((congrArg (segmentPoint (0,a) (b,0)) hh.1).trans he')

theorem axis_intercept_pair_ne (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b) (e f : BipartiteEdge m n) (hef : e ≠ f) :
    (a e.1,b e.2) ≠ (a f.1,b f.2) := by
  intro he
  exact hef (Prod.ext (hai (congrArg Prod.fst he)) (hbi (congrArg Prod.snd he)))

theorem axisContinuousDrawing_pair_subsingleton (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e f : BipartiteEdge m n) (hef : e ≠ f) :
    (edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e ∩
      edgeInterior (axisContinuousDrawing a b hai hbi ha hb) f).Subsingleton := by
  rw [axisContinuousDrawing_interior,axisContinuousDrawing_interior]
  exact axis_open_intersection_subsingleton _ _ _ _ (ha e.1) (hb e.2) (axis_intercept_pair_ne a b hai hbi e f hef)

theorem axisContinuousDrawing_crossings_finite (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) :
    (crossingPoints (axisContinuousDrawing a b hai hbi ha hb)).Finite := by
  classical
  let D := axisContinuousDrawing a b hai hbi ha hb
  let S := fun e f : BipartiteEdge m n => if e=f then (∅ : Set Plane) else edgeInterior D e ∩ edgeInterior D f
  have hfinite (e f : BipartiteEdge m n) : (S e f).Finite := by
    dsimp only [S]
    split_ifs with hef
    · exact Set.finite_empty
    · exact (axisContinuousDrawing_pair_subsingleton a b hai hbi ha hb e f hef).finite
  apply (Set.finite_iUnion fun e => Set.finite_iUnion (hfinite e)).subset
  rintro x ⟨e,f,hef,hxe,hxf⟩
  refine Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨f,?_⟩⟩
  simpa only [S,ite_eq_right hef] using (show x ∈ edgeInterior D e ∩ edgeInterior D f from ⟨hxe,hxf⟩)

theorem axisContinuousDrawing_crossings_proper (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (x : Plane) (hx : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e)
    (hy : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) f) :
    ProperCrossing (edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e)
      (edgeInterior (axisContinuousDrawing a b hai hbi ha hb) f) x := by
  rw [axisContinuousDrawing_interior] at hx hy ⊢
  rw [axisContinuousDrawing_interior]
  exact axisSegmentPoint_meeting_proper _ _ _ _ (ha e.1) (hb e.2)
    (axis_intercept_pair_ne a b hai hbi e f hef) x hx hy

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AxisConcurrency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open MvPolynomial
variable {m n : ℕ}

def axisConcurrency (a b c d e f : ℝ) : ℝ :=
  a*d*e*f+b*c*d*e+a*b*c*f-a*b*d*e-b*c*e*f-a*c*d*f

theorem axisSegmentPoint_line_equation (a b t : ℝ) :
    a*(axisSegmentPoint a b t).1+b*(axisSegmentPoint a b t).2=a*b := by
  rw [axisSegmentPoint_coordinates]
  ring

theorem axisConcurrency_zero_of_meeting (a b c d e f : ℝ) (z : Plane)
    (h₀ : a*z.1+b*z.2=a*b) (h₁ : c*z.1+d*z.2=c*d) (h₂ : e*z.1+f*z.2=e*f) :
    axisConcurrency a b c d e f=0 := by
  unfold axisConcurrency
  linear_combination -(c*f-d*e)*h₀-(b*e-a*f)*h₁-(a*d-b*c)*h₂

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AxisGenericPositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def AxisIndependentTriple (e f g : BipartiteEdge m n) : Prop :=
  e.1 ≠ f.1 ∧ e.1 ≠ g.1 ∧ f.1 ≠ g.1 ∧ e.2 ≠ f.2 ∧ e.2 ≠ g.2 ∧ f.2 ≠ g.2

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AxisAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem axisContinuousDrawing_meeting_independent (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (x : Plane) (hx : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e)
    (hy : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) f) : e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  rw [axisContinuousDrawing_interior] at hx hy
  obtain ⟨t,ht,he⟩ := hx
  obtain ⟨u,hu,hf⟩ := hy
  have hmeet : axisSegmentPoint (a e.1) (b e.2) t=axisSegmentPoint (a f.1) (b f.2) u := he.trans hf.symm
  constructor
  · intro hfirst
    rw [hfirst] at hmeet
    have hh := axisSegmentPoint_same_vertical (a f.1) (b e.2) (b f.2) t u (ha f.1) ht.1 hmeet
    exact hef (Prod.ext hfirst (hbi hh))
  · intro hsecond
    rw [hsecond] at hmeet
    have hh := axisSegmentPoint_same_horizontal (a e.1) (a f.1) (b f.2) t u (hb f.2) ht.2 hmeet
    exact hef (Prod.ext (hai hh) hsecond)

theorem axisContinuousDrawing_line_equation (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e : BipartiteEdge m n) (x : Plane)
    (hx : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e) :
    a e.1*x.1+b e.2*x.2=a e.1*b e.2 := by
  rw [axisContinuousDrawing_interior] at hx
  obtain ⟨t,ht,he⟩ := hx
  rw [← he]
  exact axisSegmentPoint_line_equation _ _ _

def axisAdmissibleDrawing (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0)
    (hgeneric : ∀ e f g : BipartiteEdge m n, AxisIndependentTriple e f g →
      axisConcurrency (a e.1) (b e.2) (a f.1) (b f.2) (a g.1) (b g.2) ≠ 0) : AdmissibleDrawing m n where
  toContinuousDrawing := axisContinuousDrawing a b hai hbi ha hb
  crossings_finite := axisContinuousDrawing_crossings_finite a b hai hbi ha hb
  crossings_proper := axisContinuousDrawing_crossings_proper a b hai hbi ha hb
  no_triples := by
    intro e f g hef heg hfg
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨he,hf⟩,hg⟩
    have h₀ := axisContinuousDrawing_meeting_independent a b hai hbi ha hb e f hef x he hf
    have h₁ := axisContinuousDrawing_meeting_independent a b hai hbi ha hb e g heg x he hg
    have h₂ := axisContinuousDrawing_meeting_independent a b hai hbi ha hb f g hfg x hf hg
    exact hgeneric e f g ⟨h₀.1,h₁.1,h₂.1,h₀.2,h₁.2,h₂.2⟩
      (axisConcurrency_zero_of_meeting _ _ _ _ _ _ x
        (axisContinuousDrawing_line_equation a b hai hbi ha hb e x he)
        (axisContinuousDrawing_line_equation a b hai hbi ha hb f x hf)
        (axisContinuousDrawing_line_equation a b hai hbi ha hb g x hg))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BalancedAxisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def axisIntervalLo (r : ℕ) (i : Fin r) : ℝ := if i.val < r/2 then 2*(i.val : ℝ)+1 else -(2*(i.val : ℝ)+2)
def axisIntervalHi (r : ℕ) (i : Fin r) : ℝ := if i.val < r/2 then 2*(i.val : ℝ)+2 else -(2*(i.val : ℝ)+1)

theorem axisInterval_abs_bounds (r : ℕ) (i : Fin r) (x : ℝ)
    (hx : x ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) :
    2*(i.val : ℝ)+1 < |x| ∧ |x| < 2*(i.val : ℝ)+2 := by
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  by_cases h : i.val < r/2
  · simp only [axisIntervalLo,axisIntervalHi,ite_eq_left h,Set.mem_Ioo] at hx
    rw [abs_of_pos (by linarith [hx.1])]
    exact hx
  · simp only [axisIntervalLo,axisIntervalHi,ite_eq_right h,Set.mem_Ioo] at hx
    rw [abs_of_neg (by linarith [hx.2])]
    constructor <;> linarith [hx.1,hx.2]

theorem axisInterval_ne_zero (r : ℕ) (i : Fin r) (x : ℝ)
    (hx : x ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) : x ≠ 0 := by
  have hh := (axisInterval_abs_bounds r i x hx).1
  intro he
  rw [he,abs_zero] at hh
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  linarith

theorem axisInterval_abs_strictMono (r : ℕ) (x : Fin r → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) :
    StrictMono (fun i => |x i|) := by
  intro i k hik
  have hi := (axisInterval_abs_bounds r i (x i) (hx i)).2
  have hk := (axisInterval_abs_bounds r k (x k) (hx k)).1
  have hik' : (i.val : ℝ)+1 ≤ (k.val : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hik)
  linarith

theorem axisInterval_injective (r : ℕ) (x : Fin r → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) : Function.Injective x := by
  intro i k hik
  exact (axisInterval_abs_strictMono r x hx).injective (congrArg abs hik)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BalancedAxisDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

structure BalancedAxisRealization (m n : ℕ) where
  vertical : Fin m → ℝ
  horizontal : Fin n → ℝ
  vertical_interval : ∀ i, vertical i ∈ Set.Ioo (axisIntervalLo m i) (axisIntervalHi m i)
  horizontal_interval : ∀ p, horizontal p ∈ Set.Ioo (axisIntervalLo n p) (axisIntervalHi n p)
  generic : ∀ e f g : BipartiteEdge m n, AxisIndependentTriple e f g →
    axisConcurrency (vertical e.1) (horizontal e.2) (vertical f.1) (horizontal f.2)
      (vertical g.1) (horizontal g.2) ≠ 0

namespace BalancedAxisRealization
variable {m n : ℕ} (R : BalancedAxisRealization m n)

theorem vertical_injective : Function.Injective R.vertical := axisInterval_injective m _ R.vertical_interval
theorem horizontal_injective : Function.Injective R.horizontal := axisInterval_injective n _ R.horizontal_interval
theorem vertical_ne_zero (i : Fin m) : R.vertical i ≠ 0 := axisInterval_ne_zero m i _ (R.vertical_interval i)
theorem horizontal_ne_zero (p : Fin n) : R.horizontal p ≠ 0 := axisInterval_ne_zero n p _ (R.horizontal_interval p)

def drawing : AdmissibleDrawing m n :=
  axisAdmissibleDrawing R.vertical R.horizontal R.vertical_injective R.horizontal_injective
    R.vertical_ne_zero R.horizontal_ne_zero R.generic

end BalancedAxisRealization

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BalancedRayPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open scoped Finset

def positiveRayIndices (r : ℕ) : Finset (Fin r) := Finset.univ.filter (fun i => i.val < r/2)
def negativeRayIndices (r : ℕ) : Finset (Fin r) := Finset.univ.filter (fun i => ¬ i.val < r/2)

def balancedRayPairs (r : ℕ) : Finset (Fin r × Fin r) :=
  ((positiveRayIndices r ×ˢ positiveRayIndices r).filter (fun p => p.1 < p.2)) ∪
    ((negativeRayIndices r ×ˢ negativeRayIndices r).filter (fun p => p.1 < p.2))

end Zarankiewicz

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

def LocallyStraightAt (D : ContinuousDrawing m n) (e : BipartiteEdge m n) (x : Plane) : Prop :=
  ∃ a b : Plane, a ≠ b ∧ x ∈ openSegmentTrace a b ∧
    ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
      ∀ z ∈ U, z ∈ edgeInterior D e ↔ z ∈ openSegmentTrace a b

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

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectionVertexAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : AdmissibleDrawing m n}

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
    (hm : C.innerMark p=C.innerMark q) (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (i : Bool) (j : BipartiteVertex m n) :
    v j ∉ segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) := by
  intro hx
  have hn : C.innerMark p ≠ C.vertexMark j := by
    intro he
    exact crossing_not_vertex D.toFiniteIntersectionDrawing (C.innerMark p).val (C.innerMark_is_crossing p) j (congrArg Subtype.val he)
  exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
    (C.reconnection_segment_in_disk p q hm i hx) (hv j).le

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReplaceDrawingEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.ContinuousDrawing
variable {m n : ℕ}

def replaceTwoRoutes (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (g : BipartiteEdge m n) : Path (D.vertex (.inl g.1)) (D.vertex (.inr g.2)) := by
  classical
  exact if h : g=e then γ.cast (congrArg (fun k : BipartiteEdge m n => D.vertex (.inl k.1)) h)
    (congrArg (fun k : BipartiteEdge m n => D.vertex (.inr k.2)) h)
  else if h : g=f then δ.cast (congrArg (fun k : BipartiteEdge m n => D.vertex (.inl k.1)) h)
    (congrArg (fun k : BipartiteEdge m n => D.vertex (.inr k.2)) h)
  else D.edge g

theorem replaceTwoRoutes_first (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2))) :
    D.replaceTwoRoutes e f γ δ e=γ := by
  simp only [replaceTwoRoutes,dite_eq_left rfl,Path.cast_rfl_rfl]

theorem replaceTwoRoutes_second (D : ContinuousDrawing m n) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2))) :
    D.replaceTwoRoutes e f γ δ f=δ := by
  simp only [replaceTwoRoutes,dite_eq_right (Ne.symm hef),dite_eq_left rfl,Path.cast_rfl_rfl]

theorem replaceTwoRoutes_other (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (g : BipartiteEdge m n) (hge : g ≠ e) (hgf : g ≠ f) :
    D.replaceTwoRoutes e f γ δ g=D.edge g := by
  simp only [replaceTwoRoutes,dite_eq_right hge,dite_eq_right hgf]

def replaceTwoEdges (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hvγ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, γ t ≠ D.vertex j)
    (hvδ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, δ t ≠ D.vertex j) :
    ContinuousDrawing m n where
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

end Zarankiewicz.ContinuousDrawing

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReplaceDrawingRangeCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.ContinuousDrawing
variable {m n : ℕ}

theorem replaceTwoRoutes_range_cases (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (g : BipartiteEdge m n) (x : Plane) (hx : x ∈ Set.range (D.replaceTwoRoutes e f γ δ g)) :
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

end Zarankiewicz.ContinuousDrawing

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ReconnectionAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

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

theorem DrawingPassages.reconnection_avoids_chord_meeting {m n : ℕ} {D : AdmissibleDrawing m n}
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

def IncidentEdges (j : BipartiteVertex m n) :=
  {e : BipartiteEdge m n // j=Sum.inl e.1 ∨ j=Sum.inr e.2}

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

def Bounded (k : ℕ) (p : PolynomialModule ℝ W) : Prop :=
  ∀ n, k ≤ n → p.coeff n = 0

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CircleOffset
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
-- module Solutions.OAIB3_Zar.Crossing_EndpointFlagPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

abbrev IncidentFlag (m n : ℕ) := (j : BipartiteVertex m n) × IncidentEdges j

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

abbrev BiPoly := PolynomialModule ℝ (PolynomialModule ℝ ℝ)

def BiBounded (r s : ℕ) (p : BiPoly) : Prop :=
  Bounded r p ∧ ∀ a, Bounded s (p.coeff a)

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

abbrev BiExponent (s : ℕ) := Fin s × Fin s

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_BalancedAxisCrossingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.BalancedAxisRealization
open scoped BigOperators Finset
variable {m n : ℕ} (R : BalancedAxisRealization m n)

def crossingCandidates (_R : BalancedAxisRealization m n) : Finset ((Fin m × Fin m) × (Fin n × Fin n)) :=
  balancedRayPairs m ×ˢ balancedRayPairs n

def candidateCrossings (v : (Fin m × Fin m) × (Fin n × Fin n)) : Finset Plane :=
  pairCrossings R.drawing (v.1.1,v.2.2) (v.1.2,v.2.1)

end Zarankiewicz.BalancedAxisRealization

end

end OAI
end



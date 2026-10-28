-- Prove2me | Definitions.Def_OAIB3Zr001
-- name    : OAIB3Zr001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T13:11:27.795178+00:00
-- url     : https://prove2.me/theorems/1d203468-fc7a-402d-a345-d4228bace85d
-- title:
--   Definitions bundle OAIB3Zr001 of the split of OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 95 declarations of OpenAI's Lean: 61 definitions, 1 instance and 33 theorems. The definitions and types are `OAI.Zarankiewicz.NoAdjacentCrossings`, `OAI.Zarankiewicz.OrderedNode`, `OAI.Zarankiewicz.OrderedPathPart`, `OAI.Zarankiewicz.SegmentReach`, `OAI.Zarankiewicz.TriangleIndex`, `OAI.Zarankiewicz.alternatingPath`, `OAI.Zarankiewicz.axisConcurrencyPolynomial`, `OAI.Zarankiewicz.backwardBipartiteDart`, `OAI.Zarankiewicz.bipartiteDartEdge`, `OAI.Zarankiewicz.bipartiteDartSign`, `OAI.Zarankiewicz.blockRectangle`, `OAI.Zarankiewicz.chordEndpointPairing`, `OAI.Zarankiewicz.completeBipartite`, `OAI.Zarankiewicz.cyclicIndex`, `OAI.Zarankiewicz.cyclicWalkDart`, `OAI.Zarankiewicz.deleteRightVertex`, `OAI.Zarankiewicz.derivativeAtNode`, `OAI.Zarankiewicz.detectorWeight`, `OAI.Zarankiewicz.edgeBlock`, `OAI.Zarankiewicz.edgePairing`, `OAI.Zarankiewicz.extendOrderedNode`, `OAI.Zarankiewicz.forwardBipartiteDart`, `OAI.Zarankiewicz.fourCycleWalk`, `OAI.Zarankiewicz.graphKernelEquiv`, `OAI.Zarankiewicz.graphSequenceWalk`, `OAI.Zarankiewicz.halfOrderMatrix`, `OAI.Zarankiewicz.intervalLeft`, `OAI.Zarankiewicz.intervalRight`, `OAI.Zarankiewicz.lowerTriangle`, `OAI.Zarankiewicz.mulRoot`, `OAI.Zarankiewicz.mulRootLinear`, `OAI.Zarankiewicz.nodePolynomial`, `OAI.Zarankiewicz.offDiagonalRankSum`, `OAI.Zarankiewicz.orderSign`, `OAI.Zarankiewicz.orderedTriangle`, `OAI.Zarankiewicz.orientedEdgeStep`, `OAI.Zarankiewicz.parameterNeighborhood`, `OAI.Zarankiewicz.polygonalArcPath`, `OAI.Zarankiewicz.polynomialColumnMatrix`, `OAI.Zarankiewicz.polynomialLinearMatrix` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Crossing_AffinePathHalves`, `Crossing_AffineSideEvents`, `Crossing_AlternatingPaths`, `Crossing_AxisConcurrency`, `Crossing_BipartiteDartGeometry`, `Crossing_ChordPairing`, `Crossing_CyclicWalkDarts`, `Crossing_DetectorRelabeling`, `Crossing_DrawingDeletion`, `Crossing_DrawingRangeCrossings`, `Crossing_DrawingRestriction`, `Crossing_FourCyclePairing`, `Crossing_FourCycles`, `Crossing_GraphSequenceWalk`, `Crossing_GraphWalkTrace`, `Crossing_HalfOrderReduction`, `Crossing_Interpolation`, `Crossing_MatrixGraphs`, `Crossing_MatrixRankSum`, `Crossing_NodeMoments`, `Crossing_OrderedNodeIndices`, `Crossing_OrderedPathParts`, `Crossing_ParameterNeighborhoods`, `Crossing_PathConcatenationInjective`, `Crossing_PeriodicPolygon`, `Crossing_PolygonalChainExistence`, `Crossing_PolygonalChains`, `Crossing_PolygonalReach`, `Crossing_PolynomialCoordinates`, `Crossing_PolynomialKernel`, `Crossing_PolynomialLinearMatrix`, `Crossing_ProperCrossingLocality`, `Crossing_RankDetector`, `Crossing_RectangleAlgebra`, `Crossing_RowCrossingCount`, `Crossing_StepEvents`, `Crossing_TwoTriangleBasis`, `Crossing_TwoTriangleIndices`, `Crossing_UniqueWalkPassage`.
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
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AffinePathHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def intervalLeft (t : unitInterval) : unitInterval := ⟨t.val/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
def intervalRight (t : unitInterval) : unitInterval := ⟨(1+t.val)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_StepEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def stepAt (root before after t : ℝ) : ℝ := if t < root then before else after

def stepEvent {n : ℕ} (r lo hi : Fin n → ℝ) (i : Fin n) : ℝ :=
  if 0 < r i ∧ r i < 1 then
    (hi i-lo i) * ∏ j, if j=i then 1 else stepAt (r j) (lo j) (hi j) (r i)
  else 0

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AffineSideEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def positiveIndicator (x : ℝ) : ℝ := if 0 < x then 1 else 0

def slopeSign (b : ℝ) : ℝ := if 0 < b then 1 else -1

def sideBefore (b : ℝ) : ℝ := if 0 < b then 0 else 1

def sideAfter (b : ℝ) : ℝ := if 0 < b then 1 else 0

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalReach
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
-- module Solutions.OAIB3_Zar.Crossing_PolygonalChains
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

end Zarankiewicz

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
-- module Solutions.OAIB3_Zar.Crossing_AlternatingPaths
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

def axisConcurrencyPolynomial (e f g : BipartiteEdge m n) : MvPolynomial (BipartiteVertex m n) ℝ :=
  let a := X (Sum.inl e.1); let b := X (Sum.inr e.2)
  let c := X (Sum.inl f.1); let d := X (Sum.inr f.2)
  let u := X (Sum.inl g.1); let v := X (Sum.inr g.2)
  a*d*u*v+b*c*d*u+a*b*c*v-a*b*d*u-b*c*u*v-a*c*d*v

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PeriodicPolygon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def cyclicIndex (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i%n,Nat.mod_lt i hn⟩

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

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_UniqueWalkPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem walk_dart_parameters {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (d : G.Dart) (hd : d ∈ p.darts) :
    ∃ i : ℕ, i < p.length ∧ d.fst=p.getVert i ∧ d.snd=p.getVert (i+1) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hd
  have he := SimpleGraph.Walk.darts_getElem_eq_getVert (p:=p) i.val i.isLt
  have hd' := hi.symm.trans he
  refine ⟨i.val,by simpa only [p.length_darts] using i.isLt,?_,?_⟩
  · exact congrArg (fun r : G.Dart => r.fst) hd'
  · exact congrArg (fun r : G.Dart => r.snd) hd'

end Zarankiewicz

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

theorem walk_dart_at {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (i : ℕ) (hi : i < p.length) :
    ∃ d : G.Dart, d ∈ p.darts ∧ d.fst=p.getVert i ∧ d.snd=p.getVert (i+1) := by
  have hi' : i < p.darts.length := by simpa only [p.length_darts] using hi
  refine ⟨p.darts[i],List.getElem_mem hi',?_,?_⟩
  · rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
  · rw [SimpleGraph.Walk.darts_getElem_eq_getVert]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ParameterNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

def parameterNeighborhood (t : unitInterval) (δ : ℝ) : Set unitInterval :=
  {s | |s.val-t.val| < δ}

end Zarankiewicz

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

def graphSequenceWalk {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (∀ i, i < k → G.Adj (v i) (v (i+1))) → G.Walk (v 0) (v k)
  | 0, _ => .nil
  | k+1, h => (graphSequenceWalk G v k (fun i hi => h i (by omega))).concat (h k (by omega))

theorem graphSequenceWalk_length {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (h : ∀ i, i < k → G.Adj (v i) (v (i+1))) → (graphSequenceWalk G v k h).length=k
  | 0, _ => rfl
  | k+1, h => by rw [graphSequenceWalk,SimpleGraph.Walk.length_concat,graphSequenceWalk_length]

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ProperCrossingLocality
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
-- module Solutions.OAIB3_Zar.Crossing_OrderedPathParts
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
-- module Solutions.OAIB3_Zar.Crossing_ChordPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def orderSign (a b : ℝ) : ℝ := if a < b then 1 else if b < a then -1 else 0

def chordEndpointPairing (a b c d : ℝ) : ℝ :=
  (orderSign a c-orderSign a d-orderSign b c+orderSign b d)/2

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingRangeCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem edgeInterior_subset_range (D : ContinuousDrawing m n) (e : BipartiteEdge m n) :
    edgeInterior D e ⊆ Set.range (D.edge e) := by
  rintro x ⟨t,_,he⟩
  exact ⟨t,he⟩

theorem edgeInterior_of_range_not_vertices (D : ContinuousDrawing m n) (e : BipartiteEdge m n)
    (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hvertex : ∀ j, x ≠ D.vertex j) :
    x ∈ edgeInterior D e := by
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

theorem edgeInterior_not_vertex (D : ContinuousDrawing m n) (e : BipartiteEdge m n)
    (x : Plane) (hx : x ∈ edgeInterior D e) (j : BipartiteVertex m n) : x ≠ D.vertex j := by
  obtain ⟨t,ht,he⟩ := hx
  exact fun hj => D.interior_avoids_vertices e t ht j (he.trans hj)

theorem crossing_of_ranges_not_vertices (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (hef : e ≠ f) (x : Plane) (he : x ∈ Set.range (D.edge e)) (hf : x ∈ Set.range (D.edge f))
    (hv : ∀ j, x ≠ D.vertex j) : x ∈ crossingPoints D :=
  ⟨e,f,hef,edgeInterior_of_range_not_vertices D e x he hv,edgeInterior_of_range_not_vertices D f x hf hv⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RowCrossingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

def NoAdjacentCrossings (D : AdmissibleDrawing m n) : Prop :=
  ∀ e f : BipartiteEdge m n, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) →
    edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f = ∅

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FourCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open SimpleGraph
open scoped BigOperators

abbrev completeBipartite (m n : ℕ) := completeBipartiteGraph (Fin m) (Fin n)

def orientedEdgeStep {m n : ℕ} (u v : Fin m ⊕ Fin n) : Fin m × Fin n → ℝ :=
  match u,v with
  | .inl i, .inr p => Pi.single (i,p) 1
  | .inr p, .inl i => -Pi.single (i,p) 1
  | _, _ => 0

def walkEdgeChain {m n : ℕ} {u v : Fin m ⊕ Fin n} :
    (completeBipartite m n).Walk u v → (Fin m × Fin n → ℝ)
  | .nil => 0
  | @Walk.cons _ _ _ w _ _ rest => orientedEdgeStep u w + walkEdgeChain rest

def fourCycleWalk {m n : ℕ} (i i₀ : Fin m) (p p₀ : Fin n) :
    (completeBipartite m n).Walk (.inl i) (.inl i) :=
  .cons (v := .inr p) (by simp [completeBipartite, completeBipartiteGraph])
    (.cons (v := .inl i₀) (by simp [completeBipartite, completeBipartiteGraph])
      (.cons (v := .inr p₀) (by simp [completeBipartite, completeBipartiteGraph])
        (.cons (v := .inl i) (by simp [completeBipartite, completeBipartiteGraph]) .nil)))

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

def forwardBipartiteDart (e : BipartiteEdge m n) : (completeBipartite m n).Dart :=
  ⟨(Sum.inl e.1,Sum.inr e.2),by simp [completeBipartite,completeBipartiteGraph]⟩

def backwardBipartiteDart (e : BipartiteEdge m n) : (completeBipartite m n).Dart :=
  (forwardBipartiteDart e).symm

def bipartiteDartEdge (d : (completeBipartite m n).Dart) : BipartiteEdge m n := by
  rcases d with ⟨⟨u,v⟩,h⟩
  rcases u with i | p <;> rcases v with k | q
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)
  · exact (i,q)
  · exact (k,p)
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)

def bipartiteDartSign (d : (completeBipartite m n).Dart) : ℝ :=
  match d.fst with
  | .inl _ => 1
  | .inr _ => -1

theorem bipartiteDart_cases (d : (completeBipartite m n).Dart) :
    (∃ e, d=forwardBipartiteDart e) ∨ (∃ e, d=backwardBipartiteDart e) := by
  rcases d with ⟨⟨u,v⟩,h⟩
  rcases u with i | p <;> rcases v with k | q
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)
  · exact Or.inl ⟨(i,q),rfl⟩
  · exact Or.inr ⟨(k,p),rfl⟩
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)

theorem bipartiteDart_source_incident (d : (completeBipartite m n).Dart) :
    d.fst=Sum.inl (bipartiteDartEdge d).1 ∨ d.fst=Sum.inr (bipartiteDartEdge d).2 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem bipartiteDart_target_incident (d : (completeBipartite m n).Dart) :
    d.snd=Sum.inl (bipartiteDartEdge d).1 ∨ d.snd=Sum.inr (bipartiteDartEdge d).2 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CyclicWalkDarts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open SimpleGraph
variable {m n : ℕ} {u v : BipartiteVertex m n}

def walkDart (p : (completeBipartite m n).Walk u v) (i : Fin p.length) :
    (completeBipartite m n).Dart :=
  ⟨(p.getVert i.val,p.getVert (i.val+1)),p.adj_getVert_succ i.isLt⟩

def cyclicWalkDart (p : (completeBipartite m n).Walk u u) (hp : 0 < p.length) (i : ℕ) :
    (completeBipartite m n).Dart := walkDart p (cyclicIndex p.length hp i)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_NodeMoments
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

def mulRoot (t : ℝ) (p : PolynomialModule ℝ W) : PolynomialModule ℝ W :=
  (Polynomial.X - Polynomial.C t) • p

theorem mulRoot_coeff_succ (t : ℝ) (p : PolynomialModule ℝ W) (n : ℕ) :
    (mulRoot t p).coeff (n+1) = p.coeff n - t • p.coeff (n+1) := by
  unfold mulRoot
  rw [sub_smul]
  change (((Polynomial.X : Polynomial ℝ) • p).coeff (n+1) -
    (Polynomial.C t • p).coeff (n+1)) = _
  simp [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left]

theorem eval_mulRoot (t u : ℝ) (p : PolynomialModule ℝ W) :
    eval u (mulRoot t p) = (u-t) • eval u p := by
  simp [mulRoot]

def mulRootLinear (t : ℝ) : PolynomialModule ℝ W →ₗ[ℝ] PolynomialModule ℝ W where
  toFun := mulRoot t
  map_add' _ _ := smul_add _ _ _
  map_smul' c p := smul_comm _ c p

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

variable [Fintype ι]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

def vectorInterpolant (z : ∀ i, ↥(U i ⊓ Z)) : PolynomialModule ℝ Z :=
  by
    classical
    exact ∑ i, Lagrange.basis Finset.univ node i • single ℝ 0 ⟨(z i).val, (z i).property.2⟩

theorem eval_vectorInterpolant (hn : Function.Injective node) (z : ∀ i, ↥(U i ⊓ Z)) (i : ι) :
    eval (node i) (vectorInterpolant U node Z z) = ⟨(z i).val, (z i).property.2⟩ := by
  classical
  simp only [vectorInterpolant, map_sum, eval_smul, eval_single, pow_zero, one_smul]
  rw [Finset.sum_eq_single i]
  · rw [Lagrange.eval_basis_self hn.injOn (Finset.mem_univ i), one_smul]
  · intro j hj hji
    rw [Lagrange.eval_basis_of_ne hji (Finset.mem_univ i), zero_smul]
  · simp

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TwoTriangleIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open Finset

def lowerTriangle (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (s+1)) ×ˢ (Icc 1 (s+1))).filter (fun z => z.2 < z.1)

def upperTriangle (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc (s+2) (2*s+1)) ×ˢ (Icc (s+2) (2*s+1))).filter (fun z => z.1 < z.2)

def twoTriangle (s : ℕ) : Finset (ℕ × ℕ) := lowerTriangle s ∪ upperTriangle s

theorem mem_lowerTriangle (s p q : ℕ) :
    (p,q) ∈ lowerTriangle s ↔ 1 ≤ q ∧ q < p ∧ p ≤ s+1 := by
  simp only [lowerTriangle, mem_filter, mem_product, mem_Icc]
  omega

theorem mem_upperTriangle (s p q : ℕ) :
    (p,q) ∈ upperTriangle s ↔ s+1 < p ∧ p < q ∧ q ≤ 2*s+1 := by
  simp only [upperTriangle, mem_filter, mem_product, mem_Icc]
  omega

theorem mem_twoTriangle (s p q : ℕ) :
    (p,q) ∈ twoTriangle s ↔
      (1 ≤ q ∧ q < p ∧ p ≤ s+1) ∨ (s+1 < p ∧ p < q ∧ q ≤ 2*s+1) := by
  rw [twoTriangle, mem_union, mem_lowerTriangle, mem_upperTriangle]

theorem disjoint_triangles (s : ℕ) : Disjoint (lowerTriangle s) (upperTriangle s) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨p,q⟩ hp hq
  rw [mem_lowerTriangle] at hp
  rw [mem_upperTriangle] at hq
  omega

theorem card_lowerTriangle (s : ℕ) : (lowerTriangle s).card = (s+1).choose 2 := by
  have hswap : (lowerTriangle s).card =
      (((Icc 1 (s+1)) ×ˢ (Icc 1 (s+1))).filter (fun z => z.1 < z.2)).card :=
    Finset.card_equiv (Equiv.prodComm ℕ ℕ) (by
      intro z
      simp [lowerTriangle, and_comm, and_left_comm, and_assoc])
  rw [hswap, Finset.card_product_filter_lt]
  simp

theorem card_upperTriangle (s : ℕ) : (upperTriangle s).card = s.choose 2 := by
  have h := Finset.card_product_filter_lt (s := Icc (s+2) (2*s+1))
  have hc : (Icc (s+2) (2*s+1)).card = s := by simp; omega
  simpa [upperTriangle, hc] using h

theorem adjacent_choose_two (s : ℕ) : (s+1).choose 2 + s.choose 2 = s*s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ha : (s+2).choose 2 = (s+1).choose 2 + (s+1) := by
      calc
        (s+2).choose 2 = (s+1).choose 1 + (s+1).choose 2 := Nat.choose_succ_succ (s+1) 1
        _ = (s+1).choose 2 + (s+1) := by rw [Nat.choose_one_right]; omega
    have hb : (s+1).choose 2 = s.choose 2 + s := by
      simpa [Nat.choose_one_right, Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.choose_succ_succ s 1)
    have : s+1+1 = s+2 := by omega
    rw [this, ha]
    nlinarith

theorem card_twoTriangle (s : ℕ) : (twoTriangle s).card = s*s := by
  rw [twoTriangle, card_union_of_disjoint (disjoint_triangles s), card_lowerTriangle,
    card_upperTriangle, adjacent_choose_two]

def triangleRelabel (s k : ℕ) : ℕ := if k ≤ s then s+1+k else k-s+1

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TwoTriangleBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators

abbrev TriangleIndex (s : ℕ) := ↥(twoTriangle s)

end Zarankiewicz

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

def detectorWeight (node : ι → ℝ) (p q : ι) : ℝ :=
  (node p-node q) / (derivativeAtNode node p * derivativeAtNode node q)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DetectorRelabeling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def halfOrderMatrix (α : Type*) [LinearOrder α] : Matrix α α ℝ :=
  fun p q => if p < q then (1/2 : ℝ) else if q < p then -1/2 else 0

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n k : ℕ}

def restrictEdge (f : Fin k ↪ Fin n) : BipartiteEdge m k ↪ BipartiteEdge m n :=
  Function.Embedding.prodMap (Function.Embedding.refl (Fin m)) f

def restrictContinuousDrawing (D : ContinuousDrawing m n) (f : Fin k ↪ Fin n) :
    ContinuousDrawing m k where
  vertex := D.vertex ∘ Sum.map id f
  vertex_injective := D.vertex_injective.comp (Sum.map_injective.mpr ⟨Function.injective_id, f.injective⟩)
  edge e := D.edge (restrictEdge f e)
  edge_injective e := D.edge_injective (restrictEdge f e)
  interior_avoids_vertices e t ht v := D.interior_avoids_vertices (restrictEdge f e) t ht (Sum.map id f v)

theorem restrict_crossingPoints_subset (D : ContinuousDrawing m n) (f : Fin k ↪ Fin n) :
    crossingPoints (restrictContinuousDrawing D f) ⊆ crossingPoints D := by
  rintro x ⟨e,g,heg,he,hg⟩
  exact ⟨restrictEdge f e, restrictEdge f g, (restrictEdge f).injective.ne heg, he, hg⟩

def restrictDrawing (D : AdmissibleDrawing m n) (f : Fin k ↪ Fin n) : AdmissibleDrawing m k where
  toContinuousDrawing := restrictContinuousDrawing D.toContinuousDrawing f
  crossings_finite := D.crossings_finite.subset (restrict_crossingPoints_subset D.toContinuousDrawing f)
  crossings_proper e g heg x he hg :=
    D.crossings_proper (restrictEdge f e) (restrictEdge f g) ((restrictEdge f).injective.ne heg) x he hg
  no_triples e g h heg heh hgh :=
    D.no_triples (restrictEdge f e) (restrictEdge f g) (restrictEdge f h)
      ((restrictEdge f).injective.ne heg) ((restrictEdge f).injective.ne heh) ((restrictEdge f).injective.ne hgh)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

def deleteRightVertex (D : AdmissibleDrawing m (n+1)) (v : Fin (n+1)) : AdmissibleDrawing m n :=
  restrictDrawing D (Fin.succAboveOrderEmb v).toEmbedding

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RectangleAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def edgePairing (J : Matrix ι ι ℝ) (z y : ι → ℝ) : ℝ :=
  ∑ e, ∑ f, z e * J e f * y f

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FourCyclePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def edgeBlock {m n : ℕ} (J : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ)
    (i k : Fin m) : Matrix (Fin n) (Fin n) ℝ := fun p q => J (i,p) (k,q)

def blockRectangle {m n : ℕ} (J : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ)
    (i k i₀ : Fin m) : Matrix (Fin n) (Fin n) ℝ :=
  edgeBlock J i k - edgeBlock J i i₀ - edgeBlock J i₀ k + edgeBlock J i₀ i₀

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OrderedNodeIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

abbrev OrderedNode (s : ℕ) := ↥(Finset.Icc 1 (2*s+1))

@[simp] theorem card_orderedNode (s : ℕ) : Fintype.card (OrderedNode s) = 2*s+1 := by
  simp [OrderedNode, Nat.card_Icc]

def extendOrderedNode (s : ℕ) (node : OrderedNode s → ℝ) (i : ℕ) : ℝ :=
  if hi : i ∈ Finset.Icc 1 (2*s+1) then node ⟨i,hi⟩ else 0

@[simp] theorem extendOrderedNode_apply (s : ℕ) (node : OrderedNode s → ℝ) (i : OrderedNode s) :
    extendOrderedNode s node i.val = node i := by
  simp [extendOrderedNode, i.property]

theorem triangle_nodes_mem {s p q : ℕ} (h : (p,q) ∈ twoTriangle s) :
    p ∈ Finset.Icc 1 (2*s+1) ∧ q ∈ Finset.Icc 1 (2*s+1) := by
  rw [mem_twoTriangle] at h
  simp only [Finset.mem_Icc]
  omega

def triangleNodePair (s : ℕ) (pq : TriangleIndex s) : OrderedNode s × OrderedNode s :=
  (⟨pq.val.1, (triangle_nodes_mem pq.property).1⟩,
    ⟨pq.val.2, (triangle_nodes_mem pq.property).2⟩)

def orderedTriangle (s : ℕ) : Finset (OrderedNode s × OrderedNode s) :=
  Finset.univ.filter (fun pq => (pq.1.val,pq.2.val) ∈ twoTriangle s)

def triangleNodeEquiv (s : ℕ) : TriangleIndex s ≃ ↥(orderedTriangle s) where
  toFun pq := ⟨triangleNodePair s pq, by simp [orderedTriangle, triangleNodePair, pq.property]⟩
  invFun pq := ⟨(pq.val.1.val,pq.val.2.val), by simpa [orderedTriangle] using pq.property⟩
  left_inv pq := rfl
  right_inv pq := rfl

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_HalfOrderReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

variable {ι : Type*}

def strictLowerMatrix (α : Type*) [LinearOrder α] : Matrix α α ℝ :=
  fun p q => if q < p then 1 else 0

def triangleCoefficient (s : ℕ) (p q : OrderedNode s) : ℝ :=
  if p.val ≤ s+1 then (if q < p then 1 else 0) else (if p < q then -1 else 0)

def rowCut (s : ℕ) (p : OrderedNode s) : ℝ := if s+1 < p.val then 1 else 0

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MatrixGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def graphKernelEquiv (f g : V →ₗ[ℝ] W) :
    LinearMap.ker (f-g) ≃ₗ[ℝ] ↥(f.graph ⊓ g.graph) where
  toFun v := ⟨(v.val, f v.val), rfl, (sub_eq_zero.mp v.property)⟩
  invFun z := ⟨z.val.1, by
    change f z.val.1 - g z.val.1 = 0
    rw [← z.property.1, ← z.property.2, sub_self]⟩
  left_inv v := Subtype.ext rfl
  right_inv z := Subtype.ext (Prod.ext rfl z.property.1.symm)
  map_add' v w := Subtype.ext (Prod.ext rfl (f.map_add v.val w.val))
  map_smul' c v := Subtype.ext (Prod.ext rfl (f.map_smul c v.val))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialCoordinates
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

def scalarPolynomial (f : W →ₗ[ℝ] ℝ) : PolynomialModule ℝ W →ₗ[ℝ] Polynomial ℝ :=
  equivPolynomial.toLinearMap.comp (PolynomialModule.map ℝ f)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def polynomialColumnMatrix (b : Module.Basis ι ℝ W) (p : κ → PolynomialModule ℝ W) :
    Matrix ι κ (Polynomial ℝ) := fun i j => scalarPolynomial (b.coord i) (p j)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialLinearMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module
variable {V W ι κ : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable [Fintype ι] [Fintype κ] [DecidableEq κ]

def polynomialLinearMatrix (bV : Basis κ ℝ V) (bW : Basis ι ℝ W)
    (F : V →ₗ[ℝ] PolynomialModule ℝ W) : Matrix ι κ (Polynomial ℝ) :=
  polynomialColumnMatrix bW (fun j => F (bV j))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MatrixRankSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
open scoped BigOperators

def offDiagonalRankSum (m d : ℕ)
    (X Y : Fin m → Matrix (Fin d) (Fin d) ℝ) : ℕ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (X i-Y j).rank

end Zarankiewicz

end

end OAI
end



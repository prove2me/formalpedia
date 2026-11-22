-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionArm
-- name    : VehicleRoutingSurvey_RuralPostman1979_ContractionArm
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T16:15:16.107445+00:00
-- url     : https://prove2.me/theorems/a732fdc1-ad7e-486b-943b-781ee6857f77
-- title:
--   Rural postman algorithm — contraction stage interface
-- statement:
--   The type definitions specify the traced forest, the pre-contraction dual snapshot, and the registered blossom structure used in the contraction proof.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionStructure

/-! matching/WeightedCertificate.lean -/
section RppSource_WeightedCertificate
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





theorem matchingCrossesCut_mk_iff {n : ℕ} (S : Finset (Fin n)) {u v : Fin n}
    (distinct : u ≠ v) : MatchingCrossesCut S s(u, v) ↔
      (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
    simp [MatchingCrossesCut, Sym2.mk_isDiag_iff, Sym2.toFinset_mk_eq, Finset.filter_insert,
      Finset.filter_singleton, hu, hv, distinct]











end VehicleRoutingSurvey.Routing
end RppSource_WeightedCertificate

/-! matching/WeightedDualStep.lean -/
section RppSource_WeightedDualStep
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





















theorem oddCutDualEdgeValue_shift {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential direction : Fin n → ℝ) (cutDual cutDirection : Finset (Fin n) → ℝ)
    (δ : ℝ) (e : Sym2 (Fin n)) :
    oddCutDualEdgeValue cuts (fun v => potential v + δ * direction v)
      (fun S => cutDual S + δ * cutDirection S) e =
    oddCutDualEdgeValue cuts potential cutDual e + δ * oddCutDualEdgeValue cuts direction cutDirection e := by
  simp only [oddCutDualEdgeValue, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  abel









end VehicleRoutingSurvey.Routing
end RppSource_WeightedDualStep

/-! matching/WeightedForestSlope.lean -/
section RppSource_WeightedForestSlope
namespace VehicleRoutingSurvey.Routing







private theorem forest_crossing_blocks {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    {u v : Fin n} (hu : u ∈ O) (hv : v ∈ O) (distinct : u ≠ v) :
    (O.image blocks.block).filter (MatchingCrossesCut · s(u, v)) =
      if blocks.block u = blocks.block v then ∅ else {blocks.block u, blocks.block v} := by
  by_cases same : blocks.block u = blocks.block v
  · rw [if_pos same]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨top, cross⟩ := Finset.mem_filter.mp hS
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
    rcases (matchingCrossesCut_mk_iff _ distinct).mp cross with ⟨inU, outV⟩ | ⟨inV, outU⟩
    · exact outV ((same.symm.trans (blocks.same_of_mem hw inU)) ▸ blocks.self_mem v hv)
    · exact outU ((same.trans (blocks.same_of_mem hw inV)) ▸ blocks.self_mem u hu)
  · rw [if_neg same]
    ext S
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      matchingCrossesCut_mk_iff _ distinct]
    constructor
    · rintro ⟨top, ⟨inU, _⟩ | ⟨inV, _⟩⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
        exact Or.inl (blocks.same_of_mem hw inU).symm
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
        exact Or.inr (blocks.same_of_mem hw inV).symm
    · rintro (rfl | rfl)
      · exact ⟨Finset.mem_image_of_mem _ hu, Or.inl ⟨blocks.self_mem u hu, fun bad =>
          same (blocks.same_of_mem hu bad).symm⟩⟩
      · exact ⟨Finset.mem_image_of_mem _ hv, Or.inr ⟨blocks.self_mem v hv, fun bad =>
          same (blocks.same_of_mem hv bad)⟩⟩

/-- The dual slope of an edge is zero within a block. Across blocks it is the sum of their
two labels, so checking one edge does not require scanning the current cut variables. -/
theorem forest_edge_slope {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (label : Finset (Fin n) → ℝ)
    {u v : Fin n} (hu : u ∈ O) (hv : v ∈ O) (distinct : u ≠ v) :
    oddCutDualEdgeValue cuts (forestVertexDirection blocks label) (forestCutDirection blocks label)
      s(u, v) = if blocks.block u = blocks.block v then 0 else label (blocks.block u) + label (blocks.block v) := by
  have supportEq : (cuts.filter (MatchingCrossesCut · s(u, v))).filter
      (fun S => S ∈ O.image blocks.block ∧ S.card ≠ 1) =
      ((O.image blocks.block).filter (MatchingCrossesCut · s(u, v))).filter (fun S => S.card ≠ 1) := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, cross⟩, top, notOne⟩
      exact ⟨⟨top, cross⟩, notOne⟩
    · rintro ⟨⟨top, cross⟩, notOne⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
      exact ⟨⟨blocks.cut_mem hw notOne, cross⟩, top, notOne⟩
  have sumEq : (∑ S ∈ cuts.filter (MatchingCrossesCut · s(u, v)), forestCutDirection blocks label S) =
      ∑ S ∈ ((O.image blocks.block).filter (MatchingCrossesCut · s(u, v))).filter (fun S => S.card ≠ 1),
        label S := by
    calc
      _ = ∑ S ∈ (cuts.filter (MatchingCrossesCut · s(u, v))).filter
          (fun S => S ∈ O.image blocks.block ∧ S.card ≠ 1), label S :=
        (Finset.sum_filter _ _).symm
      _ = _ := congrArg (fun sets => ∑ S ∈ sets, label S) supportEq
  unfold oddCutDualEdgeValue forestVertexDirection
  rw [sumEq, forest_crossing_blocks blocks hu hv distinct, Sym2.toFinset_mk_eq]
  by_cases same : blocks.block u = blocks.block v
  · have vNotOne : (blocks.block v).card ≠ 1 := by
      intro one
      obtain ⟨w, singleton⟩ := Finset.card_eq_one.mp one
      have uIn : u ∈ blocks.block v := same ▸ blocks.self_mem u hu
      have vIn := blocks.self_mem v hv
      rw [singleton] at uIn vIn
      exact distinct ((Finset.mem_singleton.mp uIn).trans (Finset.mem_singleton.mp vIn).symm)
    simp [same, vNotOne, Finset.sum_insert, distinct]
  · by_cases uOne : (blocks.block u).card = 1 <;> by_cases vOne : (blocks.block v).card = 1 <;>
      simp [same, uOne, vOne, distinct, Finset.sum_insert, Finset.filter_insert,
        Finset.filter_singleton, add_comm]

end VehicleRoutingSurvey.Routing
end RppSource_WeightedForestSlope

/-! matching/MatchingPartitionView.lean -/
section RppSource_MatchingPartitionView
namespace VehicleRoutingSurvey.Routing













theorem CompactMatchingPartition.representativeOf_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (positive : 0 < k)
    (v : Fin k) : part.representativeOf positive (part.blocks.block v) = part.representative v := by
  have members : (part.blocks.block v).Nonempty := ⟨v, part.blocks.self_mem v (Finset.mem_univ v)⟩
  rw [CompactMatchingPartition.representativeOf, dif_pos members]
  exact part.constant _ _ (part.blocks.same_of_mem (Finset.mem_univ v) members.choose_spec)




end VehicleRoutingSurvey.Routing
end RppSource_MatchingPartitionView

/-! matching/CompactEdges.lean -/
section RppSource_CompactEdges
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem mem_compactMatchingEdges_mk {k : ℕ} {u v : Fin k} (different : u ≠ v) :
    s(u, v) ∈ compactMatchingEdges k := by
  apply List.mem_flatMap.mpr
  refine ⟨u, by simp, List.mem_map.mpr ⟨v, ?_, rfl⟩⟩
  simp [different]

theorem mem_compactMatchingEdges_iff {k : ℕ} {e : Sym2 (Fin k)} :
    e ∈ compactMatchingEdges k ↔ ¬ e.IsDiag := by
  constructor
  · intro h
    obtain ⟨u, _, row⟩ := List.mem_flatMap.mp h
    obtain ⟨v, present, rfl⟩ := List.mem_map.mp row
    have distinct : u ≠ v := of_decide_eq_true (List.mem_filter.mp present).2
    exact fun loop => distinct (Sym2.mk_isDiag_iff.mp loop)
  · induction e using Sym2.inductionOn with
    | hf u v => exact fun h => mem_compactMatchingEdges_mk (fun eq => h (Sym2.mk_isDiag_iff.mpr eq))



end VehicleRoutingSurvey.Routing
end RppSource_CompactEdges

/-! matching/MatchingSearchDual.lean -/
section RppSource_MatchingSearchDual
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





theorem AlternatingForestState.mate_dualDirection_add_eq_zero {α : Type*}
    {forest : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : forest.valid mate tight) {u v : α} (uv : mate u = some v) (vu : mate v = some u) :
    (forest.role u).dualDirection + (forest.role v).dualDirection = 0 := by
  have outerPartner {x y : α} {p : Option α} (outer : forest.role x = .outer p) (xy : mate x = some y) :
      ∃ r, forest.role y = .inner r := by
    have row := valid x
    rw [outer] at row
    cases p with
    | none =>
      have impossible : some y = none := xy.symm.trans row
      simp at impossible
    | some p =>
      obtain ⟨pInner, xp, _, _, _⟩ := row
      exact (Option.some.inj (xp.symm.trans xy)) ▸ pInner
  have innerPartner {x y p : α} (inner : forest.role x = .inner p) (xy : mate x = some y) :
      forest.role y = .outer (some x) := by
    have row := valid x
    rw [inner] at row
    obtain ⟨_, _, ⟨z, xz, outer⟩, _, _⟩ := row
    exact (Option.some.inj (xz.symm.trans xy)) ▸ outer
  cases hu : forest.role u with
  | outer p =>
    obtain ⟨r, hv⟩ := outerPartner hu uv
    norm_num [hv, AlternatingForestRole.dualDirection]
  | inner p => norm_num [innerPartner hu uv, AlternatingForestRole.dualDirection]
  | unlabelled =>
    cases hv : forest.role v with
    | unlabelled => simp [AlternatingForestRole.dualDirection]
    | outer p =>
      obtain ⟨r, bad⟩ := outerPartner hv vu
      simp [hu] at bad
    | inner p =>
      have bad := innerPartner hv vu
      simp [hu] at bad



theorem CompactMatchingPartition.dualLabel_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (v : Fin k) :
    part.dualLabel forest positive (part.blocks.block v) = (forest.role (part.representative v)).dualDirection := by
  rw [CompactMatchingPartition.dualLabel, part.representativeOf_block]

theorem CompactMatchingSearchForest.matched_slope_zero {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    {e : Sym2 (Fin k)} (present : e ∈ state.edges) :
    oddCutDualEdgeValue state.cuts (forestVertexDirection part.blocks (part.dualLabel forest positive))
      (forestCutDirection part.blocks (part.dualLabel forest positive)) e = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have legal := (state.perfect.1 _ present).1
    have distinct : u ≠ v := fun same => legal (Sym2.mk_isDiag_iff.mpr same)
    rw [forest_edge_slope part.blocks _ (Finset.mem_univ u) (Finset.mem_univ v) distinct]
    by_cases same : part.blocks.block u = part.blocks.block v
    · rw [if_pos same]
    · rw [if_neg same, part.dualLabel_block, part.dualLabel_block]
      obtain ⟨uv, vu⟩ := search.crossing present same
      exact AlternatingForestState.mate_dualDirection_add_eq_zero search.valid uv vu

/-- The selected step keeps the primal matching and partition intact while
updating the two dual functions and exposing the newly tight event. -/
noncomputable def CompactMatchingPrimalDual.advanceSearch {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (part : CompactMatchingPartition state)
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    (internal : state.InternalCuts) (bound : DualBound (MatchingDualEvent k))
    (adjustment : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
      (forestCutDirection part.blocks (part.dualLabel forest positive)) bound) : CompactMatchingPrimalDual k cost where
  covered := state.covered
  edges := state.edges
  perfect := state.perfect
  cuts := state.cuts
  potential v := state.potential v + bound.amount * forestVertexDirection part.blocks (part.dualLabel forest positive) v
  cutDual B := state.cutDual B + bound.amount * forestCutDirection part.blocks (part.dualLabel forest positive) B
  cutValid B present := ⟨(state.cutValid B present).1, adjustment.2.2.1 B present⟩
  feasible e legal := adjustment.2.1 e (mem_compactMatchingEdges_iff.mpr legal)
  tight e present := by
    rw [oddCutDualEdgeValue_shift, search.matched_slope_zero positive present, mul_zero, add_zero]
    exact state.tight e present
  internal B present _ := internal B present


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchDual

/-! matching/MatchingEventDualRefinement.lean -/
section RppSource_MatchingEventDualRefinement
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Moving the dual leaves the top partition and its representatives intact. -/
noncomputable def CompactMatchingPartition.advanceSearch {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    (internal : state.InternalCuts) (bound : DualBound (MatchingDualEvent k))
    (adjustment : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
      (forestCutDirection part.blocks (part.dualLabel forest positive)) bound) :
    CompactMatchingPartition (state.advanceSearch part search positive internal bound adjustment) where
  blocks := part.blocks
  representative := part.representative
  inside := part.inside
  constant := part.constant
  coveredAway := part.coveredAway




end VehicleRoutingSurvey.Routing
end RppSource_MatchingEventDualRefinement

/-! matching/MatchingTraceDispatch.lean -/
section RppSource_MatchingTraceDispatch
namespace VehicleRoutingSurvey.Routing















structure MatchingResolvedOuter {k : ℕ} (forest : AlternatingForestState (Fin k))
    (u v : Fin k) (base : ℕ) (s t : ArithmeticState) : Prop where
  tag : t.nr 35 = if forest.commonAncestor u v = none then 3 else 1
  selected : t.nr 1 = s.nr 91
  zero : t.nr 36 = 0
  leftCount : t.nr 10 = (forest.traceToRoot u).length
  rightCount : t.nr 11 = (forest.traceToRoot v).length
  left : ForestTraceArray t.nm (s.nr 83) (forest.traceToRoot u)
  right : ForestTraceArray t.nm (s.nr 84) (forest.traceToRoot v)
  shared : t.nr 12 = ((forest.commonAncestor u v).map Fin.val).getD k
  split : ForestTraceSplit (forest.traceToRoot u) (forest.traceToRoot v)
    (forest.commonAncestor u v) (t.nr 13) (t.nr 14)
  natural : ∀ a, a < base ∨ base + 3 * k ≤ a → t.nm a = s.nm a
  registers : ∀ r, r ∉ [1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 35, 36] → t.nr r = s.nr r
  realRegisters : t.rr = s.rr
  realMemory : t.rm = s.rm



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingTraceDispatch

/-! matching/MatchingContractionCycleOrder.lean -/
section RppSource_MatchingContractionCycleOrder
namespace VehicleRoutingSurvey.Routing









def contractionCycleOrder {α : Type*} (left right : List α) (base : α) := left ++ base :: right.reverse













end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCycleOrder

/-! matching/MatchingContractionWrittenRows.lean -/
section RppSource_MatchingContractionWrittenRows
namespace VehicleRoutingSurvey.Routing

/-- The row at a physical cycle index of the newly appended node. -/
def matchingContractionWrittenChild (s : ArithmeticState) (i : ℕ) : MatchingCycleChild :=
  let r := matchingCycleRecordReference s
  if i < s.nr 13 then leftCycleRecordAt r i else if i = s.nr 13 then commonCycleRecord r
    else rightCycleRecordAt r (i - (s.nr 13+1))



end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionWrittenRows

/-! matching/MatchingContractionCycleEdges.lean -/
section RppSource_MatchingContractionCycleEdges
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- An oriented row of the emitted cycle retains original endpoints in its two
direct children. If those children are mates, the words are precisely the ports. -/
def ContractionCycleEdgeWords {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (src dst : Fin k) (words : ℕ × ℕ) : Prop :=
  ∃ a b : Fin k, words = (a.val,b.val) ∧ part.representative a = src ∧ part.representative b = dst ∧
    oddCutDualEdgeValue state.cuts state.potential state.cutDual s(a,b) = edgeCost cost s(a,b) ∧
    (state.partialMate src = some dst → a = src ∧ b = dst)











end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCycleEdges

/-! matching/MatchingContractionPrimal.lean -/
section RppSource_MatchingContractionPrimal
namespace VehicleRoutingSurvey.Routing

theorem contractionMates_covered {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {cycle : Finset (Fin k)} {base : Fin k}
    (pairs : ∀ x ∈ cycle, x ≠ base → ∃ y ∈ cycle, y ≠ base ∧ state.partialMate x = some y) :
    ∀ x ∈ cycle, x ≠ base → x ∈ state.covered := by
  intro x hx diff
  obtain ⟨y,_,_,edge⟩ := pairs x hx diff
  exact (state.perfect.1 _ (state.partialMate_some_iff.mp edge)).2 x (Sym2.mem_mk_left _ _)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPrimal

/-! matching/MatchingContractionArchiveFrame.lean -/
section RppSource_MatchingContractionArchiveFrame
namespace VehicleRoutingSurvey.Routing

/-- The old trees read only allocated start and count words and bytes strictly
before the next cycle cursor. Reserving the next pair of headers is safe. -/
def matchingContractionOldArchive (s : ArithmeticState) (a : ℕ) : Prop :=
  (∃ n < s.nr 76, a = s.nr 77+n ∨ a = s.nr 78+n) ∨
  matchingRebaseScratchEnd s ≤ a ∧ a < s.nr 68







end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionArchiveFrame



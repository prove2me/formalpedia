-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces
-- name    : VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T15:59:08.83928+00:00
-- url     : https://prove2.me/theorems/507085a2-53bf-4a49-84b0-50be0f1c7050
-- title:
--   Rural postman algorithm — matcher proof interfaces
-- statement:
--   The Lean types for the contraction, expansion, and augmentation proofs describe the weighted matcher’s memory layout, partial matching, and dual search state. This module also defines the interface between the stage invariant and the fixed matcher program.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface

/-! matching/WeightedDeltaRAM.lean -/
section RppSource_WeightedDeltaRAM
namespace VehicleRoutingSurvey.Routing

/-- Real registers 0 and 3 contain slack and rate. Divide for a rising constraint, or
clear the candidate edge identifier for a constraint that imposes no upper bound. -/
def prepareDualBoundBlock : List ArithmeticInstruction :=
  [.realConst 4 0, .realBranch 3 4 2 4, .natConst 0 0, .jump 6, .realDiv 0 0 3, .jump 6]





def mergeDualBoundBlock : List ArithmeticInstruction := appendBlock prepareDualBoundBlock mergeSlackEntryBlock





end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaRAM

/-! matching/WeightedReadDeltaRAM.lean -/
section RppSource_WeightedReadDeltaRAM
namespace VehicleRoutingSurvey.Routing



































/-- Read one cached event. Natural registers 3, 4, and 5 address the identifier, slack, and
rate arrays. Register 7 is the current index. The identifier is zero for an empty slot. -/
def readDualBoundBlock : List ArithmeticInstruction :=
  [.natAdd 6 3 7, .natLoad 0 6, .natAdd 6 4 7, .realLoad 0 6, .natAdd 6 5 7, .realLoad 3 6]





def considerDualBoundBlock : List ArithmeticInstruction := appendBlock readDualBoundBlock mergeDualBoundBlock





end VehicleRoutingSurvey.Routing
end RppSource_WeightedReadDeltaRAM

/-! matching/MatchingStageControl.lean -/
section RppSource_MatchingStageControl
namespace VehicleRoutingSurvey.Routing

/-- Start the stage driver and the dual selector with the permanent matching tables. -/
def resetMatchingStageControlBlock : List ArithmeticInstruction :=
  [.natConst 29 0, .natConst 34 1, .natAdd 31 55 55, .natAdd 31 31 55,
   .natAdd 31 31 31, .natAdd 31 31 34, .natConst 32 0, .natConst 33 1,
   .natConst 1 0, .natConst 9 1, .natAdd 3 58 29, .natAdd 4 59 29,
   .natAdd 5 60 29, .natAdd 8 61 29, .realConst 15 0]





/-- Publish the final compact mate array and restore the compact row-map registers. -/
def publishCompactMateTableBlock : List ArithmeticInstruction :=
  [.natConst 0 0, .natAdd 31 56 0, .natAdd 32 55 0, .natAdd 33 50 0]




end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageControl

/-! matching/MatchingTerminalState.lean -/
section RppSource_MatchingTerminalState
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

structure MatchingTerminalCertificate (k : ℕ) (cost : Fin k → Fin k → ℝ)
    (original result : ArithmeticState) where
  mate : Fin k → Fin k
  cuts : Finset (Finset (Fin k))
  potential : Fin k → ℝ
  cutDual : Finset (Fin k) → ℝ
  dimension : result.nr 55 = k
  mapBase : result.nr 56 = original.nr 31
  mateAbove : original.nr 63 ≤ result.nr 50
  mateBytes : ∀ v : Fin k, result.nm (result.nr 50 + v.val) = (mate v).val
  validMate : MateTableOn Finset.univ mate
  saved : ∀ r ≥ 100, result.nr r = original.nr r
  natural : ∀ a < original.nr 63, result.nm a = original.nm a
  real : ∀ a < original.nr 64, result.rm a = original.rm a
  cutValid : ∀ B ∈ cuts, Odd B.card ∧ 0 ≤ cutDual B
  feasible : ∀ e, ¬e.IsDiag → oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost cost e
  tight : ∀ e ∈ mateEdgeSet Finset.univ mate, oddCutDualEdgeValue cuts potential cutDual e = edgeCost cost e
  internal : ∀ B ∈ cuts, 0 < cutDual B → ∃ base ∈ B,
    ∀ v ∈ B, v ≠ base → ∃ e ∈ mateEdgeSet Finset.univ mate, v ∈ e ∧ ∀ w ∈ e, w ∈ B










end VehicleRoutingSurvey.Routing
end RppSource_MatchingTerminalState

/-! matching/MatchingPartitionView.lean -/
section RppSource_MatchingPartitionView
namespace VehicleRoutingSurvey.Routing



theorem CompactMatchingPartition.same_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) {u v : Fin k} :
    part.representative u = part.representative v ↔ part.blocks.block u = part.blocks.block v := by
  refine ⟨?_, part.constant u v⟩
  intro same
  have first := part.blocks.same_of_mem (Finset.mem_univ u) (part.inside u)
  have second := part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v)
  rw [same] at first
  exact first.symm.trans second

theorem CompactMatchingPartition.representative_idem {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (v : Fin k) :
    part.representative (part.representative v) = part.representative v :=
  part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v))












end VehicleRoutingSurvey.Routing
end RppSource_MatchingPartitionView

/-! matching/AlternatingForestGrow.lean -/
section RppSource_AlternatingForestGrow
namespace VehicleRoutingSurvey.Routing







/-- Reach a matched, unlabelled pair through a tight edge from an existing outer node. -/
def AlternatingForestState.grow {α : Type*} [DecidableEq α] (state : AlternatingForestState α)
    (source inner outer : α) : AlternatingForestState α where
  role x := if x = inner then .inner source else if x = outer then .outer (some inner) else state.role x
  depth x := if x = inner then state.depth source + 1
    else if x = outer then state.depth source + 2 else state.depth x



end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrow

/-! matching/AlternatingForestTrace.lean -/
section RppSource_AlternatingForestTrace
namespace VehicleRoutingSurvey.Routing



theorem AlternatingForestState.parent_valid {α : Type*}
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {x : α} (marked : state.role x ≠ .unlabelled) :
    match (state.role x).parent with
    | none => state.role x = .outer none ∧ mate x = none
    | some p => state.role p ≠ .unlabelled ∧ state.depth p < state.depth x ∧ tight p x := by
  have old := valid x
  cases kind : state.role x with
  | unlabelled => exact (marked kind).elim
  | outer parent =>
    try rw [kind] at old
    cases parent with
    | none => exact ⟨rfl, old⟩
    | some p =>
      obtain ⟨⟨q, pRole⟩, _, _, edge, earlier⟩ := old
      exact ⟨by simp [pRole], earlier, edge⟩
  | inner p =>
    try rw [kind] at old
    obtain ⟨⟨q, pRole⟩, _, _, edge, earlier⟩ := old
    exact ⟨by simp [pRole], earlier, edge⟩

 def AlternatingForestState.traceParents {α : Type*} (state : AlternatingForestState α) :
    ℕ → α → List α
  | 0, _ => []
  | fuel + 1, x => x :: (match (state.role x).parent with
      | none => []
      | some p => state.traceParents fuel p)

/-- Follow the marked node's parent pointers to its exposed outer root. -/
def AlternatingForestState.traceToRoot {α : Type*} (state : AlternatingForestState α) (x : α) : List α :=
  state.traceParents (state.depth x + 1) x





end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTrace

/-! matching/AlternatingForestAncestor.lean -/
section RppSource_AlternatingForestAncestor
namespace VehicleRoutingSurvey.Routing

 def markForestTrace {α : Type*} [DecidableEq α] (trace : List α) : α → Bool :=
  trace.foldl (fun table v => Function.update table v true) (fun _ => false)



/-- Mark the first parent trace, then scan the second from its endpoint towards its root. -/
def firstSharedAncestor {α : Type*} [DecidableEq α] (left right : List α) : Option α :=
  right.find? (markForestTrace left)





/-- Select the common ancestor for contraction, or report that the endpoints lie in
different trees. The mark table avoids comparing every pair of entries in the two traces. -/
def AlternatingForestState.commonAncestor {α : Type*} [DecidableEq α]
    (state : AlternatingForestState α) (u v : α) : Option α :=
  firstSharedAncestor (state.traceToRoot u) (state.traceToRoot v)



end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAncestor

/-! matching/BlossomPartitionMerge.lean -/
section RppSource_BlossomPartitionMerge
namespace VehicleRoutingSurvey.Routing

/-- Contract the chosen top-level children to their union and register the new odd cut. -/
def TopLevelMatchingBlocks.contract {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (children : Finset (Finset (Fin n)))
    (top : children ⊆ O.image blocks.block) :
    TopLevelMatchingBlocks O (insert (children.biUnion id) cuts) where
  block v := if blocks.block v ∈ children then children.biUnion id else blocks.block v
  self_mem v hv := by
    by_cases merged : blocks.block v ∈ children
    · exact (if_pos merged).symm ▸ Finset.mem_biUnion.mpr ⟨blocks.block v, merged, blocks.self_mem v hv⟩
    · exact (if_neg merged).symm ▸ blocks.self_mem v hv
  same_of_mem {v w} hv hw := by
    by_cases merged : blocks.block v ∈ children
    · rw [if_pos merged] at hw ⊢
      obtain ⟨child, member, inChild⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨u, hu, blockEq⟩ := Finset.mem_image.mp (top member)
      have wasChild : blocks.block w = child :=
        (blocks.same_of_mem hu (blockEq.symm ▸ inChild)).trans blockEq
      rw [wasChild, if_pos member]
    · rw [if_neg merged] at hw ⊢
      rw [blocks.same_of_mem hv hw, if_neg merged]
  cut_mem {v} hv nontrivial := by
    by_cases merged : blocks.block v ∈ children
    · rw [if_pos merged]
      exact Finset.mem_insert_self _ _
    · rw [if_neg merged] at nontrivial ⊢
      exact Finset.mem_insert_of_mem (blocks.cut_mem hv nontrivial)

theorem contractedBlossom_eligible {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) {children : Finset (Finset (Fin n))}
    (top : children ⊆ O.image blocks.block) (contained : ∀ v ∈ O, blocks.block v ⊆ O)
    (oddChildren : ∀ S ∈ children, Odd S.card) (oddCycle : Odd children.card) :
    children.biUnion id ⊆ O ∧ Odd (children.biUnion id).card := by
  constructor
  · intro v hv
    obtain ⟨child, member, inChild⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨u, hu, shape⟩ := Finset.mem_image.mp (top member)
    exact contained u hu (shape.symm ▸ inChild)
  · have disjoint : (children : Set (Finset (Fin n))).PairwiseDisjoint id := by
      intro S sIn T tIn different
      apply Finset.disjoint_left.mpr
      intro v inS inT
      obtain ⟨x, hx, shapeS⟩ := Finset.mem_image.mp (top sIn)
      obtain ⟨y, hy, shapeT⟩ := Finset.mem_image.mp (top tIn)
      have intoS := (blocks.same_of_mem hx (shapeS.symm ▸ inS)).trans shapeS
      have intoT := (blocks.same_of_mem hy (shapeT.symm ▸ inT)).trans shapeT
      exact different (intoS.symm.trans intoT)
    rw [Nat.odd_iff, Finset.card_biUnion disjoint]
    have counts := Nat.ModEq.sum (n := 2) (s := children) (f := fun S => S.card) (g := fun _ => 1)
      (fun S hS => by simpa only [Nat.ModEq] using Nat.odd_iff.mp (oddChildren S hS))
    simp only [Nat.ModEq, Finset.sum_const, nsmul_eq_mul, mul_one] at counts
    simpa only [id_eq] using counts.trans (Nat.odd_iff.mp oddCycle)

/-- Assign zero only to newly represented cuts. Existing dual values are unchanged. -/
noncomputable def extendBlossomCutDual {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (dual : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  if S ∈ cuts then dual S else 0

/-- Registering a contracted cut at zero preserves every edge's dual value and slack. -/
theorem oddCutDualEdgeValue_register_cut {n : ℕ} (cuts : Finset (Finset (Fin n))) (S : Finset (Fin n))
    (potential : Fin n → ℝ) (dual : Finset (Fin n) → ℝ) (e : Sym2 (Fin n)) :
    oddCutDualEdgeValue (insert S cuts) potential (extendBlossomCutDual cuts dual) e =
      oddCutDualEdgeValue cuts potential dual e := by
  simp only [oddCutDualEdgeValue, Finset.sum_filter]
  congr 1
  have preserves : (∑ B ∈ cuts, if MatchingCrossesCut B e then extendBlossomCutDual cuts dual B else 0) =
      ∑ B ∈ cuts, if MatchingCrossesCut B e then dual B else 0 :=
    Finset.sum_congr rfl fun B hB => by simp only [extendBlossomCutDual, if_pos hB]
  by_cases already : S ∈ cuts
  · rwa [Finset.insert_eq_of_mem already]
  · rw [Finset.sum_insert already, preserves]
    simp [extendBlossomCutDual, already]

end VehicleRoutingSurvey.Routing
end RppSource_BlossomPartitionMerge

/-! matching/BlossomPartitionExpand.lean -/
section RppSource_BlossomPartitionExpand
namespace VehicleRoutingSurvey.Routing

/-- Expand a top-level blossom into its stored children and remove the blossom cut. -/
def TopLevelMatchingBlocks.expand {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (blossom : Finset (Fin n))
    (top : blossom ∈ O.image blocks.block) (child : Fin n → Finset (Fin n))
    (childSelf : ∀ v ∈ blossom, v ∈ child v) (childSubset : ∀ v ∈ blossom, child v ⊆ blossom)
    (childSame : ∀ v ∈ blossom, ∀ w ∈ child v, child w = child v)
    (childCut : ∀ v ∈ blossom, (child v).card ≠ 1 → child v ∈ cuts.erase blossom) :
    TopLevelMatchingBlocks O (cuts.erase blossom) where
  block v := if blocks.block v = blossom then child v else blocks.block v
  self_mem v hv := by
    by_cases inside : blocks.block v = blossom
    · rw [if_pos inside]
      exact childSelf v (inside ▸ blocks.self_mem v hv)
    · rw [if_neg inside]
      exact blocks.self_mem v hv
  same_of_mem {v w} hv hw := by
    by_cases inside : blocks.block v = blossom
    · rw [if_pos inside] at hw ⊢
      have vIn : v ∈ blossom := inside ▸ blocks.self_mem v hv
      have wIn : w ∈ blossom := childSubset v vIn hw
      obtain ⟨u, hu, identifies⟩ := Finset.mem_image.mp top
      have wBlock : blocks.block w = blossom :=
        (blocks.same_of_mem hu (identifies.symm ▸ wIn)).trans identifies
      rw [if_pos wBlock, childSame v vIn w hw]
    · rw [if_neg inside] at hw ⊢
      rw [blocks.same_of_mem hv hw, if_neg inside]
  cut_mem {v} hv nonsingleton := by
    by_cases inside : blocks.block v = blossom
    · rw [if_pos inside] at nonsingleton ⊢
      exact childCut v (inside ▸ blocks.self_mem v hv) nonsingleton
    · rw [if_neg inside] at nonsingleton ⊢
      exact Finset.mem_erase.mpr ⟨inside, blocks.cut_mem hv nonsingleton⟩

/-- Removing a zero-dual blossom at expansion preserves every edge's slack and tightness. -/
theorem oddCutDualEdgeValue_erase_zero {n : ℕ} (cuts : Finset (Finset (Fin n)))
    {blossom : Finset (Fin n)} (member : blossom ∈ cuts)
    (potential : Fin n → ℝ) (dual : Finset (Fin n) → ℝ) (zero : dual blossom = 0) (e : Sym2 (Fin n)) :
    oddCutDualEdgeValue (cuts.erase blossom) potential dual e = oddCutDualEdgeValue cuts potential dual e := by
  simp only [oddCutDualEdgeValue, Finset.sum_filter]
  congr 1
  simpa [zero] using Finset.sum_erase_add cuts (fun S => if MatchingCrossesCut S e then dual S else 0) member

end VehicleRoutingSurvey.Routing
end RppSource_BlossomPartitionExpand

/-! matching/MatchingSearchTopology.lean -/
section RppSource_MatchingSearchTopology
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





/-- Contraction registers an odd cut with dual zero. It leaves the original
matching and every edge's dual value intact. -/
noncomputable def CompactMatchingPrimalDual.registerCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (B : Finset (Fin k)) (odd : Odd B.card) :
    CompactMatchingPrimalDual k cost where
  covered := state.covered
  edges := state.edges
  perfect := state.perfect
  cuts := insert B state.cuts
  potential := state.potential
  cutDual := extendBlossomCutDual state.cuts state.cutDual
  cutValid S present := by
    by_cases old : S ∈ state.cuts
    · simpa only [extendBlossomCutDual, if_pos old] using state.cutValid S old
    · have eq : S = B := (Finset.mem_insert.mp present).resolve_right old
      exact ⟨eq.symm ▸ odd, by simp [extendBlossomCutDual, old]⟩
  feasible e legal := by rw [oddCutDualEdgeValue_register_cut]; exact state.feasible e legal
  tight e member := by rw [oddCutDualEdgeValue_register_cut]; exact state.tight e member
  internal S _ positive := by
    have old : S ∈ state.cuts := by
      by_contra absent
      simp [extendBlossomCutDual, absent] at positive
    exact state.internal S old (by simpa only [extendBlossomCutDual, if_pos old] using positive)

/-- Expansion removes the exhausted cut. Its children's registry and dual
values stay available for the next forest and matching operations. -/
def CompactMatchingPrimalDual.eraseZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) {B : Finset (Fin k)}
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0) : CompactMatchingPrimalDual k cost where
  covered := state.covered
  edges := state.edges
  perfect := state.perfect
  cuts := state.cuts.erase B
  potential := state.potential
  cutDual := state.cutDual
  cutValid S member := state.cutValid S (Finset.mem_of_mem_erase member)
  feasible e legal := by rw [oddCutDualEdgeValue_erase_zero _ present _ _ zero]; exact state.feasible e legal
  tight e member := by rw [oddCutDualEdgeValue_erase_zero _ present _ _ zero]; exact state.tight e member
  internal S member := state.internal S (Finset.mem_of_mem_erase member)






end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchTopology

/-! matching/MatchingForestReset.lean -/
section RppSource_MatchingForestReset
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Reset one vertex's forest entry. The top-level representatives are exactly the vertices
that represent themselves. An exposed representative has the compact dimension as its mate. -/
 def resetMatchingForestCell : List ArithmeticInstruction :=
  [.natAdd 12 57 71, .natLoad 13 12, .natAdd 12 50 71, .natLoad 14 12,
   .natConst 15 0, .natBranch 13 71 6 9, .natBranch 71 13 7 9, .natBranch 55 14 8 9,
   .natConst 15 1, .natAdd 12 51 71, .natStore 12 15, .natAdd 12 52 71, .natStore 12 55,
   .natAdd 12 53 71, .natConst 17 0, .natStore 12 17]

def resetMatchingForestBlock : List ArithmeticInstruction :=
  countedLoopFromZero 34 71 55 resetMatchingForestCell












end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestReset

/-! matching/MatchingClearCandidates.lean -/
section RppSource_MatchingClearCandidates
namespace VehicleRoutingSurvey.Routing

 def clearMatchingCandidateCell : List ArithmeticInstruction :=
  [.natConst 0 0, .natAdd 2 58 71, .natStore 2 0]

/-- Mark every candidate slot inactive. Its other cells are read only once a new identifier
has been installed. -/
def clearMatchingCandidatesBlock : List ArithmeticInstruction :=
  countedLoopFromZero 34 71 61 clearMatchingCandidateCell






end VehicleRoutingSurvey.Routing
end RppSource_MatchingClearCandidates

/-! matching/MatchingPairClear.lean -/
section RppSource_MatchingPairClear
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

 def measureMatchingMatrixBlock : List ArithmeticInstruction :=
  [.natConst 71 0, .natBranch 55 71 7 2, .natSub 73 55 34, .natAdd 73 21 73,
   .natLoad 73 73, .natAdd 73 73 55, .jump 8, .natConst 73 0]



 def clearMatchingPairSlot : List ArithmeticInstruction :=
  [.natAdd 71 72 72, .natAdd 71 65 71, .natStore 71 55]

 def clearMatchingPairSlots : List ArithmeticInstruction :=
  countedLoopFromZero 34 72 73 clearMatchingPairSlot

/-- Only the first endpoint word of a pair bucket needs resetting. Both endpoints and its
key are installed together when an edge occupies the bucket. -/
def clearMatchingPairCacheBlock : List ArithmeticInstruction :=
  appendBlock measureMatchingMatrixBlock clearMatchingPairSlots










end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairClear

/-! matching/MatchingWarmSeed.lean -/
section RppSource_MatchingWarmSeed
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace VehicleRoutingSurvey.Routing

def readWarmCacheSource : List ArithmeticInstruction :=
  [.natAdd 15 24 14, .natAdd 6 57 15, .natLoad 26 6, .natAdd 6 51 26, .natLoad 19 6]

def refreshWarmCacheSource : List ArithmeticInstruction :=
  appendBlock readWarmCacheSource (branchOnAtMost 19 14 [] refreshSelectedOuterVertex)

def sweepWarmMatchingCache : List ArithmeticInstruction :=
  countedLoopFromZero 9 24 55 refreshWarmCacheSource

/-- Rebuild the reset cache from each original vertex whose top-level representative is
outer. The stage begins with no inner representatives. -/
def rebuildMatchingActiveCacheBlock : List ArithmeticInstruction :=
  appendBlock [.natConst 14 0] sweepWarmMatchingCache

/-- Reinitialize a search following an augmentation. The reset preserves the matched
edges and the remaining blossoms. -/
def warmMatchingPreparationPrefixBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock resetMatchingStageControlBlock resetMatchingForestBlock)
    clearMatchingCandidatesBlock) clearMatchingPairCacheBlock

def warmMatchingPreparationBlock : List ArithmeticInstruction :=
  appendBlock warmMatchingPreparationPrefixBlock rebuildMatchingActiveCacheBlock












end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmSeed

/-! matching/MatchingWarmPrimal.lean -/
section RppSource_MatchingWarmPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem CompactMatchingPrimalDual.partialMate_some_iff {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) {v w : Fin k} : state.partialMate v = some w ↔
      s(v, w) ∈ state.edges := by
  by_cases covered : v ∈ state.covered
  · rw [CompactMatchingPrimalDual.partialMate, if_pos covered, Option.some.injEq]
    constructor
    · rintro rfl
      exact mateOfMatching_edge state.perfect covered
    · intro known
      have equal := (state.perfect.2 v covered).unique
        ⟨mateOfMatching_edge state.perfect covered, Sym2.mem_mk_left _ _⟩
        ⟨known, Sym2.mem_mk_left _ _⟩
      rcases Sym2.eq_iff.mp equal with direct | reversal
      · exact direct.2
      · exact reversal.2.trans reversal.1
  · rw [CompactMatchingPrimalDual.partialMate, if_neg covered]
    constructor
    · intro impossible
      cases impossible
    · intro impossible
      exact (covered ((state.perfect.1 _ impossible).2 v (Sym2.mem_mk_left _ _))).elim





def CompactMatchingPartition.activeRepresentatives {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) : Finset (Fin k) :=
  Finset.univ.filter fun v => part.representative v = v












end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPrimal

/-! matching/MatchingExpansionPartition.lean -/
section RppSource_MatchingExpansionPartition
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The child blocks obtained from the live registry agree with their original
members and identify one exposed port for each child. -/
structure MatchingExpansionChildren {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (B : Finset (Fin k)) where
  block : Fin k → Finset (Fin k)
  representative : Fin k → Fin k
  self : ∀ v ∈ B, v ∈ block v
  subset : ∀ v ∈ B, block v ⊆ B
  same : ∀ v ∈ B, ∀ w ∈ block v, block w = block v
  cut : ∀ v ∈ B, (block v).card ≠ 1 → block v ∈ state.cuts.erase B
  inside : ∀ v ∈ B, representative v ∈ block v
  constant : ∀ u ∈ B, ∀ v ∈ B, block u = block v → representative u = representative v
  interior : ∀ v ∈ B, ∀ w ∈ block v, w ≠ representative v →
    ∃ e ∈ state.edges, w ∈ e ∧ ∀ z ∈ e, z ∈ block v
  matchedBase : ∀ v ∈ B, ∀ w, state.partialMate (representative v) = some w → w ∉ block v

theorem CompactMatchingPartition.block_eq_iff_member {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block) (v : Fin k) :
    part.blocks.block v = B ↔ v ∈ B := by
  constructor
  · intro same
    rw [← same]
    exact part.blocks.self_mem v (Finset.mem_univ v)
  · intro member
    obtain ⟨u, hu, identifies⟩ := Finset.mem_image.mp top
    exact (part.blocks.same_of_mem hu (identifies.symm ▸ member)).trans identifies

 theorem selectExpansionBlock {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block)
    (v : Fin k) (inside outside : Finset (Fin k)) :
    (if part.blocks.block v = B then inside else outside) = (if v ∈ B then inside else outside) := by
  by_cases h : v ∈ B
  · simp only [if_pos h, if_pos ((part.block_eq_iff_member top v).2 h)]
  · simp only [if_neg h, if_neg (fun e => h ((part.block_eq_iff_member top v).1 e))]

/-- Opening an exhausted blossom refines exactly its own block and retains
its children as top-level blocks. Every outside representative is unchanged. -/
def CompactMatchingPartition.openZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (children : MatchingExpansionChildren state B) :
    CompactMatchingPartition (state.eraseZeroCut present zero) where
  blocks := part.blocks.expand B top children.block children.self children.subset children.same children.cut
  representative v := if v ∈ B then children.representative v else part.representative v
  inside v := by
    change (if v ∈ B then children.representative v else part.representative v) ∈
      (if part.blocks.block v = B then children.block v else part.blocks.block v)
    rw [selectExpansionBlock part top v]
    split
    · exact children.inside v ‹v ∈ B›
    · exact part.inside v
  constant u v same := by
    change (if part.blocks.block u = B then children.block u else part.blocks.block u) =
      (if part.blocks.block v = B then children.block v else part.blocks.block v) at same
    rw [selectExpansionBlock part top u, selectExpansionBlock part top v] at same
    change (if u ∈ B then children.representative u else part.representative u) =
      (if v ∈ B then children.representative v else part.representative v)
    by_cases hu : u ∈ B <;> by_cases hv : v ∈ B
    · rw [if_pos hu, if_pos hv] at same ⊢
      exact children.constant u hu v hv same
    · rw [if_pos hu, if_neg hv] at same
      have member := part.blocks.self_mem v (Finset.mem_univ v)
      rw [← same] at member
      exact (hv (children.subset u hu member)).elim
    · rw [if_neg hu, if_pos hv] at same
      have member := part.blocks.self_mem u (Finset.mem_univ u)
      rw [same] at member
      exact (hu (children.subset v hv member)).elim
    · rw [if_neg hu, if_neg hv] at same ⊢
      exact part.constant u v same
  coveredAway v w member notBase := by
    change w ∈ (if part.blocks.block v = B then children.block v else part.blocks.block v) at member
    rw [selectExpansionBlock part top v] at member
    change w ≠ (if v ∈ B then children.representative v else part.representative v) at notBase
    change w ∈ state.covered
    by_cases hv : v ∈ B
    · rw [if_pos hv] at member notBase
      obtain ⟨e, edge, incident, _⟩ := children.interior v hv w member notBase
      exact (state.perfect.1 e edge).2 w incident
    · rw [if_neg hv] at member notBase
      exact part.coveredAway v w member notBase







end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPartition

/-! matching/MatchingExpansionChildPorts.lean -/
section RppSource_MatchingExpansionChildPorts
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



/-- An exposed port of an internally matched child must be the base in the
matching certificate. This identifies the certificate with the registered port. -/
theorem CompactMatchingPrimalDual.certifiedChildBase {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)} {p : Fin k}
    (internal : state.InternalCuts) (live : B ∈ state.cuts) (inside : p ∈ B)
    (exposed : ∀ w, state.partialMate p = some w → w ∉ B) :
    ∀ v ∈ B, v ≠ p → ∃ e ∈ state.edges, v ∈ e ∧ ∀ w ∈ e, w ∈ B := by
  obtain ⟨base, _, matched⟩ := internal B live
  have same : p = base := by
    by_contra different
    obtain ⟨e, edge, incident, contained⟩ := matched p inside different
    have covered := (state.perfect.1 e edge).2 p incident
    let w := mateOfMatching state.perfect p
    have mate : state.partialMate p = some w := by simp [CompactMatchingPrimalDual.partialMate, covered, w]
    have exactEdge := (state.partialMate_some_iff).mp mate
    have sameEdge := (state.perfect.2 p covered).unique ⟨exactEdge, Sym2.mem_mk_left _ _⟩ ⟨edge, incident⟩
    exact exposed w mate (contained w (sameEdge ▸ Sym2.mem_mk_right p w))
  rwa [same]

/-- The old matching determines the nonbase interior edges of every child.
Only exposure of each registered port needs to be read from the cycle. -/
def MatchingExpansionChildPorts.toExpansionChildren {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    (registry : MatchingExpansionChildPorts state B) (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p) :
    MatchingExpansionChildren state B where
  block v := registry.block (registry.owner v)
  representative := registry.owner
  self v member := (registry.covered v member).2
  subset v member := registry.subset _ (registry.covered v member).1
  same v member w inside := by rw [registry.unique _ (registry.covered v member).1 w inside]
  cut v member := registry.live _ (registry.covered v member).1
  inside v member := registry.containsPort _ (registry.covered v member).1
  constant u hu v hv same := by
    have left := (registry.covered u hu).1
    have right := (registry.covered v hv).1
    have inside := registry.containsPort _ left
    rw [same] at inside
    have lhs := registry.unique _ left _ (registry.containsPort _ left)
    exact lhs.symm.trans (registry.unique _ right _ inside)
  interior v member w inside different := by
    have child := (registry.covered v member).1
    have port := registry.containsPort _ child
    by_cases singleton : (registry.block (registry.owner v)).card = 1
    · obtain ⟨p, eq⟩ := Finset.card_eq_one.mp singleton
      rw [eq] at inside port
      exact (different ((Finset.mem_singleton.mp inside).trans (Finset.mem_singleton.mp port).symm)).elim
    · exact CompactMatchingPrimalDual.certifiedChildBase internal
        (Finset.mem_of_mem_erase (registry.live _ child singleton)) port (external _ child) w inside different
  matchedBase v member := external _ (registry.covered v member).1

theorem MatchingExpansionChildPorts.port_external_of_adjacentMate {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    (registry : MatchingExpansionChildPorts state B) {p q : Fin k}
    (pIn : p ∈ registry.ports) (qIn : q ∈ registry.ports) (different : p ≠ q)
    (matched : state.partialMate p = some q) :
    ∀ w, state.partialMate p = some w → w ∉ registry.block p := by
  intro w mate inside
  have same : q = w := Option.some.inj (matched.symm.trans mate)
  subst w
  exact different ((registry.unique p pIn q inside).symm.trans
    (registry.unique q qIn q (registry.containsPort q qIn)))

theorem MatchingExpansionChildPorts.port_external_of_oldBase {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    {part : CompactMatchingPartition state} (matching : CompactTopMatching part)
    (registry : MatchingExpansionChildPorts state B) {p : Fin k} (pIn : p ∈ registry.ports)
    (base : part.representative p = p) (block : part.blocks.block p = B) :
    ∀ w, state.partialMate p = some w → w ∉ registry.block p := by
  intro w mate inside
  have member : w ∈ part.blocks.block p := block.symm ▸ registry.subset p pIn inside
  exact matching.matchedBase base mate (part.blocks.same_of_mem (Finset.mem_univ p) member).symm

/-- The even tail of the current cycle pairs every child except its base.
Those mates are different child ports, so all child bases stay exposed to
their own blocks when the old base is released. -/
theorem MatchingExpansionChildPorts.ports_external_of_cycle {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    {part : CompactMatchingPartition state} (matching : CompactTopMatching part)
    (registry : MatchingExpansionChildPorts state B) (base : Fin k) (children : List (Fin k))
    (cyclePorts : registry.ports = (base :: children).toFinset)
    (nodup : children.Nodup) (even : children.length % 2 = 0)
    (baseFixed : part.representative base = base) (baseBlock : part.blocks.block base = B)
    (childMates : ∀ a b, s(a, b) ∈ alternatingEdges children →
      state.partialMate a = some b ∧ state.partialMate b = some a) :
    ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p := by
  intro p pIn
  by_cases isBase : p = base
  · subst p
    exact registry.port_external_of_oldBase matching pIn baseFixed baseBlock
  · have inner : p ∈ children := by
      rw [cyclePorts, List.mem_toFinset, List.mem_cons] at pIn
      exact pIn.resolve_left isBase
    have perfect := (alternatingEdges_perfect children nodup even).2
    obtain ⟨edge, ⟨eIn, incident⟩, _⟩ := perfect.2 p (List.mem_toFinset.mpr inner)
    induction edge using Sym2.inductionOn with
    | _ a b =>
      have aIn : a ∈ registry.ports := by
        rw [cyclePorts, List.mem_toFinset]
        exact List.mem_cons.mpr (.inr (List.mem_toFinset.mp ((perfect.1 _ eIn).2 a (Sym2.mem_mk_left _ _))))
      have bIn : b ∈ registry.ports := by
        rw [cyclePorts, List.mem_toFinset]
        exact List.mem_cons.mpr (.inr (List.mem_toFinset.mp ((perfect.1 _ eIn).2 b (Sym2.mem_mk_right _ _))))
      have mates := childMates a b (List.mem_toFinset.mp eIn)
      have distinct := mt Sym2.mk_isDiag_iff.mpr (perfect.1 _ eIn).1
      rcases Sym2.mem_iff.mp incident with left | right
      · subst p
        exact registry.port_external_of_adjacentMate aIn bIn distinct mates.1
      · subst p
        exact registry.port_external_of_adjacentMate bIn aIn (Ne.symm distinct) mates.2

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionChildPorts

/-! matching/MatchingCycleRecordRAM.lean -/
section RppSource_MatchingCycleRecordRAM
namespace VehicleRoutingSurvey.Routing























def startMatchingCycleReal (s : ArithmeticState) : ℕ → ℝ :=
  Function.update s.rm (s.nr 75 + s.nr 76) 0

















end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordRAM

/-! matching/MatchingForestWitnessRAM.lean -/
section RppSource_MatchingForestWitnessRAM
namespace VehicleRoutingSurvey.Routing











/-- Reserve a parent-edge witness pair for each compact representative.
Root entries are ignored and need no initialization. -/
def allocateMatchingForestWitnessArray : List ArithmeticInstruction :=
  [.natAdd 90 68 14, .natAdd 68 68 55, .natAdd 68 68 55]































end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestWitnessRAM

/-! matching/MatchingExpansionSearchRAM.lean -/
section RppSource_MatchingExpansionSearchRAM
namespace VehicleRoutingSurvey.Routing

def expansionOldParentWitness (s : ArithmeticState) : ℕ × ℕ :=
  matchingForestWitnessAt s.nm (s.nr 90) (s.nr 97)





























end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSearchRAM

/-! matching/ExpansionRegistryRAM.lean -/
section RppSource_ExpansionRegistryRAM
namespace VehicleRoutingSurvey.Routing

def expansionCycleRow (s : ArithmeticState) (i : ℕ) : MatchingCycleChild :=
  matchingCycleChildAt s.nm (s.nr 18 + 4 * i)





















end VehicleRoutingSurvey.Routing
end RppSource_ExpansionRegistryRAM

/-! matching/AlternatingForestGrowPairs.lean -/
section RppSource_AlternatingForestGrowPairs
namespace VehicleRoutingSurvey.Routing

/-- Restore the inner/outer pairs along the selected blossom expansion route. The
last vertex returned is the outer predecessor of the restored blossom base. -/
def AlternatingForestState.growPairs {α : Type*} [DecidableEq α] (state : AlternatingForestState α)
    (source : α) : List α → AlternatingForestState α × α
  | inner :: outer :: rest => (state.grow source inner outer).growPairs outer rest
  | _ => (state, source)





end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrowPairs

/-! matching/AlternatingForestExpand.lean -/
section RppSource_AlternatingForestExpand
namespace VehicleRoutingSurvey.Routing

 def shiftedForestDepth (threshold extra depth : ℕ) : ℕ :=
  depth + if threshold ≤ depth then extra else 0



 def AlternatingForestState.reserveDepths {α : Type*} (state : AlternatingForestState α)
    (threshold extra : ℕ) : AlternatingForestState α :=
  {state with depth := fun x => shiftedForestDepth threshold extra (state.depth x)}



 def AlternatingForestState.reattachInner {α : Type*} [DecidableEq α] (state : AlternatingForestState α)
    (base predecessor : α) : AlternatingForestState α :=
  {state with role := Function.update state.role base (.inner predecessor)}



/-- Restore the alternating route to an expanded inner blossom's base. Reserve enough depth
between its old parent and its existing descendants before growing the internal pairs. -/
def AlternatingForestState.expandAlong {α : Type*} [DecidableEq α] (state : AlternatingForestState α)
    (source base : α) (vertices : List α) : AlternatingForestState α :=
  let raised := state.reserveDepths (state.depth base) vertices.length
  let grown := raised.growPairs source vertices
  grown.1.reattachInner base grown.2



end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestExpand

/-! matching/MatchingBlossomDualRAM.lean -/
section RppSource_MatchingBlossomDualRAM
namespace VehicleRoutingSurvey.Routing



def blossomRoleAt (s : ArithmeticState) (i : ℕ) : ℕ :=
  s.nm (s.nr 51 + i)

noncomputable def blossomDualAfterDelta (s : ArithmeticState) (i : ℕ) : ℝ :=
  let old := s.rm (s.nr 75 + blossomNodeAt s i)
  if blossomRoleAt s i ≤ 1 then old + s.rr 1 else old - s.rr 1

noncomputable def modifyBlossomDualAt (s : ArithmeticState) (i : ℕ) : ℕ → ℝ :=
  if blossomNodeAt s i = 0 ∨ blossomRoleAt s i = 0 then s.rm
  else Function.update s.rm (s.nr 75 + blossomNodeAt s i) (blossomDualAfterDelta s i)









noncomputable def iterateBlossomDuals (s : ArithmeticState) : ℕ → (ℕ → ℝ)
  | 0 => s.rm
  | i + 1 => modifyBlossomDualAt {s with rm := iterateBlossomDuals s i} i





end VehicleRoutingSurvey.Routing
end RppSource_MatchingBlossomDualRAM

/-! matching/MatchingEffectiveUpdateRAM.lean -/
section RppSource_MatchingEffectiveUpdateRAM
namespace VehicleRoutingSurvey.Routing

def effectiveRoleAt (s : ArithmeticState) (index : ℕ) : ℕ :=
  s.nm (s.nr 51 + s.nm (s.nr 57 + index))

noncomputable def effectivePotentialAfterDelta (s : ArithmeticState) (index : ℕ) : ℝ :=
  let role := effectiveRoleAt s index
  let old := s.rm (s.nr 62 + index)
  if role = 0 then old else if role ≤ 1 then old + s.rr 1 else old - s.rr 1













end VehicleRoutingSurvey.Routing
end RppSource_MatchingEffectiveUpdateRAM

/-! matching/MatchingExpansionLookup.lean -/
section RppSource_MatchingExpansionLookup
namespace VehicleRoutingSurvey.Routing

def expansionOldNode (s : ArithmeticState) : ℕ := s.nm (s.nr 74 + s.nr 97)

def expansionRegisteredCycleBase (s : ArithmeticState) : ℕ := s.nm (s.nr 77 + expansionOldNode s)

def expansionRegisteredCycleLength (s : ArithmeticState) : ℕ := s.nm (s.nr 78 + expansionOldNode s)















end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionLookup

/-! matching/MatchingExpansionEmitter.lean -/
section RppSource_MatchingExpansionEmitter
namespace VehicleRoutingSurvey.Routing





def expansionTripleAt (memory : ℕ → ℕ) (address : ℕ) : ℕ × ℕ × ℕ :=
  (memory address, memory (address + 1), memory (address + 2))



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionEmitter

/-! matching/TightBlossomRematch.lean -/
section RppSource_TightBlossomRematch
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory







/-- Rotate a blossom cycle to its new base and match the remaining children in order. -/
def rematchBlossomCycle {n : ℕ} (vertices : List (Fin n)) (base : ℕ) : Finset (Sym2 (Fin n)) :=
  (alternatingEdges (vertices.rotate base).tail).toFinset



end VehicleRoutingSurvey.Routing
end RppSource_TightBlossomRematch

/-! matching/TightBlossomExpansion.lean -/
section RppSource_TightBlossomExpansion
namespace VehicleRoutingSurvey.Routing



/-- Use the even-length route from the entry to the old base around an odd cycle. The
cycle is stored with the base first. -/
def blossomExpansionPath {α : Type*} (base : α) (vertices : List α) (entry : ℕ) : List α :=
  if entry % 2 = 0 then (vertices.take (entry + 1)).reverse else vertices.drop entry ++ [base]











end VehicleRoutingSurvey.Routing
end RppSource_TightBlossomExpansion

/-! matching/MatchingExpansionRotation.lean -/
section RppSource_MatchingExpansionRotation
namespace VehicleRoutingSurvey.Routing

def expansionForwardArcDistance (length entry base : ℕ) : ℕ :=
  if entry ≤ base then base - entry else length - (entry - base)

def expansionEntryFromBase (length entry base : ℕ) : ℕ :=
  (entry + length - base) % length

def expansionArcLength (length entry base : ℕ) : ℕ :=
  let forward := expansionForwardArcDistance length entry base
  if forward % 2 = 0 then forward else length - forward

def expansionArcIndex (length entry base i : ℕ) : ℕ :=
  (if expansionForwardArcDistance length entry base % 2 = 0 then entry + i
    else entry + length - i) % length











end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRotation

/-! matching/ExpansionArcRAM.lean -/
section RppSource_ExpansionArcRAM
namespace VehicleRoutingSurvey.Routing

def expansionArcScratch : List ℕ :=
  [0, 6, 7, 10, 15, 16, 17, 18, 19, 22, 23, 24, 25, 27, 43, 44, 45, 46, 47, 49,
    81, 82, 94, 95, 96, 98]

def expansionArcWords (initial : ArithmeticState) (e b i : ℕ) : ℕ × ℕ × ℕ :=
  let atIndex := expansionArcIndex (expansionRegisteredCycleLength initial) e b
  let row := fun j => matchingCycleChildAt initial.nm (expansionRegisteredCycleBase initial + 4 * atIndex j)
  if i = 0 then ((row i).representative, (expansionOldParentWitness initial).1, (expansionOldParentWitness initial).2)
  else if expansionForwardArcDistance (expansionRegisteredCycleLength initial) e b % 2 = 0 then
    ((row i).representative, (row (i - 1)).endpointA, (row (i - 1)).endpointB)
  else ((row i).representative, (row i).endpointB, (row i).endpointA)

structure ExpansionArcReady (initial final : ArithmeticState) (e b : ℕ) : Prop where
  cycleStart : final.nr 18 = expansionRegisteredCycleBase initial
  cycleLength : final.nr 19 = expansionRegisteredCycleLength initial
  pathBase : final.nr 94 = initial.nr 86
  arcLength : 2 * final.nr 95 = expansionArcLength (expansionRegisteredCycleLength initial) e b
  parent : final.nr 96 = initial.nm (initial.nr 52 + initial.nr 97)
  mate : final.nr 98 = initial.nm (initial.nr 50 + initial.nr 97)
  words : ∀ i ≤ expansionArcLength (expansionRegisteredCycleLength initial) e b,
    expansionTripleAt final.nm (final.nr 94 + 3 * i) = expansionArcWords initial e b i
  natural : ∀ a, (a < initial.nr 86 ∨
    initial.nr 86 + 3 * (expansionArcLength (expansionRegisteredCycleLength initial) e b + 1) ≤ a) →
    final.nm a = initial.nm a
  real : final.rm = initial.rm
  realRegisters : final.rr = initial.rr
  fixed : ∀ r, r ∉ expansionArcScratch → final.nr r = initial.nr r





end VehicleRoutingSurvey.Routing
end RppSource_ExpansionArcRAM

/-! matching/AlternatingBlossomExpansion.lean -/
section RppSource_AlternatingBlossomExpansion
namespace VehicleRoutingSurvey.Routing



/-- Restore an inner blossom along the even route selected in its stored odd cycle. -/
def AlternatingForestState.expandBlossom {n : ℕ} (state : AlternatingForestState (Fin n))
    (source base : Fin n) (children : List (Fin n)) (entry : ℕ) : AlternatingForestState (Fin n) :=
  state.expandAlong source base (blossomExpansionPath base (base :: children) entry).dropLast



end VehicleRoutingSurvey.Routing
end RppSource_AlternatingBlossomExpansion

/-! matching/MatchingExpansionRefinement.lean -/
section RppSource_MatchingExpansionRefinement
namespace VehicleRoutingSurvey.Routing



structure MatchingExpandedForest {k : ℕ} (forest : AlternatingForestState (Fin k))
    (mate : Fin k → Option (Fin k)) (tightRep tightOriginal : Sym2 (Fin k) → Prop)
    (rep : Fin k → Fin k) (s t : ArithmeticState) : Prop where
  encoding : AlternatingForestMemory forest (s.nr 51) t.nm
  valid : forest.valid mate (fun a b => tightRep s(a, b))
  edgeWitness : ∀ child parent : Fin k, (forest.role child).parent = some parent →
    ∃ edge : Fin k × Fin k,
      matchingForestWitnessAt t.nm (s.nr 90) child.val = (edge.1.val, edge.2.val) ∧
      (rep edge.1, rep edge.2) = (parent, child) ∧ tightOriginal s(edge.1, edge.2)
  natural : ∀ a, (a < s.nr 51 ∨ s.nr 51 + k + k + k ≤ a) →
    (a < s.nr 90 ∨ s.nr 90 + k + k ≤ a) → t.nm a = s.nm a
  real : t.rm = s.rm
  realRegisters : t.rr = s.rr
  fixed : ∀ r ≥ 30, t.nr r = s.nr r



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRefinement

/-! matching/ExpansionCommitRAM.lean -/
section RppSource_ExpansionCommitRAM
namespace VehicleRoutingSurvey.Routing

structure ExpansionPublication (s t : ArithmeticState) : Prop where
  representatives : ∀ v < s.nr 55, t.nm (s.nr 57 + v) =
    if s.nm (s.nr 79 + v) < s.nr 55 then s.nm (s.nr 79 + v) else s.nm (s.nr 57 + v)
  nodes : ∀ j < s.nr 19, t.nm (s.nr 74 + (expansionCycleRow s j).representative) = (expansionCycleRow s j).node
  natural : ∀ a, (a < s.nr 57 ∨ s.nr 57 + s.nr 55 ≤ a) →
    (∀ j < s.nr 19, a ≠ s.nr 74 + (expansionCycleRow s j).representative) → t.nm a = s.nm a
  real : t.rm = s.rm
  realRegisters : t.rr = s.rr
  fixed : ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 17, 25] → t.nr r = s.nr r







end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCommitRAM

/-! matching/MatchingExpansionAfterMembers.lean -/
section RppSource_MatchingExpansionAfterMembers
namespace VehicleRoutingSurvey.Routing

structure ExpansionInputLayout (k : ℕ) (s : ArithmeticState) : Prop where
  dimension : s.nr 55 = k
  one : s.nr 9 = 1
  zero : s.nr 14 = 0
  parents : s.nr 52 = s.nr 51 + k
  depths : s.nr 53 = s.nr 51 + k + k
  forestBelowRepresentatives : s.nr 51 + 3 * k ≤ s.nr 57
  representativesBelowScratch : s.nr 57 + k ≤ s.nr 79
  representativesBelowNodes : s.nr 57 + k ≤ s.nr 74
  nodesBelowWitnesses : s.nr 74 + k ≤ s.nr 90
  witnessesBelowPath : s.nr 90 + k + k ≤ s.nr 86
  pathBelowCycle : s.nr 86 + 3 * expansionRegisteredCycleLength s ≤ expansionRegisteredCycleBase s







end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionAfterMembers

/-! matching/MatchingGrowHandler.lean -/
section RppSource_MatchingGrowHandler
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

noncomputable def advancedEffectiveMemory (s : ArithmeticState) : ℕ → ℝ :=
  fun a => if s.nr 62 ≤ a ∧ a < s.nr 62 + s.nr 55 then
    effectivePotentialAfterDelta s (a - s.nr 62) else s.rm a



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowHandler

/-! matching/MatchingExpansionHandler.lean -/
section RppSource_MatchingExpansionHandler
namespace VehicleRoutingSurvey.Routing



structure ExpansionMemberMapResult (s t : ArithmeticState) (children : MatchingMemberTree) : Prop where
  selectedBase : t.nr 97 = s.nr 92
  values : ∀ p ∈ matchingMemberAssignments children, t.nm (s.nr 79 + p.1) = p.2
  sentinel : ∀ v < s.nr 55, v ∉ children.leaves → t.nm (s.nr 79 + v) = s.nr 55
  natural : ∀ a, outsideMatchingMemberScratch s a → t.nm a = s.nm a
  real : t.rm = s.rm
  realRegisters : t.rr = s.rr
  fixed : ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87, 97] → t.nr r = s.nr r







end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionHandler

/-! matching/AlternatingForestContract.lean -/
section RppSource_AlternatingForestContract
namespace VehicleRoutingSurvey.Routing

def blossomRepresentative {α : Type*} [DecidableEq α] (cycle : Finset α) (base x : α) : α :=
  if x ∈ cycle then base else x

/-- Remove the absorbed nodes from the alternating forest. The outer base remains, and
surviving inner nodes formerly reached from the cycle are reached from the base. -/
def AlternatingForestState.contract {α : Type*} [DecidableEq α] (state : AlternatingForestState α)
    (cycle : Finset α) (base : α) : AlternatingForestState α where
  role x := if x ∈ cycle ∧ x ≠ base then .unlabelled else
    match state.role x with
    | .inner p => .inner (blossomRepresentative cycle base p)
    | other => other
  depth := state.depth



end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestContract

/-! matching/ExpansionIncomingRAM.lean -/
section RppSource_ExpansionIncomingRAM
namespace VehicleRoutingSurvey.Routing

def expansionChildOf (s : ArithmeticState) (v : ℕ) : ℕ := s.nm (s.nr 79 + v)

def expansionRepRole (s : ArithmeticState) (representative : ℕ) : ℕ := s.nm (s.nr 51 + representative)















end VehicleRoutingSurvey.Routing
end RppSource_ExpansionIncomingRAM

/-! matching/ExpansionFreshRAM.lean -/
section RppSource_ExpansionFreshRAM
namespace VehicleRoutingSurvey.Routing

def freshExpansionOriginals (s : ArithmeticState) (count : ℕ) : List ℕ :=
  (List.range count).filter fun v => decide (expansionChildOf s v < s.nr 55) &&
    decide (expansionRepRole s (expansionChildOf s v) = 1)













end VehicleRoutingSurvey.Routing
end RppSource_ExpansionFreshRAM

/-! matching/ExpansionCacheRAM.lean -/
section RppSource_ExpansionCacheRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

structure ExpansionCacheFrame (s : ArithmeticState) : Prop where
  one : s.nr 9 = 1
  zero : s.nr 14 = 0
  dictionary : s.nr 58 ≤ s.nr 54
  buckets : s.nr 58 ≤ s.nr 65
  rates : s.nr 59 ≤ s.nr 60
  scores : s.nr 59 ≤ s.nr 66
  rolesBelowIncoming : s.nr 51 + s.nr 55 ≤ s.nr 58
  incomingBelowMembers : s.nr 58 + 2 * s.nr 55 ≤ s.nr 79
  cacheBelowWorkList : s.nr 58 ≤ s.nr 88
  workListBelowMembers : s.nr 88 + s.nr 55 ≤ s.nr 79

structure ExpansionCacheRestored (s t : ArithmeticState) : Prop where
  fresh : t.nr 99 = (freshExpansionOriginals s (s.nr 55)).length
  zero : t.nr 1 = 0
  identifiers : t.nr 3 = s.nr 58
  slacks : t.nr 4 = s.nr 59
  rates : t.nr 5 = s.nr 60
  rows : t.nr 8 = s.nr 61
  time : t.rr 15 = s.rr 15
  natural : ∀ a < s.nr 58, t.nm a = s.nm a
  real : ∀ a < s.nr 59, t.rm a = s.rm a
  fixed : ∀ r ≥ 50, r ≠ 99 → t.nr r = s.nr r





end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCacheRAM

/-! matching/MatchingCacheInsertion.lean -/
section RppSource_MatchingCacheInsertion
namespace VehicleRoutingSurvey.Routing

/-- Retain the earlier witness on ties, as in the cache instructions. -/
noncomputable def insertSlackCandidate {Event : Type*}
    (candidate : DualSlack Event) : Option (DualSlack Event) → Option (DualSlack Event)
  | none => some candidate
  | some old => if candidate.slack < old.slack then some candidate else some old











end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheInsertion

/-! matching/WeightedDeltaScan.lean -/
section RppSource_WeightedDeltaScan
namespace VehicleRoutingSurvey.Routing

def dualBoundIdentifier (initial : ArithmeticState) (index : ℕ) : ℕ :=
  initial.nm (initial.nr 3 + index)

def dualBoundPresent (initial : ArithmeticState) (index : ℕ) : Prop :=
  dualBoundIdentifier initial index ≠ 0 ∧ 0 < initial.rm (initial.nr 5 + index)

noncomputable def dualBoundRatio (initial : ArithmeticState) (index : ℕ) : ℝ :=
  initial.rm (initial.nr 4 + index) / initial.rm (initial.nr 5 + index)

def DualBoundMinimum (initial : ArithmeticState) (count : ℕ) (result : ArithmeticState) : Prop :=
  (result.nr 1 ≠ 0 → ∃ index < count, dualBoundPresent initial index ∧
      result.nr 1 = dualBoundIdentifier initial index ∧ result.rr 1 = dualBoundRatio initial index) ∧
  ∀ index < count, dualBoundPresent initial index → result.nr 1 ≠ 0 ∧ result.rr 1 ≤ dualBoundRatio initial index





def scanDualBoundBlock : List ArithmeticInstruction := countedLoopFromZero 9 7 8 considerDualBoundBlock



end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaScan

/-! matching/WeightedSlackAdvanceRAM.lean -/
section RppSource_WeightedSlackAdvanceRAM
namespace VehicleRoutingSurvey.Routing

/-- Subtract the selected dual step times one row's rate from its stored slack. -/
def advanceDualSlackCell : List ArithmeticInstruction :=
  [.natAdd 6 4 7, .natAdd 10 5 7, .realLoad 2 10, .realMul 2 1 2,
    .realLoad 3 6, .realSub 3 3 2, .realStore 6 3]





def advanceDualSlackBlock : List ArithmeticInstruction := countedLoopFromZero 9 7 8 advanceDualSlackCell





end VehicleRoutingSurvey.Routing
end RppSource_WeightedSlackAdvanceRAM

/-! matching/WeightedDeltaPhaseRAM.lean -/
section RppSource_WeightedDeltaPhaseRAM
namespace VehicleRoutingSurvey.Routing

def advanceDualSlackIfSelected : List ArithmeticInstruction :=
  appendBlock [.natConst 11 0] (branchOnUnequal 1 11 advanceDualSlackBlock)



def selectAndAdvanceDualSlackBlock : List ArithmeticInstruction :=
  appendBlock scanDualBoundBlock advanceDualSlackIfSelected





end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaPhaseRAM

/-! matching/MatchingCacheFootprint.lean -/
section RppSource_MatchingCacheFootprint
namespace VehicleRoutingSurvey.Routing

/-- A cache write lies in the contiguous range containing candidate data and
outer-pair buckets. Registry, witnesses, and effective potentials are outside. -/
structure MatchingCacheFootprint (k : ℕ) (s t : ArithmeticState) : Prop where
  natural : ∀ a, (a < s.nr 58 ∨ s.nr 65 + 2 * (k * k) ≤ a) → t.nm a = s.nm a
  real : ∀ a, (a < s.nr 59 ∨ s.nr 66 + k * k ≤ a) → t.rm a = s.rm a













end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheFootprint

/-! matching/MatchingExpansionGeometry.lean -/
section RppSource_MatchingExpansionGeometry
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem MatchingExpansionGeometry.rotatedPorts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)} {registry : MatchingExpansionChildPorts state B}
    {tree : MatchingMemberTree} {base : Fin k} (g : MatchingExpansionGeometry registry tree base) :
    registry.ports = (base :: g.children).toFinset := by
  ext v
  rw [g.ports, ← g.rotate, List.mem_toFinset, List.mem_toFinset, List.mem_rotate]

theorem MatchingExpansionGeometry.exposesPorts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} {registry : MatchingExpansionChildPorts state B} {tree : MatchingMemberTree}
    {base : Fin k} (g : MatchingExpansionGeometry registry tree base) (top : CompactTopMatching part)
    (baseFixed : part.representative base = base) (baseBlock : part.blocks.block base = B) :
    ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p := by
  have nodup : (base :: g.children).Nodup := by rw [← g.rotate, List.nodup_rotate]; exact g.distinct
  have size : (base :: g.children).length = g.cycle.length := by rw [← g.rotate, List.length_rotate]
  have odd := Nat.odd_iff.mp g.odd
  have even : g.children.length % 2 = 0 := by simp only [List.length_cons] at size; omega
  exact registry.ports_external_of_cycle top base g.children g.rotatedPorts (List.nodup_cons.mp nodup).2 even
    baseFixed baseBlock g.matched



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionGeometry

/-! matching/MatchingExpansionSelection.lean -/
section RppSource_MatchingExpansionSelection
namespace VehicleRoutingSurvey.Routing





structure MatchingSelectedExpansion {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (s : ArithmeticState)
    (B : Finset (Fin k)) where
  base : Fin k
  parent : Fin k
  ports : matchingOriginalGrowthEvent s = (base.val, k)
  classTag : matchingEventClass s = 2
  block : part.blocks.block base = B
  active : part.representative base = base
  representative : part.representativeOf positive B = base
  top : B ∈ Finset.univ.image part.blocks.block
  nontrivial : B.card ≠ 1
  inner : forest.role base = .inner parent











end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSelection

/-! matching/MatchingRebaseScratch.lean -/
section RppSource_MatchingRebaseScratch
namespace VehicleRoutingSurvey.Routing

/-- Reserve the compact original-to-child map and depth-first traversal stack.
The live registry cursor then points after both arrays. -/
def allocateMatchingCycleScratchBlock : List ArithmeticInstruction :=
  [.natAdd 79 68 14, .natAdd 80 79 55, .natAdd 6 55 55, .natAdd 6 6 55, .natAdd 68 80 6]




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseScratch

/-! matching/MatchingRebaseStack.lean -/
section RppSource_MatchingRebaseStack
namespace VehicleRoutingSurvey.Routing

/-- Reserve the work stack immediately after the member traversal stack. This block
is used once, after allocating the cycle scratch arrays. -/
def reserveMatchingRebaseJobsBlock : List ArithmeticInstruction :=
  [.natAdd 6 55 55, .natAdd 68 68 6]



def matchingRebaseJobAddress (s : ArithmeticState) (i : ℕ) : ℕ := s.nr 81 + 2 * i










end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseStack

/-! matching/MatchingRebaseWrite.lean -/
section RppSource_MatchingRebaseWrite
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing







def pushedMatchingRebaseJob (s : ArithmeticState) (node desired : ℕ) : ℕ → ℕ :=
  let a := matchingRebaseJobAddress s (s.nr 82)
  Function.update (Function.update s.nm a node) (a + 1) desired











/-- Queue one copy of each nontrivial child, left before right. -/
def queuedMatchingRebaseJob (s : ArithmeticState) (node desired : ℕ) : ArithmeticState :=
  if node = 0 then s else
    {s with nr := Function.update s.nr 82 (s.nr 82 + 1), nm := pushedMatchingRebaseJob s node desired}






end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseWrite

/-! matching/MatchingAugmentApply.lean -/
section RppSource_MatchingAugmentApply
namespace VehicleRoutingSurvey.Routing







def augmentationRepresentativeUpdate (s : ArithmeticState) (endpoint : ℕ) : ArithmeticState :=
  let old := s.nm (s.nr 57 + endpoint)
  let node := s.nm (s.nr 74 + old)
  let moved := Function.update (Function.update (Function.update s.nm (s.nr 89 + old) endpoint)
    (s.nr 74 + old) 0) (s.nr 74 + endpoint) node
  {s with nm := moved}














end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentApply

/-! matching/MatchingAugmentCrossingCell.lean -/
section RppSource_MatchingAugmentCrossingCell
namespace VehicleRoutingSurvey.Routing

/-- Original crossing edges, in the same two-word format read by the mate
installation block after blossom lifting. -/
def AugmentationCrossingArray {k : ℕ} (memory : ℕ → ℕ) (base : ℕ)
    (rows : List (Fin k × Fin k)) : Prop :=
  ∀ i, ∀ within : i < rows.length,
    memory (base + (i + i)) = rows[i].1.val ∧ memory (base + (i + i) + 1) = rows[i].2.val

























end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossingCell

/-! matching/MatchingAugmentCrossingLoop.lean -/
section RppSource_MatchingAugmentCrossingLoop
namespace VehicleRoutingSurvey.Routing

/-- The right trace is scanned forward with reversed witness orientation.
The left trace is scanned backward with the stored orientation. -/
def augmentationTraceIndex (forward : Bool) (start i : ℕ) : ℕ :=
  if forward then start + (i + i) else start - (i + i)



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossingLoop

/-! matching/MatchingAugmentTraceModel.lean -/
section RppSource_MatchingAugmentTraceModel
namespace VehicleRoutingSurvey.Routing





def augmentationWitnessStart (forward : Bool) (length : ℕ) : ℕ :=
  if forward then 1 else length - 2

theorem augmentationWitnessIndex_inBounds (forward : Bool) {length i : ℕ} (inside : i < length / 2) :
    augmentationTraceIndex forward (augmentationWitnessStart forward length) i < length := by
  cases forward <;> simp [augmentationWitnessStart, augmentationTraceIndex] <;> omega



def augmentationWitnessChildren {k : ℕ} (forward : Bool) (trail : List (Fin k)) : List (Fin k) :=
  List.ofFn fun i : Fin (trail.length / 2) =>
    trail[augmentationTraceIndex forward (augmentationWitnessStart forward trail.length) i.val]'(
      augmentationWitnessIndex_inBounds forward i.isLt)





/-- The output consists of the new left matches in root-to-trigger order,
the selected crossing edge, and the new right matches in trigger-to-root order. -/
def forestAugmentationCrossings {k : ℕ} (witness : Fin k → Fin k × Fin k) (trigger : Fin k × Fin k)
    (left right : List (Fin k)) : List (Fin k × Fin k) :=
  ((augmentationWitnessChildren false left).map witness ++ [trigger]) ++
    (augmentationWitnessChildren true right).map (fun v => (witness v).swap)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentTraceModel

/-! matching/AlternatingForestTraceRAM.lean -/
section RppSource_AlternatingForestTraceRAM
namespace VehicleRoutingSurvey.Routing

/-- A contiguous child-to-root list of compact vertex identifiers. -/
def ForestTraceArray {k : ℕ} (memory : ℕ → ℕ) (base : ℕ) (trail : List (Fin k)) : Prop :=
  ∀ i, ∀ within : i < trail.length, memory (base + i) = trail[i].val























end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTraceRAM

/-! matching/MatchingAugmentCrossings.lean -/
section RppSource_MatchingAugmentCrossings
namespace VehicleRoutingSurvey.Routing





/-- A list of top-level crossing edges awaiting recursive blossom lifting. -/
structure AugmentationCrossingsReady {k : ℕ} (rows : List (Fin k × Fin k))
    (s t : ArithmeticState) : Prop where
  count : t.nr 87 = rows.length
  base : t.nr 86 = s.nr 86
  array : AugmentationCrossingArray t.nm (s.nr 86) rows
  capacity : 2 * rows.length ≤ k
  natural : ∀ address, address < s.nr 86 ∨ s.nr 86 + 2 * rows.length ≤ address → t.nm address = s.nm address
  realRegisters : t.rr = s.rr
  realMemory : t.rm = s.rm
  fixed : ∀ r, r ∉ [3, 4, 5, 6, 7, 15, 16, 17, 18, 19, 87] → t.nr r = s.nr r





end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossings

/-! matching/MatchingAugmentInstallCell.lean -/
section RppSource_MatchingAugmentInstallCell
namespace VehicleRoutingSurvey.Routing



def installedAugmentationMateMemory (s : ArithmeticState) (ports : ℕ × ℕ) : ℕ → ℕ :=
  Function.update (Function.update s.nm (s.nr 50 + ports.1) ports.2) (s.nr 50 + ports.2) ports.1





def rebaseAugmentationEndpoint (s : ArithmeticState) (port : ℕ) : ArithmeticState :=
  let old := s.nm (s.nr 57 + port)
  let node := s.nm (s.nr 74 + old)
  queuedMatchingRebaseJob (augmentationRepresentativeUpdate s port) node port

/-- The exact memory and stack transition for one new original crossing edge. -/
def installAugmentationCrossingState (s : ArithmeticState) (ports : ℕ × ℕ) : ArithmeticState :=
  let installed := {s with nm := installedAugmentationMateMemory s ports}
  rebaseAugmentationEndpoint (rebaseAugmentationEndpoint installed ports.1) ports.2

















end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInstallCell

/-! matching/MatchingAugmentInstallMemory.lean -/
section RppSource_MatchingAugmentInstallMemory
namespace VehicleRoutingSurvey.Routing

/-- Ordered, disjoint arrays used during installation of the outer crossing edges. -/
structure AugmentationInstallLayout (k : ℕ) (s : ArithmeticState) : Prop where
  matesBeforeMap : s.nr 50 + k ≤ s.nr 57
  mapBeforeNodes : s.nr 57 + k ≤ s.nr 74
  nodesBeforePairs : s.nr 74 + k ≤ s.nr 86
  pairsBeforeRepresentativeWork : s.nr 86 + k ≤ s.nr 89
  representativeWorkBeforeJobs : s.nr 89 + k ≤ s.nr 81

def AugmentationInstallUnwritten (k : ℕ) (s : ArithmeticState) (address : ℕ) : Prop :=
  (address < s.nr 50 ∨ s.nr 50 + k ≤ address) ∧
  (address < s.nr 74 ∨ s.nr 74 + k ≤ address) ∧
  (address < s.nr 89 ∨ s.nr 89 + k ≤ address) ∧
  (address < s.nr 81 ∨ s.nr 81 + 2 * k ≤ address)



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInstallMemory

/-! matching/MatchingAugmentInstallRAM.lean -/
section RppSource_MatchingAugmentInstallRAM
namespace VehicleRoutingSurvey.Routing

def installAugmentationCrossingRows {k : ℕ} (s : ArithmeticState) (rows : List (Fin k × Fin k)) :
    ArithmeticState :=
  rows.foldl (fun old pair => installAugmentationCrossingState old (pair.1.val, pair.2.val)) s





end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInstallRAM

/-! matching/MatchingAugmentPreRebase.lean -/
section RppSource_MatchingAugmentPreRebase
namespace VehicleRoutingSurvey.Routing











/-- The stack is empty and the original-to-new representative map starts as identity. -/
def augmentationCrossingSeed (s : ArithmeticState) (k : ℕ) : ArithmeticState :=
  {s with
    nr := Function.update (Function.update s.nr 81 (s.nr 80 + 3 * k)) 82 0
    nm := fun address => if s.nr 89 ≤ address ∧ address < s.nr 89 + k then address - s.nr 89 else s.nm address}



def remappedAugmentationMemory (s model : ArithmeticState) (k : ℕ) : ℕ → ℕ :=
  fun address => if s.nr 57 ≤ address ∧ address < s.nr 57 + k then
    model.nm (s.nr 89 + model.nm address) else model.nm address

def AugmentationPreRebaseUnwritten (k : ℕ) (s : ArithmeticState) (address : ℕ) : Prop :=
  AugmentationInstallUnwritten k (augmentationCrossingSeed s k) address ∧
    (address < s.nr 57 ∨ s.nr 57 + k ≤ address)

/-- Exact machine state just before recursive rebasing. The original
occurrence data below the matching workspace survives this phase. -/
structure AugmentationPreRebaseReady {k : ℕ} (rows : List (Fin k × Fin k))
    (s t : ArithmeticState) : Prop where
  one : t.nr 9 = 1
  zero : t.nr 14 = 0
  jobs : t.nr 82 = (installAugmentationCrossingRows (augmentationCrossingSeed s k) rows).nr 82
  bounded : t.nr 82 ≤ 2 * rows.length
  stackBase : t.nr 81 = s.nr 80 + 3 * k
  memory : t.nm = remappedAugmentationMemory s (installAugmentationCrossingRows (augmentationCrossingSeed s k) rows) k
  untouched : ∀ address, AugmentationPreRebaseUnwritten k s address → t.nm address = s.nm address
  preservedPrefix : ∀ address < s.nr 50, t.nm address = s.nm address
  realRegisters : t.rr = s.rr
  realMemory : t.rm = s.rm
  fixed : ∀ r, r ∉ [0, 6, 9, 12, 13, 14, 15, 22, 26, 44, 81, 82] → t.nr r = s.nr r



end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPreRebase

/-! matching/MatchingRebaseNodeProof.lean -/
section RppSource_MatchingRebaseNodeProof
namespace VehicleRoutingSurvey.Routing



















/-- The physical child index of an endpoint of a pair following the new free child. -/
def matchingRebaseChildIndex (length free pair : ℕ) (second : Bool) : ℕ :=
  (free + (2 * pair + (if second then 2 else 1))) % length






















end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseNodeProof

/-! matching/MatchingRebaseQueue.lean -/
section RppSource_MatchingRebaseQueue
namespace VehicleRoutingSurvey.Routing

/-- Count the nontrivial registered nodes in an ordered forest. -/
def MatchingMemberTree.registeredNodes : MatchingMemberTree → ℕ
  | .nil => 0
  | .leaf _ siblings => siblings.registeredNodes
  | .blossom _ _ children siblings => 1 + children.registeredNodes + siblings.registeredNodes



structure MatchingRebaseTask where
  node : ℕ
  port : ℕ
  children : MatchingMemberTree

def MatchingRebaseTask.work (task : MatchingRebaseTask) : ℕ := 1 + task.children.registeredNodes

def matchingRebaseQueueWork (tasks : List MatchingRebaseTask) : ℕ := (tasks.map MatchingRebaseTask.work).sum






















end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseQueue

/-! matching/MatchingRebaseTaskBounds.lean -/
section RppSource_MatchingRebaseTaskBounds
namespace VehicleRoutingSurvey.Routing







def matchingRebaseTaskLeaves (tasks : List MatchingRebaseTask) : List ℕ :=
  tasks.flatMap fun task => task.children.leaves

























end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseTaskBounds

/-! matching/MatchingRebaseFrontier.lean -/
section RppSource_MatchingRebaseFrontier
namespace VehicleRoutingSurvey.Routing

def MatchingRebaseTask.registryIds (task : MatchingRebaseTask) : List ℕ :=
  task.node :: task.children.registryIds

def matchingRebaseQueueIds (tasks : List MatchingRebaseTask) : List ℕ :=
  tasks.flatMap MatchingRebaseTask.registryIds












end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseFrontier

/-! matching/MatchingRebaseQueueMemory.lean -/
section RppSource_MatchingRebaseQueueMemory
namespace VehicleRoutingSurvey.Routing

/-- The work stack stores the stable registry ID and original port of each task,
in order from the bottom to the top of the stack. -/
structure MatchingRebaseQueueEncoding (s : ArithmeticState) (tasks : List MatchingRebaseTask) : Prop where
  count : s.nr 82 = tasks.length
  words : ∀ i (inside : i < tasks.length),
    (s.nm (matchingRebaseJobAddress s i), s.nm (matchingRebaseJobAddress s i + 1)) =
      (tasks[i].node, tasks[i].port)












end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseQueueMemory

/-! matching/MatchingRebaseGeometry.lean -/
section RppSource_MatchingRebaseGeometry
namespace VehicleRoutingSurvey.Routing



/-- Original endpoint witnesses in physical cyclic order. The first endpoint
is in the current row's subtree and the second is in the successor's subtree. -/
structure MatchingRebaseCycleGeometry (s : ArithmeticState) (children : MatchingMemberTree) where
  edge : ℕ → ℕ × ℕ
  source : ∀ i (hi : i < (children.jobs none).length),
    (edge i).1 ∈ ((children.jobs none)[i]).tree.leaves
  target : ∀ i (hi : i < (children.jobs none).length),
    (edge i).2 ∈ ((children.jobs none)[(i + 1) % (children.jobs none).length]'(Nat.mod_lt _ (by omega))).tree.leaves
  row : ∀ i < children.arity, let child := matchingCycleChildAt s.nm (s.nm (s.nr 77 + s.nr 22) + 4 * i)
    (child.endpointA, child.endpointB) = edge i ∨ (child.endpointA, child.endpointB) = (edge i).swap








end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseGeometry

/-! matching/MatchingRebaseArchive.lean -/
section RppSource_MatchingRebaseArchive
namespace VehicleRoutingSurvey.Routing



def matchingRebaseHeaderArea (s : ArithmeticState) (a : ℕ) : Prop :=
  s.nr 50 + s.nr 55 ≤ a ∧ a < s.nr 79

def matchingRebaseRowArea (s : ArithmeticState) (node a : ℕ) : Prop :=
  matchingCycleRecordStart s node ≤ a ∧ a < matchingCycleRecordEnd s node

def matchingRebaseRecordArea (s : ArithmeticState) (ids : List ℕ) (a : ℕ) : Prop :=
  matchingRebaseHeaderArea s a ∨ ∃ n ∈ ids, matchingRebaseRowArea s n a

/-- Immutable cycle description at the beginning of an augmentation. Later
steps need only its headers and rows as long as its subtree remains pending. -/
structure MatchingArchivedCycle (s : ArithmeticState) (node : ℕ) (children : MatchingMemberTree) where
  members : MatchingMemberRoot (matchingRebaseNodeState s node) children
  odd : Odd children.arity
  distinct : (children.rootKeys.map Prod.fst).Nodup
  geometry : MatchingRebaseCycleGeometry (matchingRebaseNodeState s node) children
  footprint : (MatchingMemberTree.blossom 0 node children .nil).readable s.nm (s.nr 77) (s.nr 78)
    (fun a => matchingRebaseRecordArea s (node :: children.registryIds) a ∧ outsideMatchingMemberScratch s a)

/-- The live subtree for every registered node reachable from a pending
augmentation request, including each registered child of such a node. -/
structure MatchingRebaseArchive (s : ArithmeticState) where
  live : ℕ → MatchingMemberTree → Prop
  record : ∀ n c, live n c → MatchingArchivedCycle s n c
  allocated : ∀ n c, live n c → 0 < n ∧ n < s.nr 76
  child : ∀ n c, live n c → ∀ job ∈ c.jobs none, ∀ sub, job.children = some sub → live job.node sub
  headers : ∀ n c, live n c → matchingRebaseHeaderArea s (s.nr 77 + n) ∧
    matchingRebaseHeaderArea s (s.nr 78 + n)
  order : MatchingCycleRecordOrder s
  mates : s.nr 50 + s.nr 55 ≤ s.nr 79
  mapWalk : s.nr 79 + s.nr 55 ≤ s.nr 80
  walkJobs : s.nr 80 + 3 * s.nr 55 ≤ s.nr 81
  jobsRecords : s.nr 81 + 2 * s.nr 55 ≤ matchingRebaseScratchEnd s






end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseArchive

/-! matching/MatchingBlossomRegistry.lean -/
section RppSource_MatchingBlossomRegistry
namespace VehicleRoutingSurvey.Routing





/-- The preceding pair cache ends at its real base plus (k^2). This computes
the registry dimensions without multiplying natural registers. Identifier zero
represents a singleton. The live allocation cursor for cycle records is register 68. -/
def placeMatchingBlossomRegistry : List ArithmeticInstruction :=
  [.natConst 14 0, .natConst 76 1, .natSub 79 69 66,
   .natAdd 80 79 79, .natAdd 80 80 79, .natAdd 80 80 76,
   .natAdd 74 68 14, .natAdd 75 69 14, .natAdd 77 74 55,
   .natAdd 78 77 80, .natAdd 68 78 80, .natAdd 69 75 80]





 def clearBlossomRegistryRepresentative : List ArithmeticInstruction :=
  [.natAdd 6 74 7, .natStore 6 14]

def initializeMatchingBlossomRegistry : List ArithmeticInstruction :=
  appendBlock placeMatchingBlossomRegistry
    (countedLoopFromZero 9 7 55 clearBlossomRegistryRepresentative)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingBlossomRegistry

/-! matching/MatchingWorkspace.lean -/
section RppSource_MatchingWorkspace
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing





/-- Register 32 initially holds the compact dimension and 31 the original
vertex map. Registers 63 and 64 give the first free addresses. -/
def allocateMatchingWorkspaceBlock : List ArithmeticInstruction :=
  [.natConst 66 0, .natConst 34 1, .natAdd 55 32 66, .natAdd 56 31 66,
   .natAdd 50 63 66, .natAdd 51 50 55, .natAdd 52 51 55, .natAdd 53 52 55,
   .natAdd 57 53 55, .natAdd 58 57 55,
   .natAdd 67 55 55, .natAdd 67 67 55, .natAdd 54 58 67,
   .natAdd 68 54 67, .natAdd 68 68 67,
   .natAdd 62 64 66, .natAdd 59 62 55, .natAdd 60 59 67, .natAdd 69 60 67,
   .natAdd 61 67 66, .natAdd 31 67 67, .natAdd 31 31 34,
   .natAdd 3 58 66, .natAdd 4 59 66, .natAdd 5 60 66, .natAdd 8 61 66,
   .natConst 1 0, .natConst 9 1, .natConst 32 0, .natConst 33 1,
   .natConst 41 1, .natConst 42 0, .natConst 70 0]








end VehicleRoutingSurvey.Routing
end RppSource_MatchingWorkspace

/-! matching/MatchingVertexStart.lean -/
section RppSource_MatchingVertexStart
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

 def initializeMatchingVertexCell : List ArithmeticInstruction :=
  [.natAdd 0 50 65, .natStore 0 55,
   .natAdd 0 51 65, .natStore 0 34,
   .natAdd 0 52 65, .natStore 0 55,
   .natAdd 0 53 65, .natStore 0 66,
   .natAdd 0 57 65, .natStore 0 65,
   .natAdd 0 58 65, .natStore 0 66,
   .realConst 2 0, .natAdd 0 62 65, .realStore 0 2,
   .natAdd 42 42 70, .natSub 70 34 70]

/-- Initialize the exposed vertices, singleton blocks, and zero potentials. -/
def initializeMatchingVerticesBlock : List ArithmeticInstruction :=
  countedLoopFromZero 34 65 55 initializeMatchingVertexCell












end VehicleRoutingSurvey.Routing
end RppSource_MatchingVertexStart

/-! matching/MatchingSeedRow.lean -/
section RppSource_MatchingSeedRow
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing





 def loadMatchingSeedCandidate : List ArithmeticInstruction :=
  [.natAdd 0 73 34, .natAdd 2 71 73, .realLoad 0 2,
   .natBranch 72 73 4 6, .natBranch 73 72 5 6, .natConst 0 0]

 def considerMatchingSeedCandidate : List ArithmeticInstruction :=
  appendBlock loadMatchingSeedCandidate mergeSlackEntryBlock









 def startMatchingSeedRow : List ArithmeticInstruction :=
  [.natAdd 71 21 72, .natLoad 71 71, .natAdd 71 20 71, .natConst 1 0]

/-- Find the least metric edge in one row that does not use the diagonal.
Register 72 contains the row. The compact offsets and costs start at 21 and 20. -/
def findMatchingSeedRowBlock : List ArithmeticInstruction :=
  appendBlock startMatchingSeedRow (countedLoopFromZero 34 73 55 considerMatchingSeedCandidate)




end VehicleRoutingSurvey.Routing
end RppSource_MatchingSeedRow

/-! matching/MatchingSeedCache.lean -/
section RppSource_MatchingSeedCache
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory







 def prepareMatchingSeedStore : List ArithmeticInstruction :=
  [.natConst 14 0, .natAdd 18 72 14, .natAdd 15 72 14, .natSub 16 1 9,
   .realConst 3 0, .realAdd 0 1 3, .realConst 4 2]

def storeMatchingSeedRowBlock : List ArithmeticInstruction :=
  appendBlock prepareMatchingSeedStore storeMatchingCandidateCell



 def buildMatchingSeedRow : List ArithmeticInstruction :=
  appendBlock findMatchingSeedRowBlock storeMatchingSeedRowBlock









def seedMatchingEventCacheBlock : List ArithmeticInstruction :=
  appendBlock (countedLoopFromZero 34 72 55 buildMatchingSeedRow) [.natConst 1 0]








end VehicleRoutingSurvey.Routing
end RppSource_MatchingSeedCache

/-! matching/MatchingPairSeed.lean -/
section RppSource_MatchingPairSeed
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- The occupied singleton pair cache starts with the original metric costs and cumulative
dual shift zero. A diagonal column has no edge and uses the dimension as its endpoint code. -/
 def seedMatchingPairCell : List ArithmeticInstruction :=
  [.natAdd 79 75 75, .natAdd 79 78 79, .natAdd 80 74 81,
   .natBranch 74 75 4 6, .natBranch 75 74 5 6, .natAdd 80 55 81,
   .natStore 79 80, .natAdd 79 79 34, .natStore 79 75,
   .natAdd 79 77 75, .realLoad 16 79, .natAdd 79 76 75, .realStore 79 16]

 def prepareMatchingPairRow : List ArithmeticInstruction :=
  [.natAdd 76 21 74, .natLoad 76 76, .natAdd 77 20 76,
   .natAdd 78 76 76, .natAdd 78 65 78, .natAdd 76 66 76]

 def seedMatchingPairRow : List ArithmeticInstruction :=
  appendBlock prepareMatchingPairRow (countedLoopFromZero 34 75 55 seedMatchingPairCell)

 def prepareMatchingPairs : List ArithmeticInstruction :=
  [.natConst 81 0, .natAdd 65 68 81, .natAdd 66 69 81, .realConst 15 0]

 def finishMatchingPairs : List ArithmeticInstruction :=
  [.natBranch 55 81 6 1, .natSub 76 55 34, .natAdd 76 21 76, .natLoad 76 76,
   .natAdd 76 76 55, .jump 7, .natConst 76 0,
   .natAdd 69 66 76, .natAdd 76 76 76, .natAdd 68 65 76]

/-- Reserve both pair-cache arrays and seed them by sweeping the compact cost matrix. -/
def seedMatchingPairCacheBlock : List ArithmeticInstruction :=
  appendBlock prepareMatchingPairs
    (appendBlock (countedLoopFromZero 34 74 55 seedMatchingPairRow) finishMatchingPairs)


























end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairSeed

/-! matching/MatchingPrelude.lean -/
section RppSource_MatchingPrelude
namespace VehicleRoutingSurvey.Routing

def initializeCompactMatchingArraysBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock allocateMatchingWorkspaceBlock initializeMatchingVerticesBlock)
    clearMatchingCandidatesBlock

/-- Prepare all tables for the first augmenting search. The pair buckets are initialized last,
which sets the cumulative dual shift for the newly seeded costs. -/
def prepareCompactMatchingBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock initializeCompactMatchingArraysBlock seedMatchingEventCacheBlock)
    seedMatchingPairCacheBlock













end VehicleRoutingSurvey.Routing
end RppSource_MatchingPrelude

/-! matching/MatchingForestTraceSetup.lean -/
section RppSource_MatchingForestTraceSetup
namespace VehicleRoutingSurvey.Routing



/-- Allocate trace scratch above the existing blossom registry. -/
def allocateForestTraceScratchBlock : List ArithmeticInstruction :=
  [.natConst 49 0, .natAdd 83 68 49, .natAdd 84 83 55, .natAdd 85 84 55, .natAdd 68 85 55]















end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestTraceSetup

/-! matching/MatchingContractRowsRAM.lean -/
section RppSource_MatchingContractRowsRAM
namespace VehicleRoutingSurvey.Routing

/-- Reserve the flat absorbed-outer list and two marking arrays after the existing
forest scratch. Only touched records or cleared marking arrays are read. -/
def allocateMatchingContractionScratch : List ArithmeticInstruction :=
  [.natConst 23 0, .natAdd 86 68 23, .natAdd 88 86 55, .natAdd 89 88 55, .natAdd 68 89 55]

















def tracedOuterReps (s : ArithmeticState) (i : ℕ) : List ℕ :=
  ((List.range i).filter (fun j => decide (tracedRepresentativeOuter s j))).map (tracedRepresentative s)









def traceOuterRowsAt (s : ArithmeticState) (trace count : ℕ) : List ℕ :=
  tracedOuterReps {s with nr := Function.update s.nr 18 trace} count

def absorbedMatchingOuterRows (s : ArithmeticState) : List ℕ :=
  [s.nr 12] ++ traceOuterRowsAt s (s.nr 83) (s.nr 13) ++ traceOuterRowsAt s (s.nr 84) (s.nr 14)







end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractRowsRAM

/-! matching/MatchingAuxiliaryInit.lean -/
section RppSource_MatchingAuxiliaryInit
namespace VehicleRoutingSurvey.Routing

/-- Install the empty blossom registry and reserve separate space for traces, original
parent-edge witnesses, and the temporary contraction or augmentation records. -/
def initializeMatchingAuxiliaryBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock initializeMatchingBlossomRegistry
    allocateForestTraceScratchBlock) allocateMatchingForestWitnessArray) allocateMatchingContractionScratch






end VehicleRoutingSurvey.Routing
end RppSource_MatchingAuxiliaryInit

/-! matching/MatchingInitialization.lean -/
section RppSource_MatchingInitialization
namespace VehicleRoutingSurvey.Routing

/-- Set aside the descendant map, descendant stack, and disjoint rebase stack
before registering any variable-length cycle records. -/
def allocateMatchingStageScratchBlock : List ArithmeticInstruction :=
  appendBlock [.natConst 14 0] (appendBlock allocateMatchingCycleScratchBlock reserveMatchingRebaseJobsBlock)



/-- Allocate the compact matching input, event rows, registry, and the disjoint
scratch ranges used by the timed inner search. -/
def initializeWeightedMatchingBlock : List ArithmeticInstruction :=
  appendBlock prepareCompactMatchingBlock (appendBlock initializeMatchingAuxiliaryBlock allocateMatchingStageScratchBlock)




end VehicleRoutingSurvey.Routing
end RppSource_MatchingInitialization

/-! matching/MatchingAugmentArchiveFrame.lean -/
section RppSource_MatchingAugmentArchiveFrame
namespace VehicleRoutingSurvey.Routing

/-- The augmentation prefix may move top IDs, install pairs, remap
representatives, and initialize its work stack. The headers and records of
each allocated node keep their original locations and contents. -/
structure MatchingAugmentArchiveFrame (s t : ArithmeticState) : Prop where
  fixed : ∀ r ∈ ([50,55,68,76,77,78,79,80] : List ℕ), t.nr r = s.nr r
  headers : ∀ n, 0 < n → n < s.nr 76 →
    t.nm (s.nr 77+n) = s.nm (s.nr 77+n) ∧ t.nm (s.nr 78+n) = s.nm (s.nr 78+n)
  rows : ∀ n, 0 < n → n < s.nr 76 → ∀ a, matchingRebaseRowArea s n a → t.nm a = s.nm a






end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentArchiveFrame

/-! matching/AlternatingForestAncestorRAM.lean -/
section RppSource_AlternatingForestAncestorRAM
namespace VehicleRoutingSurvey.Routing

/-- The selected vertex and its positions on both child-to-root chains. If
there is no shared vertex, both positions are the full chain lengths. -/
structure ForestTraceSplit {k : ℕ} (left right : List (Fin k)) (shared : Option (Fin k))
    (leftLength rightLength : ℕ) : Prop where
  first : shared = firstSharedAncestor left right
  positions : match shared with
    | none => leftLength = left.length ∧ rightLength = right.length
    | some v => ∃ (li : leftLength < left.length) (ri : rightLength < right.length),
        left[leftLength] = v ∧ right[rightLength] = v



















end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAncestorRAM

/-! matching/MatchingForestTrace.lean -/
section RppSource_MatchingForestTrace
namespace VehicleRoutingSurvey.Routing







/-- The full traces, common ancestor, and the exclusive prefix lengths for
the ensuing contraction or augmentation. Only the three scratch arrays and
the listed temporary registers can change. -/
structure MatchingForestTraceResult {k : ℕ} (forest : AlternatingForestState (Fin k))
    (u v : Fin k) (base : ℕ) (s t : ArithmeticState) : Prop where
  leftCount : t.nr 10 = (forest.traceToRoot u).length
  rightCount : t.nr 11 = (forest.traceToRoot v).length
  left : ForestTraceArray t.nm (s.nr 83) (forest.traceToRoot u)
  right : ForestTraceArray t.nm (s.nr 84) (forest.traceToRoot v)
  shared : t.nr 12 = ((forest.commonAncestor u v).map Fin.val).getD k
  split : ForestTraceSplit (forest.traceToRoot u) (forest.traceToRoot v)
    (forest.commonAncestor u v) (t.nr 13) (t.nr 14)
  natural : ∀ a, a < base ∨ base + 3 * k ≤ a → t.nm a = s.nm a
  registers : ∀ r, r ∉ [2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14] → t.nr r = s.nr r
  realRegisters : t.rr = s.rr
  realMemory : t.rm = s.rm





end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestTrace

/-! matching/MatchingAugmentCrossingSemantics.lean -/
section RppSource_MatchingAugmentCrossingSemantics
namespace VehicleRoutingSurvey.Routing



def chooseAugmentationRepresentatives {k : ℕ} (original replacements : Fin k → Fin k)
    (ports : Fin k × Fin k) : Fin k → Fin k :=
  Function.update (Function.update replacements (original ports.1) ports.1) (original ports.2) ports.2









end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossingSemantics

/-! matching/MatchingAugmentRebaseJobs.lean -/
section RppSource_MatchingAugmentRebaseJobs
namespace VehicleRoutingSurvey.Routing

structure AugmentationRebaseModel (k : ℕ) where
  nodes : Fin k → ℕ
  jobs : List (ℕ × Fin k)

def AugmentationRebaseModel.move {k : ℕ} (model : AugmentationRebaseModel k)
    (old port : Fin k) : AugmentationRebaseModel k :=
  let node := model.nodes old
  ⟨Function.update (Function.update model.nodes old 0) port node,
    if node = 0 then model.jobs else model.jobs ++ [(node, port)]⟩

def AugmentationRebaseModel.crossing {k : ℕ} (original : Fin k → Fin k)
    (model : AugmentationRebaseModel k) (ports : Fin k × Fin k) : AugmentationRebaseModel k :=
  (model.move (original ports.1) ports.1).move (original ports.2) ports.2









end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentRebaseJobs

/-! matching/MatchingAugmentJobUniqueness.lean -/
section RppSource_MatchingAugmentJobUniqueness
namespace VehicleRoutingSurvey.Routing

def selectedAugmentationPorts {k : ℕ} (rows : List (Fin k × Fin k)) : List (Fin k) :=
  rows.flatMap fun pair => [pair.1, pair.2]



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentJobUniqueness

/-! matching/MatchingAugmentCutPort.lean -/
section RppSource_MatchingAugmentCutPort
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The matching internal to a blossom is complete except at its port.
A globally matched port has its other endpoint outside the blossom. -/
def matchingCutPort {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (next : CompactMatchingPrimalDual k cost) (B : Finset (Fin k)) (p : Fin k) : Prop :=
  p ∈ B ∧ ∀ e ∈ next.edges, p ∈ e → ¬ (∀ v ∈ e, v ∈ B)



/-- The requested port is determined by the new global matching and the
old permanent node ID, independent of which ancestor supplies the task. -/
noncomputable def matchingAugmentNodePort {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (next : CompactMatchingPrimalDual k cost) (cuts : Finset (Finset (Fin k)))
    (node : Finset (Fin k) → ℕ) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p : Fin k, ∃ B ∈ cuts, node B = n ∧ matchingCutPort next B p then h.choose.val else 0




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCutPort

/-! matching/MatchingRebaseLivePorts.lean -/
section RppSource_MatchingRebaseLivePorts
namespace VehicleRoutingSurvey.Routing

/-- The desired original belongs to the free child. The pair edges of the
rotated cyclic list determine the other child bases, all as actual originals. -/
structure MatchingCycleLiftPorts {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)} (cycle : MatchingLiveCycle state node B) (desired : Fin k) where
  free : Fin cycle.geometry.cycle.length
  choose : Fin k → Fin k
  exposed : choose (cycle.geometry.cycle.get free) = desired
  members : ∀ p ∈ cycle.ports.ports, choose p ∈ cycle.ports.block p
  pairs : ∀ i < (cycle.geometry.cycle.length - 1) / 2,
    let index (b : Bool) : Fin cycle.geometry.cycle.length :=
      ⟨matchingRebaseChildIndex cycle.geometry.cycle.length free.val i b, Nat.mod_lt _ (Nat.zero_lt_of_lt free.isLt)⟩
    (choose (cycle.geometry.cycle.get (index false)), choose (cycle.geometry.cycle.get (index true))) =
      cycle.geometry.edges (index false)




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseLivePorts

/-! matching/BlossomMatchingLift.lean -/
section RppSource_BlossomMatchingLift
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



/-- Lift a matching between child blossoms by installing their internal matchings and
the chosen original crossing edges. -/
def liftMatchingAcrossBlocks {n : ℕ} {Index : Type*} [DecidableEq Index]
    (groups : Finset Index) (internal : Index → Finset (Sym2 (Fin n)))
    (crossing : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  groups.biUnion internal ∪ crossing







end VehicleRoutingSurvey.Routing
end RppSource_BlossomMatchingLift

/-! matching/MatchingRebaseRecursivePrimal.lean -/
section RppSource_MatchingRebaseRecursivePrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

def matchingLiftTreeEdges {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)} {desired : Fin k} {e : MatchingLiveCycle state node B}
    (ports : MatchingCycleLiftPorts e desired) (inner : Fin k → Finset (Sym2 (Fin k))) : Finset (Sym2 (Fin k)) :=
  liftMatchingAcrossBlocks e.geometry.cycle.toFinset inner
    ((rematchBlossomCycle e.geometry.cycle ports.free.val).image (Sym2.map ports.choose))

/-- The actual choice at every recursive cut, including which original edge
joins the new ports of each adjacent matched child pair. -/
inductive MatchingCycleLiftDerivation {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {node : Finset (Fin k) → ℕ} (lookup : ∀ B ∈ state.cuts, MatchingLiveCycle state node B) :
    (B : Finset (Fin k)) → (desired : Fin k) → Finset (Sym2 (Fin k)) → Prop
  | join {B desired} (live : B ∈ state.cuts) (ports : MatchingCycleLiftPorts (lookup B live) desired)
      (inner : Fin k → Finset (Sym2 (Fin k)))
      (rootMatching : IsPerfectMatchingOn (B.erase desired) (matchingLiftTreeEdges ports inner))
      (childMatching : ∀ p ∈ (lookup B live).ports.ports,
        IsPerfectMatchingOn (((lookup B live).ports.block p).erase (ports.choose p)) (inner p))
      (single : ∀ p ∈ (lookup B live).ports.ports, ((lookup B live).ports.block p).card = 1 → inner p = ∅)
      (down : ∀ p ∈ (lookup B live).ports.ports, ((lookup B live).ports.block p).card ≠ 1 →
        MatchingCycleLiftDerivation lookup ((lookup B live).ports.block p) (ports.choose p) (inner p)) :
      MatchingCycleLiftDerivation lookup B desired (matchingLiftTreeEdges ports inner)

def matchingLiftTight {k : ℕ} {cost : Fin k → Fin k → ℝ} (state : CompactMatchingPrimalDual k cost)
    (edge : Sym2 (Fin k)) : Prop :=
  oddCutDualEdgeValue state.cuts state.potential state.cutDual edge = edgeCost cost edge






end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseRecursivePrimal

/-! matching/MatchingRebaseTaskTransition.lean -/
section RppSource_MatchingRebaseTaskTransition
namespace VehicleRoutingSurvey.Routing

def matchingRebasePortAt (c : MatchingMemberTree) (choose : MatchingMemberJob → ℕ) (index : ℕ) : ℕ :=
  if h : index < (c.jobs none).length then choose (c.jobs none)[index] else 0






end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseTaskTransition

/-! matching/MatchingRebaseCoverage.lean -/
section RppSource_MatchingRebaseCoverage
namespace VehicleRoutingSurvey.Routing

/-- A pending subtree has to fix only its interior vertices. Its requested
port has already been attached by a higher-level crossing edge. -/
def MatchingRebaseTask.needs (task : MatchingRebaseTask) (v : ℕ) : Prop :=
  v ∈ task.children.leaves ∧ v ≠ task.port





end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseCoverage

/-! matching/MatchingRebaseRowTransition.lean -/
section RppSource_MatchingRebaseRowTransition
namespace VehicleRoutingSurvey.Routing

/-- Read all four row words at the fixed addresses allocated before augmentation. -/
def matchingRebaseRowsAt (base s : ArithmeticState) (n i : ℕ) : MatchingCycleChild :=
  matchingCycleChildAt s.nm (matchingCycleRecordStart base n + 4*i)






end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseRowTransition

/-! matching/MatchingRebaseLiftTarget.lean -/
section RppSource_MatchingRebaseLiftTarget
namespace VehicleRoutingSurvey.Routing

/-- The original port exposed by each child in a mathematical blossom lift. -/
def MatchingMemberJob.liftPort (port : ℕ → ℕ) (job : MatchingMemberJob) : ℕ :=
  match job.children with
  | none => job.representative
  | some _ => port job.node

/-- A proposed lifted matching specifies one exposed original per registered
blossom. Its free child inherits that port. All the other children are joined
in pairs by both directions of the corresponding original edge. -/
structure MatchingRebaseLiftTarget {base : ArithmeticState} (archive : MatchingRebaseArchive base)
    (target : ℕ → ℕ) where
  port : ℕ → ℕ
  inherits : ∀ n c, archive.live n c → ∀ free (hf : free < (c.jobs none).length),
    port n ∈ ((c.jobs none)[free]'hf).tree.leaves → matchingRebasePortAt c (MatchingMemberJob.liftPort port) free = port n
  pairs : ∀ n c (known : archive.live n c) free (hf : free < (c.jobs none).length),
    port n ∈ ((c.jobs none)[free]'hf).tree.leaves → ∀ i < (c.arity - 1) / 2,
      let left := matchingRebaseChildIndex c.arity free i false
      let right := matchingRebaseChildIndex c.arity free i true
      let edge := (archive.record _ _ known).geometry.edge left
      (matchingRebasePortAt c (MatchingMemberJob.liftPort port) left,
        matchingRebasePortAt c (MatchingMemberJob.liftPort port) right) = edge ∧
        target edge.1 = edge.2 ∧ target edge.2 = edge.1








end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseLiftTarget

/-! matching/MatchingAugmentDerivedCut.lean -/
section RppSource_MatchingAugmentDerivedCut
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



def matchingAugmentDerivedCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ}
    (lookup : ∀ B ∈ old.cuts, MatchingLiveCycle old node B) (next : CompactMatchingPrimalDual k cost)
    (B : Finset (Fin k)) : Prop :=
  ∃ (p : Fin k) (_ : p ∈ B) (E : Finset (Sym2 (Fin k))), E ⊆ next.edges ∧ MatchingCycleLiftDerivation lookup B p E




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentDerivedCut

/-! matching/MatchingAugmentLiveQueue.lean -/
section RppSource_MatchingAugmentLiveQueue
namespace VehicleRoutingSurvey.Routing





/-- Data at the transition from crossing installation to recursive lifting. -/
structure MatchingPreparedRebase (base : ArithmeticState) (jobs : List MatchingRebaseTask) where
  registry : MatchingRebaseArchive base
  queue : MatchingRebaseQueueEncoding base jobs
  tasks : ∀ t ∈ jobs, registry.live t.node t.children ∧ t.port ∈ t.children.leaves
  distinct : (matchingRebaseTaskLeaves jobs).Nodup
  unique : (matchingRebaseQueueIds jobs).Nodup
  allocated : ∀ n ∈ matchingRebaseQueueIds jobs, 0 < n ∧ n < base.nr 76






end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentLiveQueue

/-! matching/MatchingRebaseFinishedRows.lean -/
section RppSource_MatchingRebaseFinishedRows
namespace VehicleRoutingSurvey.Routing






/-- A completed rebase preserves the headers and the original edge words.
Only the representative field of a row in a rebased node takes its new port. -/
structure MatchingRebaseCompletedRows {base : ArithmeticState} {archive : MatchingRebaseArchive base}
    {target : ℕ → ℕ} (plan : MatchingRebaseLiftTarget archive target)
    (initial : List MatchingRebaseTask) (out : ArithmeticState) : Prop where
  lowMemory : ∀ a < base.nr 50, out.nm a = base.nm a
  headers : ∀ a, matchingRebaseHeaderArea base a → out.nm a = base.nm a
  rows : ∀ n c, archive.live n c → ∀ i < c.arity,
    matchingRebaseRowsAt base out n i =
      if n ∈ matchingRebaseQueueIds initial then
        {matchingRebaseRowsAt base base n i with
          representative := matchingRebasePortAt c (MatchingMemberJob.liftPort plan.port) i}
      else matchingRebaseRowsAt base base n i
  untouched : ∀ n, 0 < n → n < base.nr 76 → n ∉ matchingRebaseQueueIds initial →
    ∀ i < base.nm (base.nr 78+n), matchingRebaseRowsAt base out n i = matchingRebaseRowsAt base base n i




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseFinishedRows

/-! matching/MatchingAugmentTargetMates.lean -/
section RppSource_MatchingAugmentTargetMates
namespace VehicleRoutingSurvey.Routing

structure MatchingPreparedLift (base : ArithmeticState) (jobs : List MatchingRebaseTask) (target : ℕ → ℕ)
    extends MatchingPreparedRebase base jobs where
  lift : MatchingRebaseLiftTarget registry target
  ports : ∀ t ∈ jobs, t.port = lift.port t.node
  boundary : ∀ v < base.nr 55, (∀ t ∈ jobs, ¬t.needs v) → base.nm (base.nr 50 + v) = target v








end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentTargetMates

/-! matching/MatchingAugmentPrimalOutput.lean -/
section RppSource_MatchingAugmentPrimalOutput
namespace VehicleRoutingSurvey.Routing

/-- Compact mate memory uses the dimension as the marker for uncovered originals. -/
noncomputable def compactPrimalMateWord {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (i : ℕ) : ℕ :=
  if h : i < k then
    if (⟨i, h⟩ : Fin k) ∈ state.covered then (mateOfMatching state.perfect ⟨i, h⟩).val else k
  else k








end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPrimalOutput

/-! matching/MatchingAugmentInitialTasks.lean -/
section RppSource_MatchingAugmentInitialTasks
namespace VehicleRoutingSurvey.Routing

noncomputable def matchingAugmentTopTask {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (port : Fin k) : Option MatchingRebaseTask :=
  let q := part.representative port
  let B := part.blocks.block q
  if h : B.card ≠ 1 then
    some ⟨dual.node B, port.val, (cycles.entry B (part.blocks.cut_mem (Finset.mem_univ q) h)).tree⟩
  else none








end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInitialTasks

/-! matching/MatchingAugmentSelectedPrimal.lean -/
section RppSource_MatchingAugmentSelectedPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The finite original crossing read on each nonroot trace row, with the
orientation actually written by the forest handler. -/
noncomputable def matchingAugmentationSavedWitness {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (stored : MatchingForestOriginalWitnesses part forest s) (child : Fin k) : Fin k × Fin k := by
  classical
  if hp : ∃ p, (forest.role child).parent = some p then
    let h := stored hp.choose_spec
    exact (h.choose, h.choose_spec.choose)
  else exact (child,child)






end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentSelectedPrimal

/-! matching/MatchingStageCutoff.lean -/
section RppSource_MatchingStageCutoff
namespace VehicleRoutingSurvey.Routing

/-- Save the first unused blossom identifier at the start of a search. Each live
node below it is inherited from an earlier search. -/
def recordMatchingStageCutoff : List ArithmeticInstruction :=
  [.natConst 39 0, .natAdd 39 39 76]

def prepareWeightedMatchingStageBlock : List ArithmeticInstruction :=
  appendBlock warmMatchingPreparationBlock recordMatchingStageCutoff






end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageCutoff

/-! matching/MatchingAdvancedStage.lean -/
section RppSource_MatchingAdvancedStage
namespace VehicleRoutingSurvey.Routing

/-- Mathematical and physical input shared by the event arms after applying
the selected dual adjustment. The old selector minima are now minima at the
new numerical point. -/
structure MatchingAdvancedStage {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (cutAt : Fin k → Finset (Fin k))
    (original s : ArithmeticState) where
  primal : CompactMatchingPrimalDualMemory state original s
  search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween
  witnesses : MatchingForestOriginalWitnesses part forest s
  links : MatchingForestLinkMemory part forest s
  dual : MatchingSearchDualMemory part forest s
  registry : MatchingRegistryView dual
  reads : MatchingRefreshInput s part.representative (fun u => alternatingRoleCode (forest.role u)) cost
    (effectiveVertexPotential state.cuts state.potential state.cutDual)
  pairs : MatchingSearchOuterBuckets s part.representative (fun u => alternatingRoleCode (forest.role u)) cost
    (effectiveVertexPotential state.cuts state.potential state.cutDual)
  valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i
  least : ∀ g : MatchingCandidateGroup k, LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
    @decide _ (Classical.propDecidable (g.admits part.blocks forest (part.representativeOf positive) d)))
    (readMatchingCandidate cutAt s g.slot)




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAdvancedStage

/-! matching/MatchingContractForestRAM.lean -/
section RppSource_MatchingContractForestRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000





def survivingInnerParentEntersCycle (s : ArithmeticState) : Prop :=
  2 ≤ s.nm (s.nr 51 + s.nr 7) ∧ wasContractedRepresentative s (s.nm (s.nr 52 + s.nr 7))

instance (s : ArithmeticState) : Decidable (survivingInnerParentEntersCycle s) :=
  inferInstanceAs (Decidable (2 ≤ s.nm (s.nr 51 + s.nr 7) ∧
    wasContractedRepresentative s (s.nm (s.nr 52 + s.nr 7))))

















end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractForestRAM

/-! matching/MatchingContractMaskRAM.lean -/
section RppSource_MatchingContractMaskRAM
namespace VehicleRoutingSurvey.Routing















def matchingContractionMaskAddresses (s : ArithmeticState) : List ℕ :=
  (s.nr 89 + s.nr 12) ::
    (List.range (s.nr 13)).map (fun i => s.nr 89 + s.nm (s.nr 83 + i)) ++
    (List.range (s.nr 14)).map (fun i => s.nr 89 + s.nm (s.nr 84 + i))



end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractMaskRAM

/-! matching/MatchingContractionPrefixView.lean -/
section RppSource_MatchingContractionPrefixView
namespace VehicleRoutingSurvey.Routing

/-- Originals entering the outer forest are identified by their old inner
representative's occurrence on the two traces or at their common base. -/
def contractionFreshOriginalsBefore (s : ArithmeticState) : List ℕ :=
  (List.range (s.nr 55)).filter fun j => decide (
    s.nr 89 + originalTopRepresentative s j ∈ matchingContractionMaskAddresses s ∧
      2 ≤ s.nm (s.nr 51 + originalTopRepresentative s j))

/-- The actual allocator state and the regions that survive the scratch
scans. Earlier records and the newly appended rows can both be read at exit. -/
structure MatchingContractionWriterView (s t : ArithmeticState) : Prop where
  allocation : ∃ start written ticks, start.pc = 0 ∧ start.halted = false ∧ start.nr 9 = 1 ∧
    start.nm = s.nm ∧ (∀ r, r ∉ [0,6,7,10,11,23,81,82] → start.nr r = s.nr r) ∧
    BlockRuns writeMatchingContractionCycle ticks start written ∧ t.nr 68 = written.nr 68 ∧
    t.nr 76 = start.nr 76+1 ∧ t.nm (start.nr 74+start.nr 12) = start.nr 76 ∧
    t.rm = startMatchingCycleReal start ∧
    ∀ addr, start.nr 74+start.nr 55 ≤ addr → start.nr 52+start.nr 55 ≤ addr →
      start.nr 57+start.nr 55 ≤ addr → (addr < start.nr 86 ∨ start.nr 89+start.nr 55 ≤ addr) →
      t.nm addr = written.nm addr

/-- Natural workspace for the pair repair. The absorbed outer rows and newly
outer originals are ordered exactly as in the two actual collectors. -/
structure MatchingContractionPrefixView (s t : ArithmeticState) : Prop where
  writer : MatchingContractionWriterView s t
  absorbedCount : t.nr 87 = (absorbedMatchingOuterRows s).length
  freshCount : t.nr 99 = (contractionFreshOriginalsBefore s).length
  absorbed : ∀ j < t.nr 87,
    t.nm (t.nr 86 + j) = (absorbedMatchingOuterRows s)[j]?.getD 0
  fresh : ∀ j < t.nr 99,
    t.nm (t.nr 88 + j) = (contractionFreshOriginalsBefore s)[j]?.getD 0
  cacheNatural : ∀ a, s.nr 57+s.nr 55 ≤ a → s.nr 52+s.nr 55 ≤ a →
    (a < s.nr 74 ∨ s.nr 74+s.nr 55 ≤ a) → a ≠ s.nr 77+s.nr 76 → a ≠ s.nr 78+s.nr 76 →
    a < s.nr 86 → t.nm a = s.nm a
  cacheReal : ∀ a, s.nr 62+s.nr 55 ≤ a → a < s.nr 75 → t.rm a = s.rm a
  representative : s.nr 52+s.nr 55 ≤ s.nr 57 → s.nr 57+s.nr 55 ≤ s.nr 74 →
    ∀ j < s.nr 55, t.nm (s.nr 57+j) =
      if s.nr 89+originalTopRepresentative s j ∈ matchingContractionMaskAddresses s
      then s.nr 12 else originalTopRepresentative s j
  topNodes : s.nr 57+s.nr 55 ≤ s.nr 74 → s.nr 52+s.nr 55 ≤ s.nr 74 →
    s.nr 74+s.nr 55 ≤ s.nr 77 → s.nr 74+s.nr 55 ≤ s.nr 78 →
    ∀ j < s.nr 55, t.nm (s.nr 74+j) = if j = s.nr 12 then s.nr 76
      else if s.nr 89+j ∈ matchingContractionMaskAddresses s then 0 else s.nm (s.nr 74+j)
  cycleMask : ∀ j < s.nr 55, t.nm (s.nr 89+j) = if s.nr 89+j ∈ matchingContractionMaskAddresses s then 1 else 0
  forest : ∀ {k : ℕ}, s.nr 55 = k → s.nr 52 = s.nr 51+k → s.nr 53 = s.nr 51+k+k →
    s.nr 53+k ≤ s.nr 57 → s.nr 57+k ≤ s.nr 74 →
    ∀ (old : AlternatingForestState (Fin k)) (base : Fin k) (cycle : Finset (Fin k)), s.nr 12 = base.val →
      AlternatingForestMemory old (s.nr 51) s.nm →
      (∀ v : Fin k, s.nr 89+v.val ∈ matchingContractionMaskAddresses s ↔ v ∈ cycle) →
      AlternatingForestMemory (old.contract cycle base) (s.nr 51) t.nm







end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPrefixView

/-! matching/MatchingContractionDualSnapshot.lean -/
section RppSource_MatchingContractionDualSnapshot
namespace VehicleRoutingSurvey.Routing

/-- The contraction proof reads the new dual tables and clock with the
original natural arguments, including the two trace lengths. -/
noncomputable def matchingContractionDualSnapshot (s : ArithmeticState) : ArithmeticState :=
  { s with
    pc := 0
    rm := iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55)
    rr := Function.update s.rr 15 (s.rr 15 + s.rr 1) }









end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionDualSnapshot

/-! matching/MatchingAugmentCheckedLift.lean -/
section RppSource_MatchingAugmentCheckedLift
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The mathematical point immediately after the dual sweep, with the
pre-event natural memory needed to name the old forest and all its cuts. -/
noncomputable abbrev matchingAugmentDualPoint (s : ArithmeticState) : ArithmeticState :=
  matchingContractionDualSnapshot s

/-- The recursive queue starts from the selected top subtrees, with the
physical registry and representative tables produced by crossing installation. -/
structure MatchingAugmentPreparedRegistry {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {before base : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest before} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (rows : List (Fin k × Fin k))
    (nextPart : CompactMatchingPartition next) {jobs : List MatchingRebaseTask}
    (prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)) : Prop where
  frame : MatchingAugmentArchiveFrame before base
  tasks : jobs = (selectedAugmentationPorts rows).filterMap (matchingAugmentTopTask cycles)
  port : prepared.lift.port = matchingAugmentNodePort next old.cuts dual.node
  live : ∀ n tree, prepared.registry.live n tree ↔
    ∃ (B : Finset (Fin k)) (h : B ∈ old.cuts),
      dual.node B = n ∧ (cycles.entry B h).tree = tree ∧ matchingAugmentDerivedCut cycles.entry next B
  lowMemory : ∀ a < before.nr 50, base.nm a = before.nm a
  forestMemory : ∀ a, before.nr 51 ≤ a → a < before.nr 51 + 3 * k → base.nm a = before.nm a
  unique : ((selectedAugmentationPorts rows).map part.representative).Nodup
  chosenPorts : nextPart.representative =
    (rows.foldl (chooseAugmentationRepresentatives part.representative) id) ∘ part.representative
  untouched : ∀ q ∈ part.activeRepresentatives, q ∉ (selectedAugmentationPorts rows).map part.representative →
    ∀ e : Sym2 (Fin k), (∀ v ∈ e, v ∈ part.blocks.block q) → (e ∈ next.edges ↔ e ∈ old.edges)
  representatives : ∀ v : Fin k,
    base.nm (before.nr 57 + v.val) = (nextPart.representative v).val
  topNodes : ∀ v : Fin k,
    base.nm (before.nr 74 + v.val) =
      (rows.foldl (AugmentationRebaseModel.crossing part.representative)
        ⟨fun v => blossomNodeAt before v, []⟩).nodes v




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCheckedLift

/-! matching/MatchingExpansionAdvance.lean -/
section RppSource_MatchingExpansionAdvance
namespace VehicleRoutingSurvey.Routing

theorem MatchingSelectedExpansion.present {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {s : ArithmeticState} {B : Finset (Fin k)}
    (event : MatchingSelectedExpansion part forest positive s B) : B ∈ state.cuts := by
  have nontrivial : (part.blocks.block event.base).card ≠ 1 := by
    rw [event.block]
    exact event.nontrivial
  exact event.block ▸ part.blocks.cut_mem (Finset.mem_univ event.base) nontrivial





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionAdvance

/-! matching/WeightedStageDriver.lean -/
section RppSource_WeightedStageDriver
namespace VehicleRoutingSurvey.Routing







/-- This describes the remaining obligations of the dispatched grow, contract, expand,
and augment RAM blocks. The frame includes the represented forest and valid refreshed cache. -/
structure MatchingStageHandler (handler : List ArithmeticInstruction) (frame : ArithmeticState → Prop)
    (counts : ArithmeticState → MatchingStageCounts) (rowCap perCharge finishBudget : ℕ) : Prop where
  ready : ∀ s, frame (matchingStageSnapshot s) → s.nr 33 ≠ 0 →
    s.nr 1 = 0 ∧ s.nr 9 = 1 ∧ s.nr 8 ≤ rowCap ∧
    ∀ i < s.nr 8, ¬(s.nr 4 ≤ s.nr 5 + i ∧ s.nr 5 + i < s.nr 4 + s.nr 8)
  dispatch : ∀ s selected selectSteps, frame (matchingStageSnapshot s) → s.nr 33 ≠ 0 →
    BlockRuns selectAndAdvanceDualSlackBlock selectSteps s selected → selected.halted = false →
    DualBoundMinimum s (s.nr 8) selected → selected.nm = s.nm →
    (∀ a, selected.rm a = if selected.nr 1 ≠ 0 ∧ s.nr 4 ≤ a ∧ a < s.nr 4 + s.nr 8 then
      s.rm a - selected.rr 1 * s.rm (s.nr 5 + (a - s.nr 4)) else s.rm a) →
    ∃ next ticks, BlockRuns handler ticks {selected with pc := 0} next ∧ next.halted = false ∧
      frame (matchingStageSnapshot next) ∧ next.nr 30 = s.nr 30 ∧ next.nr 31 = s.nr 31 ∧
      next.nr 32 = s.nr 32 ∧ next.nr 34 = s.nr 34 ∧
      ((next.nr 33 = 0 ∧ ticks ≤ finishBudget) ∨
        (next.nr 33 ≠ 0 ∧ ∃ charge,
          MatchingStageTransition (counts (matchingStageSnapshot s)) charge (counts (matchingStageSnapshot next)) ∧
          ticks ≤ perCharge * charge))

def matchingStageBody (handler : List ArithmeticInstruction) : List ArithmeticInstruction :=
  branchOnUnequal 33 32 (appendBlock selectAndAdvanceDualSlackBlock handler)

/-- Run until augmentation and skip all remaining iterations of the bounded stage. -/
def matchingStageProgram (handler : List ArithmeticInstruction) : List ArithmeticInstruction :=
  countedLoopFromZero 34 30 31 (matchingStageBody handler)







end VehicleRoutingSurvey.Routing
end RppSource_WeightedStageDriver

/-! matching/WeightedMatchingLoop.lean -/
section RppSource_WeightedMatchingLoop
namespace VehicleRoutingSurvey.Routing

/-- The outer matching loop reserves registers 40, 41, and 42 for the augmentation counter,
one, and the required number of augmentations. -/
def matchingLoopSnapshot (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr 40 0}





/-- The per-augmentation obligations for the matched state, stage initialization, and
final lifting. `view i` records the original matching and dual data after `i` augmentations. -/
structure MatchingLoopInterface (n augmentations preparation rowCap perCharge finishBudget : ℕ)
    (prepare handler : List ArithmeticInstruction) (view frame : ℕ → ArithmeticState → Prop)
    (counts : ℕ → ArithmeticState → MatchingStageCounts) : Prop where
  initializeStage : ∀ i < augmentations, ∀ s, s.pc = 0 → s.halted = false →
    s.nr 40 = i → s.nr 41 = 1 → s.nr 42 = augmentations → view i (matchingLoopSnapshot s) →
    ∃ stageInput steps, steps ≤ preparation ∧ BlockRuns prepare steps s stageInput ∧
      stageInput.halted = false ∧ stageInput.nr 31 = 6 * n + 1 ∧ stageInput.nr 32 = 0 ∧ stageInput.nr 34 = 1 ∧
      frame i (matchingStageSnapshot stageInput) ∧ (counts i (matchingStageSnapshot stageInput)).credit ≤ 6 * n
  handlerChecked : ∀ i < augmentations, MatchingStageHandler handler (frame i) (counts i) rowCap perCharge finishBudget
  augmented : ∀ i < augmentations, ∀ s result steps, view i (matchingLoopSnapshot s) →
    BlockRuns (appendBlock prepare (matchingStageProgram handler)) steps s result →
    frame i (matchingStageSnapshot result) → result.nr 33 = 0 →
    view (i + 1) (matchingLoopSnapshot result) ∧ result.nr 40 = s.nr 40 ∧ result.nr 41 = s.nr 41 ∧
      result.nr 42 = s.nr 42

def weightedMatchingLoop (prepare handler : List ArithmeticInstruction) : List ArithmeticInstruction :=
  countedLoopFromZero 41 40 42 (appendBlock prepare (matchingStageProgram handler))





end VehicleRoutingSurvey.Routing
end RppSource_WeightedMatchingLoop

/-! matching/MatchingInterstageView.lean -/
section RppSource_MatchingInterstageView
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The persistent primal data of one augmentation stage, indexed by the
number of original matching edges already installed. -/
structure CompactMatchingInterstage {k : ℕ} (cost : Fin k → Fin k → ℝ)
    (original : ArithmeticState) (index : ℕ) (s : ArithmeticState) where
  state : CompactMatchingPrimalDual k cost
  part : CompactMatchingPartition state
  top : CompactTopMatching part
  count : state.edges.card = index
  internal : state.InternalCuts
  primal : CompactMatchingPrimalDualMemory state original s
  representatives : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (part.representative v).val
  effective : ∀ v : Fin k, s.rm (s.nr 62 + v.val) = effectiveVertexPotential state.cuts state.potential state.cutDual v












end VehicleRoutingSurvey.Routing
end RppSource_MatchingInterstageView

/-! matching/MatchingBetweenStages.lean -/
section RppSource_MatchingBetweenStages
namespace VehicleRoutingSurvey.Routing

/-- Persistent state passed from the allocator or a completed augmentation
into the next outer-loop iteration. Old role words are overwritten when the
next search starts. The cycle records and primal matching are retained. -/
structure MatchingBetweenStages {k : ℕ} (cost : Fin k → Fin k → ℝ) (original : ArithmeticState)
    (i : ℕ) (s : ArithmeticState) where
  graph : CompactMatchingInterstage cost original i s
  oldForest : AlternatingForestState (Fin k)
  dual : MatchingSearchDualMemory graph.part oldForest s
  registry : MatchingRegistryView dual
  cycles : MatchingLiveCycles registry
  storage : MatchingStageStorage k original s
  order : MatchingCycleRecordOrder s
  cursor : s.nr 76 ≤ 6*k*i+1
  reads : MatchingRefreshInput s graph.part.representative (fun v => alternatingRoleCode (oldForest.role v))
    cost (effectiveVertexPotential graph.state.cuts graph.state.potential graph.state.cutDual)








end VehicleRoutingSurvey.Routing
end RppSource_MatchingBetweenStages

/-! matching/MatchingProgram.lean -/
section RppSource_MatchingProgram
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



/-- The compact matcher is one fixed instruction list for every even input dimension. -/
def weightedBlossomMatchingBlock : List ArithmeticInstruction :=
  appendBlock initializeWeightedMatchingBlock
    (appendBlock (weightedMatchingLoop prepareWeightedMatchingStageBlock weightedBlossomEventHandler)
      publishCompactMateTableBlock)





/-- The invariants needed to certify the concrete event handler and the final output. -/
structure WeightedMatchingRefinement (k : ℕ) (cost : Fin k → Fin k → ℝ) (original : ArithmeticState) where
  interstage : ℕ → ArithmeticState → Prop
  active : ℕ → ArithmeticState → Prop
  counts : ℕ → ArithmeticState → MatchingStageCounts
  initial : ∀ t ticks, BlockRuns initializeWeightedMatchingBlock ticks original t →
    interstage 0 (matchingLoopSnapshot t)
  loop : MatchingLoopInterface k (k / 2) (104 * k * k + 48 * k + 33) (3 * k)
    (1024 * (k + 1)) (512 * (k ^ 2 + 1)) prepareWeightedMatchingStageBlock weightedBlossomEventHandler
    interstage active counts
  certificate : ∀ t, interstage (k / 2) (matchingLoopSnapshot t) → Nonempty (MatchingTerminalCertificate k cost original t)






end VehicleRoutingSurvey.Routing
end RppSource_MatchingProgram

/-! matching/MatchingContractHandler.lean -/
section RppSource_MatchingContractHandler
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000































/-- The existing matching workspace leaves the route and forest data before
the candidate and cycle tables. The trace legs contain original compact indices. -/
structure MatchingContractionLayout (s : ArithmeticState) : Prop where
  roleAfter : s.nr 51 ≤ s.nr 52
  roleEnd : s.nr 51 + s.nr 55 ≤ s.nr 57
  representativeEnd : s.nr 57 + s.nr 55 ≤ s.nr 58
  dictionaryAfter : s.nr 58 ≤ s.nr 54
  bucketsAfter : s.nr 58 ≤ s.nr 65
  realRatesAfter : s.nr 59 ≤ s.nr 60
  realBucketsAfter : s.nr 59 ≤ s.nr 66
  slacksAfter : s.nr 62 ≤ s.nr 59
  nodeDualAfter : s.nr 62 ≤ s.nr 75
  selectorsBeforeRecords : s.nr 58 ≤ s.nr 77 ∧ s.nr 58 ≤ s.nr 78
  nodeTableAfter : s.nr 51 ≤ s.nr 74
  recordHeadersBeforeTrace : s.nr 77 + s.nr 76 < s.nr 83 ∧ s.nr 78 + s.nr 76 < s.nr 83 ∧ s.nr 83 ≤ s.nr 84
  leftBefore : s.nr 83 + s.nr 13 ≤ s.nr 86
  rightBefore : s.nr 84 + s.nr 14 ≤ s.nr 86
  tablesBeforeRows : s.nr 58 ≤ s.nr 86
  rowsBeforeFresh : s.nr 86 + s.nr 55 ≤ s.nr 88
  freshBeforeMask : s.nr 88 + s.nr 55 ≤ s.nr 89
  maskBeforeRecords : s.nr 89 + s.nr 55 ≤ s.nr 68
  cycleSize : s.nr 13 + s.nr 14 + 1 ≤ s.nr 55
  baseValid : s.nr 12 < s.nr 55
  leftValid : ∀ j < s.nr 13, s.nm (s.nr 83 + j) < s.nr 55
  rightValid : ∀ j < s.nr 14, s.nm (s.nr 84 + j) < s.nr 55
  representativeValid : ∀ j < s.nr 55, originalTopRepresentative s j < s.nr 55













end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractHandler

/-! matching/MatchingContractionPartition.lean -/
section RppSource_MatchingContractionPartition
namespace VehicleRoutingSurvey.Routing

def CompactMatchingPartition.contractCut {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (cycle : Finset (Fin k)) : Finset (Fin k) :=
  (cycle.image part.blocks.block).biUnion id

theorem CompactMatchingPartition.mem_contractionChildren {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ v ∈ cycle, part.representative v = v) (u : Fin k) :
    part.blocks.block u ∈ cycle.image part.blocks.block ↔ part.representative u ∈ cycle := by
  constructor
  · intro h
    obtain ⟨r,hr,eq⟩ := Finset.mem_image.mp h
    have same := (part.same_block.mpr eq).symm.trans (fixed r hr)
    exact same.symm ▸ hr
  · intro h
    exact Finset.mem_image.mpr ⟨part.representative u,h,part.same_block.mp (part.representative_idem u)⟩

theorem CompactMatchingPartition.mem_contractCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ v ∈ cycle, part.representative v = v) (u : Fin k) :
    u ∈ part.contractCut cycle ↔ part.representative u ∈ cycle := by
  rw [← part.mem_contractionChildren cycle fixed u]
  constructor
  · intro h
    obtain ⟨B,hB,member⟩ := Finset.mem_biUnion.mp h
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hB
    have equal := part.blocks.same_of_mem (Finset.mem_univ r) member
    exact Finset.mem_image.mpr ⟨r,hr,equal.symm⟩
  · intro h
    exact Finset.mem_biUnion.mpr ⟨part.blocks.block u,h,part.blocks.self_mem u (Finset.mem_univ _)⟩

theorem CompactMatchingPartition.contractCut_odd {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card) : Odd (part.contractCut cycle).card := by
  have number : (cycle.image part.blocks.block).card = cycle.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv eq
    exact (fixed _ hu).symm.trans ((part.same_block.mpr eq).trans (fixed _ hv))
  exact (contractedBlossom_eligible part.blocks (Finset.image_mono part.blocks.block (Finset.subset_univ _)) (fun _ _ => Finset.subset_univ _)
    (fun B member => by
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp member
      by_cases one : (part.blocks.block u).card = 1
      · rw [one]; decide
      · exact (state.cutValid _ (part.blocks.cut_mem (Finset.mem_univ _) one)).1)
    (number.symm ▸ odd)).2

/-- Contract an odd cycle of top representatives, preserving the exposed
original port at its outer base and the two-way representative/partition map. -/
noncomputable def CompactMatchingPartition.contract {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle)
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card)
    (covered : ∀ c ∈ cycle, c ≠ base → c ∈ state.covered) :
    CompactMatchingPartition (state.registerCut (part.contractCut cycle) (part.contractCut_odd cycle fixed odd)) := by
  let next := part.blocks.contract (cycle.image part.blocks.block) (Finset.image_mono part.blocks.block (Finset.subset_univ _))
  let rep := fun u => blossomRepresentative cycle base (part.representative u)
  have block (u : Fin k) : next.block u = if part.representative u ∈ cycle then part.contractCut cycle else part.blocks.block u := by
    simp only [next,TopLevelMatchingBlocks.contract,part.mem_contractionChildren cycle fixed,contractCut]
  have baseMem : base ∈ part.contractCut cycle := (part.mem_contractCut cycle fixed base).mpr ((fixed base baseIn).symm ▸ baseIn)
  have sameFiber {u v : Fin k} (found : v ∈ next.block u) : rep v = rep u := by
    rw [block] at found
    by_cases merged : part.representative u ∈ cycle
    · rw [if_pos merged] at found
      simp only [rep,blossomRepresentative,if_pos merged,if_pos ((part.mem_contractCut cycle fixed v).mp found)]
    · rw [if_neg merged] at found
      have same := part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ u) found)
      simp only [rep,same]
  refine {blocks := next, representative := rep, inside := ?_, constant := ?_, coveredAway := ?_}
  · intro u
    rw [block]
    by_cases merged : part.representative u ∈ cycle
    · simpa only [rep,blossomRepresentative,if_pos merged] using baseMem
    · simpa only [rep,blossomRepresentative,if_neg merged] using part.inside u
  · intro u v eq
    exact sameFiber (eq.symm ▸ next.self_mem v (Finset.mem_univ v)) |>.symm
  · intro u v found different
    change v ∈ state.covered
    rw [block] at found
    by_cases merged : part.representative u ∈ cycle
    · rw [if_pos merged] at found
      have inCycle := (part.mem_contractCut cycle fixed v).mp found
      have away : v ≠ base := by simpa only [rep,blossomRepresentative,if_pos merged] using different
      by_cases fixedV : part.representative v = v
      · exact covered _ (fixedV ▸ inCycle) away
      · exact part.coveredAway v v (part.blocks.self_mem v (Finset.mem_univ v)) (Ne.symm fixedV)
    · rw [if_neg merged] at found
      exact part.coveredAway u v found (by simpa only [rep,blossomRepresentative,if_neg merged] using different)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPartition

/-! matching/MatchingContractColumnRows.lean -/
section RppSource_MatchingContractColumnRows
namespace VehicleRoutingSurvey.Routing



noncomputable def addContractionWinner {k : ℕ} (transform : DualSlack (MatchingDualEvent k) → DualSlack (MatchingDualEvent k))
    (winner old : Option (DualSlack (MatchingDualEvent k))) : Option (DualSlack (MatchingDualEvent k)) :=
  (winner.map transform).elim old (fun chosen => insertSlackCandidate chosen old)







end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractColumnRows

/-! matching/MatchingContractionColumnStep.lean -/
section RppSource_MatchingContractionColumnStep
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

def MatchingContractionColumnEligible {k : ℕ} (s : ArithmeticState) (merged outside : Fin k) : Prop :=
  s.nm (s.nr 51+outside.val) = 1 ∧ merged ≠ outside

instance {k : ℕ} (s : ArithmeticState) (merged outside : Fin k) :
    Decidable (MatchingContractionColumnEligible s merged outside) :=
  inferInstanceAs (Decidable (s.nm (s.nr 51+outside.val) = 1 ∧ merged ≠ outside))





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionColumnStep

/-! matching/MatchingContractionColumnSweep.lean -/
section RppSource_MatchingContractionColumnSweep
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

abbrev ContractionColumnWinner (k : ℕ) := Fin k × Option (DualSlack (MatchingDualEvent k))

noncomputable def contractionColumnRowUpdate {k : ℕ} (merged : Fin k) (clock : ℝ) (i : ℕ)
    (prior : Option (DualSlack (MatchingDualEvent k))) (result : ContractionColumnWinner k) :
    Option (DualSlack (MatchingDualEvent k)) :=
  if i = merged.val ∨ i = result.1.val then
    addContractionWinner (fun d => {d with slack := d.slack-(clock+clock)}) result.2 prior else prior

noncomputable def contractionColumnPairUpdate {k : ℕ} (merged : Fin k) (i : ℕ)
    (prior : Option (DualSlack (MatchingDualEvent k))) (result : ContractionColumnWinner k) :
    Option (DualSlack (MatchingDualEvent k)) :=
  if i = k*merged.val+result.1.val ∨ i = k*result.1.val+merged.val then
    addContractionWinner id result.2 prior else prior



 structure ContractionColumnProgress {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState)
    (merged : Fin k) (absorbed : List (Fin k)) (full : Fin k → Fin k → List (DualSlack (MatchingDualEvent k)))
    (seen : ℕ) (m : ArithmeticState) where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 24 = seen
  unit : m.nr 9 = 1
  zero : m.nr 23 = 0
  fixed : ∀ r, r = 21 ∨ 25 ≤ r → m.nr r = s.nr r
  clock : m.rr 15 = s.rr 15
  footprint : MatchingCacheFootprint k s m
  history : List (ContractionColumnWinner k)
  chosen : ∀ v : Fin k, MatchingContractionColumnEligible s merged v → v.val < seen →
    ∃ w, (v,w) ∈ history ∧ LeastSlackEntry (absorbed.flatMap (fun row => full row v)) w
  offered : ∀ v w, (v,w) ∈ history → v.val < seen ∧
    (if MatchingContractionColumnEligible s merged v then LeastSlackEntry (absorbed.flatMap (fun row => full row v)) w else w = none)
  pending : ∀ row ∈ absorbed, ∀ v : Fin k, MatchingContractionColumnEligible s merged v → seen ≤ v.val →
    readMatchingPairBucket (k := k) m (k*row.val+v.val) = readMatchingPairBucket (k := k) s (k*row.val+v.val)
  rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt m i ∧
    readMatchingCandidate cutAt m i = history.foldl (contractionColumnRowUpdate merged (s.rr 15) i) (readMatchingCandidate cutAt s i)
  buckets : ∀ i < k*k, MatchingPairBucketValid k m i ∧
    readMatchingPairBucket (k := k) m i = history.foldl (contractionColumnPairUpdate merged i) (readMatchingPairBucket (k := k) s i)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionColumnSweep

/-! matching/MatchingContractionPairMeaning.lean -/
section RppSource_MatchingContractionPairMeaning
namespace VehicleRoutingSurvey.Routing

/-- Relations between representative fibers before and after one contraction.
The role functions are the physical forest role codes. -/
structure MatchingContractionPairGeometry {k : ℕ} (prior next : Fin k → Fin k)
    (oldRole newRole : Fin k → ℕ) (merged : Fin k) (absorbed fresh : List (Fin k)) : Prop where
  baseMember : merged ∈ absorbed
  absorbedOuter : ∀ r ∈ absorbed, oldRole r = 1
  baseOuter : newRole merged = 1
  survivorOutside : ∀ c, c ≠ merged → newRole c = 1 → c ∉ absorbed
  survivorOuter : ∀ c, c ≠ merged → newRole c = 1 → oldRole c = 1
  survivorFiber : ∀ c, c ≠ merged → newRole c = 1 → ∀ u, next u = c ↔ prior u = c
  mergedFiber : ∀ u, next u = merged ↔ prior u ∈ absorbed ∨ u ∈ fresh
  outerPersists : ∀ u, oldRole (prior u) = 1 → newRole (next u) = 1
  outerAtRepresentative : ∀ c, newRole c = 1 → newRole (next c) = 1
  idempotent : ∀ u, next (next u) = next u



end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPairMeaning

/-! matching/MatchingContractionGroupMinimum.lean -/
section RppSource_MatchingContractionGroupMinimum
namespace VehicleRoutingSurvey.Routing

noncomputable def contractionSearchEntries {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (group : MatchingCandidateGroup k) :=
  (matchingSearchSlacks part forest positive).filter fun d =>
    @decide _ (Classical.propDecidable (group.admits part.blocks forest (part.representativeOf positive) d))





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionGroupMinimum

/-! matching/MatchingExpansionCutSweep.lean -/
section RppSource_MatchingExpansionCutSweep
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

structure ExpansionCutReadLayout (k : ℕ) (s : ArithmeticState) : Prop where
  roles : s.nr 51 + k ≤ s.nr 58
  owners : s.nr 65 ≤ s.nr 79
  nodes : s.nr 65 ≤ s.nr 74
  duals : s.nr 66 ≤ s.nr 75





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCutSweep

/-! matching/MatchingExpansionCoreFrame.lean -/
section RppSource_MatchingExpansionCoreFrame
namespace VehicleRoutingSurvey.Routing



/-- These four intervals contain the input, mate table, candidate dictionary
and pair buckets, registry headers, and every allocated cycle. -/
def matchingExpansionProtected (k : ℕ) (s : ArithmeticState) (a : ℕ) : Prop :=
  a < s.nr 51 ∨ (s.nr 58 ≤ a ∧ a < s.nr 74) ∨
    (s.nr 77 ≤ a ∧ a < s.nr 90) ∨ s.nr 80+3*k ≤ a

/-- Physical frame for the member map, arc path, split publication and
alternating forest update, before the cache is repaired. -/
structure MatchingExpansionCoreFrame (k : ℕ) (s t : ArithmeticState) : Prop where
  natural : ∀ a, matchingExpansionProtected k s a → t.nm a = s.nm a
  real : t.rm = s.rm
  realRegisters : t.rr = s.rr
  ports : ∀ r, 30 ≤ r → r ∉ [43,44,45,46,47,49,81,82,87,94,95,96,97,98] → t.nr r = s.nr r



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCoreFrame

/-! matching/MatchingExpansionExactLinks.lean -/
section RppSource_MatchingExpansionExactLinks
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- A tight original witness on a projected matched edge must itself be the
matching edge. This property is symmetric, so reversing a physical arc keeps it. -/
def matchingExactExpansionEdge {k : ℕ} {cost : Fin k → Fin k → ℝ} (state : CompactMatchingPrimalDual k cost)
    (rep : Fin k → Fin k) (e : Sym2 (Fin k)) : Prop :=
  oddCutDualEdgeValue state.cuts state.potential state.cutDual e = edgeCost cost e ∧
    (Sym2.map rep e ∈ state.edges → e ∈ state.edges)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionExactLinks

/-! matching/MatchingExpansionOpenedCore.lean -/
section RppSource_MatchingExpansionOpenedCore
namespace VehicleRoutingSurvey.Routing



theorem MatchingLiveCycles.selectedBase {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {chosen s : ArithmeticState}
    {B : Finset (Fin k)} (event : MatchingSelectedExpansion part forest positive chosen B)
    {prior : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView prior}
    (live : MatchingLiveCycles registry) :
    (live.entry B event.present).base = event.base ∧ registry.trees.tree event.base =
      .blossom event.base.val (prior.node B) (live.entry B event.present).tree .nil := by
  have present : part.blocks.block event.base ∈ state.cuts := event.block.symm ▸ event.present
  let target := (live.entry B event.present).base = event.base ∧ registry.trees.tree event.base =
    .blossom event.base.val (prior.node B) (live.entry B event.present).tree .nil
  change target
  have transport (C : Finset (Fin k)) (h : C ∈ state.cuts) (eq : C = B) :
      (live.entry C h).base = event.base ∧ registry.trees.tree event.base =
        .blossom event.base.val (prior.node C) (live.entry C h).tree .nil → target := by
    subst C
    exact id
  exact transport _ present event.block (live.top event.base present event.active)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionOpenedCore

/-! matching/MatchingExpansionCollectTables.lean -/
section RppSource_MatchingExpansionCollectTables
namespace VehicleRoutingSurvey.Routing

def matchingExpansionFreshSources (k : ℕ) (s : ArithmeticState) : List (Fin k) :=
  (List.finRange k).filter fun v => decide (expansionChildOf s v.val < s.nr 55) &&
    decide (expansionRepRole s (expansionChildOf s v.val) = 1)







end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCollectTables



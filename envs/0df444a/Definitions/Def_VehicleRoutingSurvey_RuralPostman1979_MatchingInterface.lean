-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
-- name    : VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T15:22:51.384843+00:00
-- url     : https://prove2.me/theorems/5e19faab-fd65-4053-86c8-d4db44febbca
-- title:
--   Rural postman algorithm — weighted matching dispatcher interface
-- statement:
--   This Lean module defines the arithmetic-RAM weighted matching dispatcher, its selected and prepared search states, and the credit used to bound continuing events in the Table 3 implementation.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part02

/-! matching/WeightedCacheRAM.lean -/
section RppSource_WeightedCacheRAM
namespace VehicleRoutingSurvey.Routing

/-- Merge one least-slack candidate into a cache cell. Natural register 0 is the new edge
identifier, and register 1 is the current one. Zero means empty. Real registers 0 and 1
carry their slacks. An equal-slack edge keeps the earlier representative. -/
def mergeSlackEntryBlock : List ArithmeticInstruction :=
  [.natConst 2 0, .natBranch 0 2 7 2, .natBranch 1 2 4 3, .realBranch 1 0 7 4,
    .natAdd 1 0 2, .realConst 2 0, .realAdd 1 0 2]













end VehicleRoutingSurvey.Routing
end RppSource_WeightedCacheRAM

/-! matching/WeightedCertificate.lean -/
section RppSource_WeightedCertificate
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



/-- A matching edge crosses a cut when exactly one of its endpoints belongs to the cut. -/
abbrev MatchingCrossesCut {n : ℕ} (S : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  ¬ e.IsDiag ∧ (e.toFinset.filter (· ∈ S)).card = 1





/-- The sum of the endpoint potentials and the cut variables on an edge. -/
noncomputable def oddCutDualEdgeValue {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) (e : Sym2 (Fin n)) : ℝ :=
  (∑ v ∈ e.toFinset, potential v) + ∑ S ∈ cuts.filter (MatchingCrossesCut · e), cutDual S







end VehicleRoutingSurvey.Routing
end RppSource_WeightedCertificate

/-! matching/WeightedDualStep.lean -/
section RppSource_WeightedDualStep
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- A linear constraint remains feasible while `step * rate ≤ slack`. -/
structure DualSlack (Event : Type*) where
  event : Event
  slack : ℝ
  rate : ℝ

structure DualBound (Event : Type*) where
  event : Event
  amount : ℝ









inductive MatchingDualEvent (n : ℕ) where
  | edge (e : Sym2 (Fin n))
  | cut (S : Finset (Fin n))

noncomputable def matchingEdgeSlack {n : ℕ} (c : Fin n → Fin n → ℝ)
    (cuts : Finset (Finset (Fin n))) (potential direction : Fin n → ℝ)
    (cutDual cutDirection : Finset (Fin n) → ℝ) (e : Sym2 (Fin n)) :
    DualSlack (MatchingDualEvent n) :=
  ⟨.edge e, edgeCost c e - oddCutDualEdgeValue cuts potential cutDual e,
    oddCutDualEdgeValue cuts direction cutDirection e⟩

noncomputable def matchingCutSlack {n : ℕ} (cutDual cutDirection : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) : DualSlack (MatchingDualEvent n) :=
  ⟨.cut S, cutDual S, -cutDirection S⟩

/-- The constraints encountered by a weighted matching dual adjustment. -/
noncomputable def matchingDualSlacks {n : ℕ} (c : Fin n → Fin n → ℝ)
    (edges : List (Sym2 (Fin n))) (cuts : Finset (Finset (Fin n)))
    (potential direction : Fin n → ℝ) (cutDual cutDirection : Finset (Fin n) → ℝ) :
    List (DualSlack (MatchingDualEvent n)) :=
  edges.map (matchingEdgeSlack c cuts potential direction cutDual cutDirection) ++
    cuts.toList.map (matchingCutSlack cutDual cutDirection)





noncomputable def MatchingDualAdjustment {n : ℕ} (c : Fin n → Fin n → ℝ)
    (edges : List (Sym2 (Fin n))) (cuts : Finset (Finset (Fin n)))
    (potential direction : Fin n → ℝ) (cutDual cutDirection : Finset (Fin n) → ℝ)
    (bound : DualBound (MatchingDualEvent n)) : Prop :=
    let potential' := fun v => potential v + bound.amount * direction v
    let cutDual' := fun S => cutDual S + bound.amount * cutDirection S
    0 ≤ bound.amount ∧ (∀ e ∈ edges, oddCutDualEdgeValue cuts potential' cutDual' e ≤ edgeCost c e) ∧
      (∀ S ∈ cuts, 0 ≤ cutDual' S) ∧
      match bound.event with
      | .edge e => e ∈ edges ∧ 0 < oddCutDualEdgeValue cuts direction cutDirection e ∧
          oddCutDualEdgeValue cuts potential' cutDual' e = edgeCost c e
      | .cut S => S ∈ cuts ∧ cutDirection S < 0 ∧ cutDual' S = 0





end VehicleRoutingSurvey.Routing
end RppSource_WeightedDualStep

/-! matching/WeightedForestSlope.lean -/
section RppSource_WeightedForestSlope
namespace VehicleRoutingSurvey.Routing

/-- The current top-level blocks group matched vertices into singleton vertices and
contracted blossoms. The nonsingleton blocks have cut variables. -/
structure TopLevelMatchingBlocks {n : ℕ} (O : Finset (Fin n))
    (cuts : Finset (Finset (Fin n))) where
  block : Fin n → Finset (Fin n)
  self_mem : ∀ v ∈ O, v ∈ block v
  same_of_mem : ∀ {v w}, v ∈ O → w ∈ block v → block w = block v
  cut_mem : ∀ {v}, v ∈ O → (block v).card ≠ 1 → block v ∈ cuts

noncomputable def forestVertexDirection {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    (label : Finset (Fin n) → ℝ) (v : Fin n) : ℝ :=
  if (blocks.block v).card = 1 then label (blocks.block v) else 0

noncomputable def forestCutDirection {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    (label : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  if S ∈ O.image blocks.block ∧ S.card ≠ 1 then label S else 0





end VehicleRoutingSurvey.Routing
end RppSource_WeightedForestSlope

/-! matching/MatchingTerminalState.lean -/
section RppSource_MatchingTerminalState
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



/-- Data maintained between searches. Exposed originals are outside `covered`.
Internal matchings provide the complementary-slackness condition for live cuts. -/
structure CompactMatchingPrimalDual (k : ℕ) (cost : Fin k → Fin k → ℝ) where
  covered : Finset (Fin k)
  edges : Finset (Sym2 (Fin k))
  perfect : IsPerfectMatchingOn covered edges
  cuts : Finset (Finset (Fin k))
  potential : Fin k → ℝ
  cutDual : Finset (Fin k) → ℝ
  cutValid : ∀ B ∈ cuts, Odd B.card ∧ 0 ≤ cutDual B
  feasible : ∀ e, ¬e.IsDiag → oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost cost e
  tight : ∀ e ∈ edges, oddCutDualEdgeValue cuts potential cutDual e = edgeCost cost e
  internal : ∀ B ∈ cuts, 0 < cutDual B → ∃ base ∈ B,
    ∀ v ∈ B, v ≠ base → ∃ e ∈ edges, v ∈ e ∧ ∀ w ∈ e, w ∈ B

structure CompactMatchingPrimalDualMemory {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (original result : ArithmeticState) : Prop where
  dimension : result.nr 55 = k
  oddMap : result.nr 56 = original.nr 31
  mateAbove : original.nr 63 ≤ result.nr 50
  mate : ∀ v : Fin k, result.nm (result.nr 50 + v.val) =
    if v ∈ state.covered then (mateOfMatching state.perfect v).val else k
  saved : ∀ r ≥ 100, result.nr r = original.nr r
  natural : ∀ a < original.nr 63, result.nm a = original.nm a
  real : ∀ a < original.nr 64, result.rm a = original.rm a






end VehicleRoutingSurvey.Routing
end RppSource_MatchingTerminalState

/-! matching/MatchingPartitionView.lean -/
section RppSource_MatchingPartitionView
namespace VehicleRoutingSurvey.Routing

/-- The live top partition names each block by an original port. Inside a block,
only that port can remain exposed to the rest of the matching. -/
structure CompactMatchingPartition {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) where
  blocks : TopLevelMatchingBlocks Finset.univ state.cuts
  representative : Fin k → Fin k
  inside : ∀ v, representative v ∈ blocks.block v
  constant : ∀ u v, blocks.block u = blocks.block v → representative u = representative v
  coveredAway : ∀ v w, w ∈ blocks.block v → w ≠ representative v → w ∈ state.covered









/-- A search only starts in positive dimension. Extend the representative map to
arbitrary cuts for the selector's label function. The empty-set value is unused. -/
noncomputable def CompactMatchingPartition.representativeOf {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (positive : 0 < k)
    (S : Finset (Fin k)) : Fin k := by
  classical
  exact if member : S.Nonempty then part.representative member.choose else ⟨0, positive⟩






end VehicleRoutingSurvey.Routing
end RppSource_MatchingPartitionView

/-! matching/CompactEdges.lean -/
section RppSource_CompactEdges
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The abstract constraint list for the complete matching problem on the compact indices. -/
def compactMatchingEdges (k : ℕ) : List (Sym2 (Fin k)) :=
  (List.finRange k).flatMap fun u =>
    ((List.finRange k).filter fun v => decide (u ≠ v)).map fun v => s(u, v)







end VehicleRoutingSurvey.Routing
end RppSource_CompactEdges

/-! matching/AlternatingForestGrow.lean -/
section RppSource_AlternatingForestGrow
namespace VehicleRoutingSurvey.Routing

inductive AlternatingForestRole (α : Type*) where
  | unlabelled
  | outer (parent : Option α)
  | inner (parent : α)

structure AlternatingForestState (α : Type*) where
  role : α → AlternatingForestRole α
  depth : α → ℕ

/-- The parent of a marked node is closer to a root. An inner node was reached by
a tight unmatched edge, and its mate is an outer child. -/
def AlternatingForestState.valid {α : Type*} (state : AlternatingForestState α)
    (mate : α → Option α) (tight : α → α → Prop) : Prop :=
  ∀ x, match state.role x with
    | .unlabelled => True
    | .outer none => mate x = none
    | .outer (some p) => (∃ q, state.role p = .inner q) ∧ mate x = some p ∧
        mate p = some x ∧ tight p x ∧ state.depth p < state.depth x
    | .inner p => (∃ q, state.role p = .outer q) ∧ mate x ≠ some p ∧
        (∃ child, mate x = some child ∧ state.role child = .outer (some x)) ∧
        tight p x ∧ state.depth p < state.depth x





end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrow

/-! matching/AlternatingForestTrace.lean -/
section RppSource_AlternatingForestTrace
namespace VehicleRoutingSurvey.Routing

def AlternatingForestRole.parent {α : Type*} : AlternatingForestRole α → Option α
  | .unlabelled => none
  | .outer parent => parent
  | .inner parent => some parent











end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTrace

/-! matching/WeightedForestDispatch.lean -/
section RppSource_WeightedForestDispatch
namespace VehicleRoutingSurvey.Routing

noncomputable def AlternatingForestRole.dualDirection {α : Type*} : AlternatingForestRole α → ℝ
  | .outer _ => 1
  | .inner _ => -1
  | .unlabelled => 0













end VehicleRoutingSurvey.Routing
end RppSource_WeightedForestDispatch

/-! matching/MatchingSearchDual.lean -/
section RppSource_MatchingSearchDual
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Every retained blossom has an internal near-perfect matching, including
blossoms with zero dual value that can acquire a positive value in this search. -/
def CompactMatchingPrimalDual.InternalCuts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) : Prop :=
  ∀ B ∈ state.cuts, ∃ base ∈ B,
    ∀ v ∈ B, v ≠ base → ∃ e ∈ state.edges, v ∈ e ∧ ∀ w ∈ e, w ∈ B

/-- A crossing matched edge is represented by the two endpoints of its
quotient mate pair. Inner and outer partners take opposite dual steps. -/
structure CompactMatchingSearchForest {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (mate : Fin k → Option (Fin k))
    (tight : Fin k → Fin k → Prop) : Prop where
  valid : forest.valid mate tight
  crossing : ∀ {u v : Fin k}, s(u, v) ∈ state.edges → part.blocks.block u ≠ part.blocks.block v →
    mate (part.representative u) = some (part.representative v) ∧
      mate (part.representative v) = some (part.representative u)
  exposed : ∀ v ∉ state.covered, forest.role (part.representative v) = .outer none



noncomputable def CompactMatchingPartition.dualLabel {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (B : Finset (Fin k)) : ℝ :=
  (forest.role (part.representativeOf positive B)).dualDirection








end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchDual

/-! matching/WeightedEffectivePotential.lean -/
section RppSource_WeightedEffectivePotential
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- For edges leaving a top-level blossom, all containing cut variables act as part of the
vertex's effective potential. Storing this value makes external edge slack a constant-time read. -/
noncomputable def effectiveVertexPotential {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) (v : Fin n) : ℝ :=
  potential v + ∑ S ∈ cuts.filter (v ∈ ·), cutDual S









end VehicleRoutingSurvey.Routing
end RppSource_WeightedEffectivePotential

/-! matching/MatchingCacheWriteRAM.lean -/
section RppSource_MatchingCacheWriteRAM
namespace VehicleRoutingSurvey.Routing

/-- Register 18 is the cache slot, registers 15–16 its original endpoints, real register 0
the slack, and real register 4 the rate. Slot `r` uses event identifier `r+1`. -/
def storeMatchingCandidateCell : List ArithmeticInstruction :=
  [.natAdd 6 18 9, .natAdd 10 58 18, .natStore 10 6, .natAdd 10 18 18,
    .natAdd 10 54 10, .natStore 10 15, .natAdd 10 10 9, .natStore 10 16,
    .natAdd 10 59 18, .realStore 10 0, .natAdd 10 60 18, .realStore 10 4]







 def compareMatchingCacheCandidate : List ArithmeticInstruction :=
  [.natAdd 6 58 18, .natLoad 10 6, .natConst 11 0, .natBranch 10 11 7 4,
    .natAdd 6 59 18, .realLoad 2 6, .realBranch 2 0 19 7]

def improveMatchingCandidateBlock : List ArithmeticInstruction :=
  appendBlock compareMatchingCacheCandidate storeMatchingCandidateCell









end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheWriteRAM

/-! matching/MatchingEdgeSlackRAM.lean -/
section RppSource_MatchingEdgeSlackRAM
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- On registers 15 and 16, load a pair's metric entry and its two effective potentials.
The resulting external edge slack is stored in real register 0. -/
def readExternalSlackBlock : List ArithmeticInstruction :=
  [.natAdd 6 21 15, .natLoad 10 6, .natAdd 6 20 10, .natAdd 6 6 16, .realLoad 0 6,
    .natAdd 6 62 15, .realLoad 2 6, .natAdd 6 62 16, .realLoad 3 6,
    .realSub 0 0 2, .realSub 0 0 3]





end VehicleRoutingSurvey.Routing
end RppSource_MatchingEdgeSlackRAM

/-! matching/MatchingEventDispatchRAM.lean -/
section RppSource_MatchingEventDispatchRAM
namespace VehicleRoutingSurvey.Routing

/-- Execute exactly one of two blocks, selected by a natural register comparison. -/
def branchOnAtMost (x y : ℕ) (left right : List ArithmeticInstruction) : List ArithmeticInstruction :=
  [.natBranch x y 1 (2 + left.length)] ++ left.map (relocateInstruction 1) ++
    [.jump (2 + left.length + right.length)] ++ right.map (relocateInstruction (2 + left.length))









/-- After the action tag is stored in register 35, dispatch to its grow, contract, expand,
or augment code. Registers 36–38 hold 0, 1, and 2. -/
def dispatchMatchingActionBlock (grow contract expand augment : List ArithmeticInstruction) : List ArithmeticInstruction :=
  branchOnAtMost 35 37 (branchOnAtMost 35 36 grow contract) (branchOnAtMost 35 38 expand augment)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingEventDispatchRAM

/-! matching/MatchingPairBucketRAM.lean -/
section RppSource_MatchingPairBucketRAM
namespace VehicleRoutingSurvey.Routing

/-- Update one outer-to-outer bucket. Register 18 is its flat index, 15 and 16 are
the original endpoints, and real register 5 is the normalized slack. -/
def improveMatchingPairBucketCell : List ArithmeticInstruction :=
  [.natAdd 6 18 18, .natAdd 6 65 6, .natLoad 10 6, .natBranch 55 10 7 4,
    .natAdd 11 66 18, .realLoad 2 11, .realBranch 2 5 12 7,
    .natStore 6 15, .natAdd 6 6 9, .natStore 6 16, .natAdd 11 66 18, .realStore 11 5]











end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairBucketRAM

/-! matching/MatchingGrowCacheRAM.lean -/
section RppSource_MatchingGrowCacheRAM
namespace VehicleRoutingSurvey.Routing

attribute [local simp] List.forall_mem_append List.forall_mem_map
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def readGrowthCacheNeighbor : List ArithmeticInstruction :=
  [.natAdd 16 25 14, .natAdd 6 57 16, .natLoad 17 6, .natAdd 6 51 17, .natLoad 19 6]

def growIncomingArgs (rate : ℚ) : List ArithmeticInstruction :=
  [.natAdd 18 55 16, .realConst 4 rate]

def growIncomingCache (rate : ℚ) : List ArithmeticInstruction :=
  appendBlock (growIncomingArgs rate) improveMatchingCandidateBlock

def normalizeGrowthSlack : List ArithmeticInstruction :=
  [.realAdd 5 15 15, .realAdd 5 5 0, .realConst 4 2]

def growBucketArgs (source target : ℕ) : List ArithmeticInstruction :=
  [.natAdd 6 21 source, .natLoad 10 6, .natAdd 18 10 target]

def growOuterRowArgs (source : ℕ) : List ArithmeticInstruction :=
  [.natAdd 18 source 14]

def growOuterCacheSide (source target : ℕ) : List ArithmeticInstruction :=
  appendBlock (appendBlock (growBucketArgs source target) improveMatchingPairBucketCell)
    (appendBlock (growOuterRowArgs source) improveMatchingCandidateBlock)

/-- Registers 26 and 17 name distinct outer blocks, 15 and 16 name the original
endpoints, and real register 0 contains the raw edge slack. Insert the edge into
both outer pair buckets and both incident candidate rows. -/
def insertMatchingOuterEdgeBlock : List ArithmeticInstruction :=
  appendBlock normalizeGrowthSlack
    (appendBlock (growOuterCacheSide 26 17) (growOuterCacheSide 17 26))

def chooseGrowthCache : List ArithmeticInstruction :=
  branchOnAtMost 19 14 (growIncomingCache 1)
    (branchOnAtMost 19 9 insertMatchingOuterEdgeBlock (growIncomingCache 0))

/-- An original vertex in the newly outer block is in register 15. Visit the original
neighbor indexed by register 25. Register 26 contains the newly outer representative
and register 14 is zero. Internal edges are skipped. For external edges, update the
incoming cache for a nonouter target or both directed buckets and row caches for an
outer target. -/
def refreshGrowthNeighborBlock : List ArithmeticInstruction :=
  appendBlock readGrowthCacheNeighbor
    (branchOnUnequal 26 17 (appendBlock readExternalSlackBlock chooseGrowthCache))















































def refreshSelectedOuterVertex : List ArithmeticInstruction :=
  countedLoopFromZero 9 25 55 refreshGrowthNeighborBlock







def readGrowthCacheSource : List ArithmeticInstruction :=
  [.natAdd 15 24 14, .natAdd 6 57 15, .natLoad 17 6]

def selectedGrowthCacheSource : List ArithmeticInstruction :=
  appendBlock [.natAdd 27 27 9] refreshSelectedOuterVertex

def refreshGrowthCacheSourceBlock : List ArithmeticInstruction :=
  appendBlock readGrowthCacheSource
    (branchOnAtMost 17 26 (branchOnAtMost 26 17 selectedGrowthCacheSource []) [])

def initGrowthCacheScan : List ArithmeticInstruction :=
  [.natConst 24 0, .natConst 27 0]

/-- Visit each compact vertex once. Only vertices whose representative is the newly
outer block in register 26 initiate a neighbor scan. Register 27 counts those scans. -/
def refreshMatchingNewOuterBlock : List ArithmeticInstruction :=
  appendBlock initGrowthCacheScan (countedLoop 9 24 55 refreshGrowthCacheSourceBlock)























end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRAM

/-! matching/AlternatingForestGrowRAM.lean -/
section RppSource_AlternatingForestGrowRAM
namespace VehicleRoutingSurvey.Routing

/-- Registers 0, 1, and 2 hold the predecessor, inner vertex, and outer vertex. Registers
3, 4, and 5 hold the role, parent, and depth table bases. Outer is stored as 1 and inner as 2. -/
def alternatingForestGrowBlock : List ArithmeticInstruction :=
  [.natAdd 6 5 0, .natLoad 8 6,
    .natAdd 6 3 1, .natConst 7 2, .natStore 6 7,
    .natAdd 6 3 2, .natConst 7 1, .natStore 6 7,
    .natAdd 6 4 1, .natStore 6 0,
    .natAdd 6 4 2, .natStore 6 1,
    .natAdd 8 8 7, .natAdd 6 5 1, .natStore 6 8,
    .natAdd 8 8 7, .natAdd 6 5 2, .natStore 6 8]





end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrowRAM

/-! matching/AlternatingForestMemory.lean -/
section RppSource_AlternatingForestMemory
namespace VehicleRoutingSurvey.Routing

def alternatingRoleCode {n : ℕ} : AlternatingForestRole (Fin n) → ℕ
  | .unlabelled => 0
  | .outer _ => 1
  | .inner _ => 2

def alternatingParentCode {n : ℕ} : AlternatingForestRole (Fin n) → ℕ
  | .unlabelled => n
  | .outer none => n
  | .outer (some p) => p.val
  | .inner p => p.val

/-- A forest is stored in three consecutive tables. The vertex count is the empty parent code. -/
def AlternatingForestMemory {n : ℕ} (forest : AlternatingForestState (Fin n)) (base : ℕ)
    (memory : ℕ → ℕ) : Prop :=
  ∀ v : Fin n,
    memory (base + v.val) = alternatingRoleCode (forest.role v) ∧
    memory (base + n + v.val) = alternatingParentCode (forest.role v) ∧
    memory (base + n + n + v.val) = forest.depth v





end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestMemory

/-! matching/MatchingWarmPreparation.lean -/
section RppSource_MatchingWarmPreparation
namespace VehicleRoutingSurvey.Routing

/-- The persistent memory layout used when starting another augmenting search. -/
structure MatchingWarmLayout (s : ArithmeticState) (k : ℕ) : Prop where
  size : s.nr 55 = k
  candidates : s.nr 61 = 3 * k
  parents : s.nr 52 = s.nr 51 + k
  depths : s.nr 53 = s.nr 51 + k + k
  matesBefore : s.nr 50 + k ≤ s.nr 51
  representativesAfter : s.nr 51 + 3 * k ≤ s.nr 57
  candidatesAfter : s.nr 57 + k ≤ s.nr 58
  dictionaryAfter : s.nr 58 ≤ s.nr 54
  pairsAfter : s.nr 58 ≤ s.nr 65
  ratesAfter : s.nr 59 ≤ s.nr 60
  keysAfter : s.nr 59 ≤ s.nr 66
  offsetsBefore : s.nr 21 + k ≤ s.nr 50








end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPreparation

/-! matching/MatchingWarmPrimal.lean -/
section RppSource_MatchingWarmPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

noncomputable def CompactMatchingPrimalDual.partialMate {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (v : Fin k) : Option (Fin k) :=
  if v ∈ state.covered then some (mateOfMatching state.perfect v) else none





/-- Every nonbase member of a top block is already matched inside it. A matched
base instead has a partner in a different block. -/
structure CompactTopMatching {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) : Prop where
  interior : ∀ v w, w ∈ part.blocks.block v → w ≠ part.representative v →
    ∃ e ∈ state.edges, w ∈ e ∧ ∀ z ∈ e, z ∈ part.blocks.block v
  matchedBase : ∀ {v w}, part.representative v = v → state.partialMate v = some w →
    part.blocks.block v ≠ part.blocks.block w







def CompactMatchingPartition.tightBetween {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (u v : Fin k) : Prop :=
  ∃ a b : Fin k, part.representative a = u ∧ part.representative b = v ∧
    oddCutDualEdgeValue state.cuts state.potential state.cutDual s(a, b) = edgeCost cost s(a, b)






end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPrimal

/-! matching/MatchingExpansionChildPorts.lean -/
section RppSource_MatchingExpansionChildPorts
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The child port table is a partition of the opened blossom. Each registered
child owns its original endpoints, and any nontrivial child remains a live cut. -/
structure MatchingExpansionChildPorts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (B : Finset (Fin k)) where
  ports : Finset (Fin k)
  block : Fin k → Finset (Fin k)
  owner : Fin k → Fin k
  containsPort : ∀ p ∈ ports, p ∈ block p
  subset : ∀ p ∈ ports, block p ⊆ B
  covered : ∀ v ∈ B, owner v ∈ ports ∧ v ∈ block (owner v)
  unique : ∀ p ∈ ports, ∀ v ∈ block p, owner v = p
  live : ∀ p ∈ ports, (block p).card ≠ 1 → block p ∈ state.cuts.erase B











end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionChildPorts

/-! matching/MatchingCycleRecordRAM.lean -/
section RppSource_MatchingCycleRecordRAM
namespace VehicleRoutingSurvey.Routing

/-- One child in the cyclic list and the original edge leading to the next child. -/
structure MatchingCycleChild where
  representative : ℕ
  node : ℕ
  endpointA : ℕ
  endpointB : ℕ











/-- Append a child record at the live registry cursor. Its old node identifier is
loaded before any writes, making existing nested blossoms available to later expansions. -/
def appendMatchingCycleChild : List ArithmeticInstruction :=
  [.natAdd 6 74 15, .natLoad 10 6,
   .natStore 68 15, .natAdd 68 68 9, .natStore 68 10, .natAdd 68 68 9,
   .natStore 68 16, .natAdd 68 68 9, .natStore 68 17, .natAdd 68 68 9]





/-- Register the new cycle at zero dual value. Its record will start at the current
cursor and contain the two exclusive trace legs and the common base. -/
def startMatchingCycleRecord : List ArithmeticInstruction :=
  [.natAdd 6 77 76, .natStore 6 68, .natAdd 6 78 76,
   .natAdd 10 13 14, .natAdd 10 10 9, .natStore 6 10,
   .natAdd 6 75 76, .realConst 0 0, .realStore 6 0]







def matchingCycleChildAt (memory : ℕ → ℕ) (address : ℕ) : MatchingCycleChild :=
  ⟨memory address, memory (address + 1), memory (address + 2), memory (address + 3)⟩



/-- Read a stored cycle header using its node identifier in register 22. -/
def readMatchingCycleHeader : List ArithmeticInstruction :=
  [.natAdd 6 77 22, .natLoad 18 6, .natAdd 6 78 22, .natLoad 19 6]



/-- Read a single child record at index 7 in the cycle starting at register 18. -/
def readMatchingCycleChild : List ArithmeticInstruction :=
  [.natAdd 6 7 7, .natAdd 6 6 6, .natAdd 6 18 6, .natLoad 15 6,
    .natAdd 6 6 9, .natLoad 25 6, .natAdd 6 6 9, .natLoad 16 6,
    .natAdd 6 6 9, .natLoad 17 6]





end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordRAM

/-! matching/MatchingCycleMembersRAM.lean -/
section RppSource_MatchingCycleMembersRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096





/-- Push a representative, child node ID, and its immediate child of the expanded
blossom onto the depth-first traversal stack. -/
def pushMatchingCycleMember : List ArithmeticInstruction :=
  [.natAdd 6 87 87, .natAdd 6 6 87, .natAdd 6 80 6, .natStore 6 15,
    .natAdd 6 6 9, .natStore 6 25, .natAdd 6 6 9, .natStore 6 26, .natAdd 87 87 9]



def popMatchingCycleMember : List ArithmeticInstruction :=
  [.natSub 87 87 9, .natAdd 6 87 87, .natAdd 6 6 87, .natAdd 6 80 6,
    .natLoad 15 6, .natAdd 6 6 9, .natLoad 22 6, .natAdd 6 6 9, .natLoad 26 6]



def preserveTopCycleChild : List ArithmeticInstruction := [.natAdd 26 15 23]

def writeCycleMemberLeaf : List ArithmeticInstruction :=
  [.natAdd 6 79 15, .natStore 6 26]

def pushTopCycleChild : List ArithmeticInstruction :=
  appendBlock readMatchingCycleChild (appendBlock preserveTopCycleChild pushMatchingCycleMember)

def pushNestedCycleChild : List ArithmeticInstruction :=
  appendBlock readMatchingCycleChild pushMatchingCycleMember

def visitCycleMemberNode : List ArithmeticInstruction :=
  appendBlock popMatchingCycleMember (branchOnAtMost 22 23 writeCycleMemberLeaf
    (appendBlock readMatchingCycleHeader (countedLoopFromZero 9 7 19 pushNestedCycleChild)))

def clearCycleMemberMapCell : List ArithmeticInstruction :=
  [.natAdd 6 79 7, .natStore 6 55]

/-- Recover the immediate-child map of the nontrivial node given in register 22.
Each original leaf receives the representative of its immediate child. Registers
79 and 80 hold disjoint map and stack scratch arrays. -/
def mapMatchingCycleNodeMembers : List ArithmeticInstruction :=
  appendBlock [.natConst 23 0, .natConst 87 0, .natAdd 28 55 55]
    (appendBlock (countedLoopFromZero 9 7 55 clearCycleMemberMapCell)
      (appendBlock readMatchingCycleHeader
        (appendBlock (countedLoopFromZero 9 7 19 pushTopCycleChild)
          (countedLoopFromZero 9 24 28 (branchOnUnequal 87 23 visitCycleMemberNode)))))

/-- Recover the child map for the current top-level representative in register 97. -/
def mapMatchingCycleMembers : List ArithmeticInstruction :=
  appendBlock [.natAdd 6 74 97, .natLoad 22 6] mapMatchingCycleNodeMembers











end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleMembersRAM

/-! matching/MatchingMemberTree.lean -/
section RppSource_MatchingMemberTree
namespace VehicleRoutingSurvey.Routing

/-- The live descendant records of a blossom. A nontrivial record owns an ordered
cycle of children and a singleton has no registry node. The final argument of each
nonempty constructor is the list of siblings. -/
inductive MatchingMemberTree where
  | nil
  | leaf (vertex : ℕ) (siblings : MatchingMemberTree)
  | blossom (representative node : ℕ) (children siblings : MatchingMemberTree)

namespace MatchingMemberTree

def arity : MatchingMemberTree → ℕ
  | .nil => 0
  | .leaf _ siblings | .blossom _ _ _ siblings => 1 + siblings.arity



def leaves : MatchingMemberTree → List ℕ
  | .nil => []
  | .leaf v siblings => v :: siblings.leaves
  | .blossom _ _ children siblings => children.leaves ++ siblings.leaves

/-- Two or more children suffice for the accounting bound. Actual blossom cycles
have odd length at least three. -/
def proper : MatchingMemberTree → Prop
  | .nil => True
  | .leaf _ siblings => siblings.proper
  | .blossom _ node children siblings =>
    0 < node ∧ 2 ≤ children.arity ∧ children.proper ∧ siblings.proper





/-- Registry words used by the membership traversal at one child entry. -/
def rootKey (representative node : ℕ) : ℕ × ℕ := (representative, node)

def rootKeys : MatchingMemberTree → List (ℕ × ℕ)
  | .nil => []
  | .leaf v siblings => rootKey v 0 :: siblings.rootKeys
  | .blossom r node _ siblings => rootKey r node :: siblings.rootKeys



/-- Interpret the descendants using exactly the cycle headers and child keys read by
the RAM routine. The two endpoint words of an entry are not used in this traversal. -/
def encoded (memory : ℕ → ℕ) (startBase countBase : ℕ) : MatchingMemberTree → Prop
  | .nil => True
  | .leaf _ siblings => siblings.encoded memory startBase countBase
  | .blossom _ node children siblings =>
    memory (countBase + node) = children.arity ∧
    (∀ i (h : i < children.rootKeys.length),
      let cell := matchingCycleChildAt memory (memory (startBase + node) + 4 * i)
      rootKey cell.representative cell.node = children.rootKeys[i]) ∧
    children.encoded memory startBase countBase ∧ siblings.encoded memory startBase countBase

/-- Areas which must remain unchanged while the scratch map and DFS stack are written. -/
def readable (memory : ℕ → ℕ) (startBase countBase : ℕ) (untouched : ℕ → Prop) :
    MatchingMemberTree → Prop
  | .nil => True
  | .leaf _ siblings => siblings.readable memory startBase countBase untouched
  | .blossom _ node children siblings =>
    untouched (startBase + node) ∧ untouched (countBase + node) ∧
    (∀ i < children.arity, ∀ w < 4, untouched (memory (startBase + node) + 4 * i + w)) ∧
    children.readable memory startBase countBase untouched ∧ siblings.readable memory startBase countBase untouched



/-- The dynamic cycle records start past the statically allocated scratch arrays.
Unlike the cycle records, header cells may be below the scratch arrays. -/
def recordsAbove (memory : ℕ → ℕ) (startBase lower : ℕ) : MatchingMemberTree → Prop
  | .nil => True
  | .leaf _ siblings => siblings.recordsAbove memory startBase lower
  | .blossom _ node children siblings =>
    lower ≤ memory (startBase + node) ∧ children.recordsAbove memory startBase lower ∧
      siblings.recordsAbove memory startBase lower

end MatchingMemberTree

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberTree

/-! matching/MatchingMemberStack.lean -/
section RppSource_MatchingMemberStack
namespace VehicleRoutingSurvey.Routing

/-- A pending visit keeps the immediate child of the original root even when it
travels down to a nested blossom. The first three fields are the RAM stack words. -/
structure MatchingMemberJob where
  representative : ℕ
  node : ℕ
  owner : ℕ
  children : Option MatchingMemberTree

namespace MatchingMemberJob

def assignments (job : MatchingMemberJob) : List (ℕ × ℕ) :=
  match job.children with
  | none => [(job.representative, job.owner)]
  | some children => children.leaves.map fun v => (v, job.owner)





def tree (job : MatchingMemberJob) : MatchingMemberTree :=
  match job.children with
  | none => .leaf job.representative .nil
  | some children => .blossom job.representative job.node children .nil

def frontier (stack : List MatchingMemberJob) : List (ℕ × ℕ) := stack.flatMap assignments









end MatchingMemberJob

namespace MatchingMemberTree

/-- Order before the RAM puts these records on its LIFO stack. At the first level
each child is its own owner, and every deeper level inherits its parent's owner. -/
def jobs (owner : Option ℕ) : MatchingMemberTree → List MatchingMemberJob
  | .nil => []
  | .leaf v siblings => ⟨v, 0, owner.getD v, none⟩ :: siblings.jobs owner
  | .blossom r node children siblings => ⟨r, node, owner.getD r, some children⟩ :: siblings.jobs owner

















end MatchingMemberTree

namespace MatchingMemberJob























end MatchingMemberJob

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberStack

/-! matching/MatchingMemberWalkRAM.lean -/
section RppSource_MatchingMemberWalkRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

/-- Neither the leaf map nor the encoded DFS stack may overlap a live header or record. -/
def outsideMatchingMemberScratch (s : ArithmeticState) (a : ℕ) : Prop :=
  (a < s.nr 79 ∨ s.nr 79 + s.nr 55 ≤ a) ∧ (a < s.nr 80 ∨ s.nr 80 + 3 * s.nr 55 ≤ a)



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberWalkRAM

/-! matching/MatchingMemberMapRAM.lean -/
section RppSource_MatchingMemberMapRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

/-- The registry entry in register 22 denotes an actual nontrivial live blossom.
The finite subtree identifies all original leaves, their immediate-child owners,
and the immutable cycle data needed to reach them. -/
structure MatchingMemberRoot (s : ArithmeticState) (children : MatchingMemberTree) : Prop where
  proper : (MatchingMemberTree.blossom 0 (s.nr 22) children .nil).proper
  encoded : (MatchingMemberTree.blossom 0 (s.nr 22) children .nil).encoded s.nm (s.nr 77) (s.nr 78)
  readable : (MatchingMemberTree.blossom 0 (s.nr 22) children .nil).readable s.nm (s.nr 77) (s.nr 78)
    (outsideMatchingMemberScratch s)
  above : (MatchingMemberTree.blossom 0 (s.nr 22) children .nil).recordsAbove s.nm (s.nr 77)
    (s.nr 80 + 3 * s.nr 55)
  unique : children.leaves.Nodup
  valid : ∀ v ∈ children.leaves, v < s.nr 55
  separated : s.nr 79 + s.nr 55 ≤ s.nr 80

def matchingMemberAssignments (children : MatchingMemberTree) : List (ℕ × ℕ) :=
  MatchingMemberJob.frontier (children.jobs none)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberMapRAM

/-! matching/MatchingExpansionDirectionRAM.lean -/
section RppSource_MatchingExpansionDirectionRAM
namespace VehicleRoutingSurvey.Routing

private def halveExpansionDistanceCell : List ArithmeticInstruction :=
  [.natBranch 49 47 1 4, .natSub 47 47 49, .natAdd 95 95 9, .jump 4]



private def initializeExpansionHalving : List ArithmeticInstruction :=
  [.natConst 49 2, .natAdd 47 46 23, .natConst 95 0]

/-- Compute quotient and remainder by two on a path length bounded by the compact
dimension. The real RAM has addition and subtraction on natural registers. -/
def halveExpansionDistance : List ArithmeticInstruction :=
  appendBlock initializeExpansionHalving (countedLoopFromZero 9 24 55 halveExpansionDistanceCell)





private def chooseForwardExpansionDistance : List ArithmeticInstruction :=
  branchOnAtMost 81 82 [.natSub 46 82 81] [.natSub 6 81 82, .natSub 46 19 6]





private def chooseEvenExpansionDirection : List ArithmeticInstruction :=
  branchOnAtMost 47 23 [.natConst 45 0]
    (appendBlock [.natConst 45 1, .natSub 46 19 46] halveExpansionDistance)

/-- Of the two arcs between entry and base, use the even-length one. Register 45
selects the direction, 46 is its edge count, and 95 is its pair count. -/
def chooseMatchingExpansionDirection : List ArithmeticInstruction :=
  appendBlock chooseForwardExpansionDistance (appendBlock halveExpansionDistance chooseEvenExpansionDirection)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionDirectionRAM

/-! matching/MatchingForestWitnessRAM.lean -/
section RppSource_MatchingForestWitnessRAM
namespace VehicleRoutingSurvey.Routing

def forestWitnessAddress (base child : ℕ) : ℕ := base + (child + child)

def matchingForestWitnessAt (memory : ℕ → ℕ) (base child : ℕ) : ℕ × ℕ :=
  let addr := forestWitnessAddress base child
  (memory addr, memory (addr + 1))











def matchingOriginalGrowthEvent (s : ArithmeticState) : ℕ × ℕ :=
  let slot := s.nr 1 - 1
  let addr := s.nr 54 + (slot + slot)
  (s.nm addr, s.nm (addr + 1))

/-- Save both original endpoints before growth can replace the selected candidate row. -/
def saveMatchingGrowthOriginalEdge : List ArithmeticInstruction :=
  [.natSub 6 1 9, .natAdd 6 6 6, .natAdd 6 54 6, .natLoad 22 6, .natAdd 6 6 9, .natLoad 23 6]





/-- Use the saved original endpoint pair to write the new inner node's link. The matched
parent edge of the new outer node connects its base and the inner base. -/
def storeMatchingGrowthWitnesses : List ArithmeticInstruction :=
  [.natAdd 6 28 28, .natAdd 6 90 6, .natStore 6 22, .natAdd 6 6 9, .natStore 6 23,
   .natAdd 6 26 26, .natAdd 6 90 6, .natStore 6 28, .natAdd 6 6 9, .natStore 6 26]











 def orientMatchingGrowthEdge : List ArithmeticInstruction :=
  [.natAdd 6 57 22, .natLoad 10 6, .natBranch 10 28 3 8, .natBranch 28 10 4 8,
   .natConst 14 0, .natAdd 6 22 14, .natAdd 22 23 14, .natAdd 23 6 14]



/-- Both resulting witness pairs point from the forest parent to its child. -/
def storeOrientedMatchingGrowthWitnesses : List ArithmeticInstruction :=
  appendBlock orientMatchingGrowthEdge storeMatchingGrowthWitnesses



end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestWitnessRAM

/-! matching/MatchingExpansionSearchRAM.lean -/
section RppSource_MatchingExpansionSearchRAM
namespace VehicleRoutingSurvey.Routing







private def fetchExpansionParentWitness : List ArithmeticInstruction :=
  [.natConst 23 0, .natAdd 6 52 97, .natLoad 96 6, .natAdd 6 50 97, .natLoad 98 6,
   .natAdd 6 97 97, .natAdd 6 90 6, .natLoad 43 6, .natAdd 6 6 9, .natLoad 44 6,
   .natAdd 6 57 43, .natLoad 10 6]

private def chooseExpansionEntryChild (original : ℕ) : List ArithmeticInstruction :=
  [.natAdd 6 79 original, .natLoad 27 6]

/-- Recover the decomposed inner blossom's entry child from the original parent witness.
Registers 43/44 save that witness, 96 the outside forest parent, and 98 the mate. -/
def findExpansionEntryChild : List ArithmeticInstruction :=
  appendBlock fetchExpansionParentWitness (branchOnAtMost 10 97
    (branchOnAtMost 97 10 (chooseExpansionEntryChild 43) (chooseExpansionEntryChild 44))
    (chooseExpansionEntryChild 44))

def readExpansionHeader : List ArithmeticInstruction :=
  appendBlock [.natAdd 6 74 97, .natLoad 22 6, .natAdd 81 55 23, .natAdd 82 55 23]
    readMatchingCycleHeader

def readExpansionRepresentative : List ArithmeticInstruction :=
  [.natAdd 6 7 7, .natAdd 6 6 6, .natAdd 6 18 6, .natLoad 15 6]

def rememberExpansionIndex (representative output : ℕ) : List ArithmeticInstruction :=
  branchOnAtMost 15 representative
    (branchOnAtMost representative 15 [.natAdd output 7 23] []) []

def considerExpansionIndex : List ArithmeticInstruction :=
  appendBlock readExpansionRepresentative (appendBlock (rememberExpansionIndex 27 81) (rememberExpansionIndex 97 82))

/-- Locate the entry and old base in the stored cycle. The cycle base and length end
in registers 18 and 19, and the two positions in 81 and 82. -/
def locateMatchingExpansionEndpoints : List ArithmeticInstruction :=
  appendBlock findExpansionEntryChild
    (appendBlock readExpansionHeader (countedLoopFromZero 9 7 19 considerExpansionIndex))









end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSearchRAM

/-! matching/MatchingRebasePair.lean -/
section RppSource_MatchingRebasePair
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Advance the cycle index in register 7, wrapping at the count in register 19. -/
def advanceMatchingCycleIndexBlock : List ArithmeticInstruction :=
  [.natAdd 7 7 9, .natBranch 19 7 2 3, .natConst 7 0]



private def saveRebasePairLeft : List ArithmeticInstruction :=
  [.natAdd 10 15 14, .natAdd 11 25 14, .natAdd 12 16 14, .natAdd 13 17 14]





private def orientRebasePairPorts : List ArithmeticInstruction :=
  [.natAdd 6 79 12, .natLoad 6 6, .natBranch 6 10 3 4, .natBranch 10 6 7 4,
   .natAdd 6 12 14, .natAdd 12 13 14, .natAdd 13 6 14]





/-- Read adjacent child records and orient the saved original edge using the membership map.
The right child is the cyclic successor, including when the edge crosses the array boundary. -/
def readRebasedCyclePairBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock (appendBlock readMatchingCycleChild saveRebasePairLeft)
    advanceMatchingCycleIndexBlock) readMatchingCycleChild) orientRebasePairPorts




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePair

/-! matching/MatchingExpansionEmitRAM.lean -/
section RppSource_MatchingExpansionEmitRAM
namespace VehicleRoutingSurvey.Routing

/-- Move to the previous cycle record, wrapping zero to the last index. -/
def retreatMatchingCycleIndexBlock : List ArithmeticInstruction :=
  [.natBranch 7 23 3 1, .natSub 7 7 9, .jump 4, .natSub 7 19 9]





/-- Append a child representative and its original parent-edge pair to the path output. -/
def writeMatchingExpansionPathTriple : List ArithmeticInstruction :=
  [.natStore 47 15, .natAdd 47 47 9, .natStore 47 16, .natAdd 47 47 9,
    .natStore 47 17, .natAdd 47 47 9]



def prepareExpansionPathFirst : List ArithmeticInstruction :=
  [.natAdd 94 86 23, .natAdd 47 86 23, .natAdd 7 81 23, .natAdd 16 43 23, .natAdd 17 44 23]

def writeExpansionPathForward : List ArithmeticInstruction :=
  appendBlock readMatchingCycleChild
    (appendBlock advanceMatchingCycleIndexBlock (appendBlock readExpansionRepresentative writeMatchingExpansionPathTriple))

def writeExpansionPathBackward : List ArithmeticInstruction :=
  appendBlock retreatMatchingCycleIndexBlock (appendBlock readMatchingCycleChild
    (appendBlock [.natAdd 6 16 23, .natAdd 16 17 23, .natAdd 17 6 23] writeMatchingExpansionPathTriple))

/-- The first record uses the blossom's old outer-parent witness. Following records use
the cycle edge just traversed, in either direction. The selected arc has an even edge count. -/
def emitMatchingExpansionPath : List ArithmeticInstruction :=
  appendBlock prepareExpansionPathFirst
    (appendBlock readExpansionRepresentative
      (appendBlock writeMatchingExpansionPathTriple
        (countedLoopFromZero 9 24 46 (branchOnAtMost 45 23 writeExpansionPathForward writeExpansionPathBackward))))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionEmitRAM

/-! matching/ExpansionRepresentativeRAM.lean -/
section RppSource_ExpansionRepresentativeRAM
namespace VehicleRoutingSurvey.Routing

private def publishExpansionRepresentativeCell : List ArithmeticInstruction :=
  [.natAdd 6 79 7, .natLoad 10 6, .natBranch 55 10 6 3,
    .natAdd 6 57 7, .natStore 6 10, .jump 9, .jump 7, .jump 8, .jump 9]

def publishExpansionRepresentatives : List ArithmeticInstruction :=
  countedLoopFromZero 9 7 55 publishExpansionRepresentativeCell















end VehicleRoutingSurvey.Routing
end RppSource_ExpansionRepresentativeRAM

/-! matching/ExpansionRegistryRAM.lean -/
section RppSource_ExpansionRegistryRAM
namespace VehicleRoutingSurvey.Routing



private def storeExpansionNode : List ArithmeticInstruction :=
  [.natAdd 6 74 15, .natStore 6 25]

private def publishExpansionNodeCell : List ArithmeticInstruction :=
  appendBlock readMatchingCycleChild storeExpansionNode









def publishExpansionNodes : List ArithmeticInstruction := countedLoopFromZero 9 7 19 publishExpansionNodeCell



def publishExpansionSplit : List ArithmeticInstruction :=
  appendBlock publishExpansionRepresentatives publishExpansionNodes



end VehicleRoutingSurvey.Routing
end RppSource_ExpansionRegistryRAM

/-! matching/ExpansionDepthRAM.lean -/
section RppSource_ExpansionDepthRAM
namespace VehicleRoutingSurvey.Routing



private def readExpansionDepths : List ArithmeticInstruction :=
  [.natAdd 10 53 97, .natLoad 11 10, .natAdd 12 95 95]

private def shiftExpansionDepthCell : List ArithmeticInstruction :=
  [.natAdd 10 53 15, .natLoad 16 10, .natBranch 11 16 3 6,
    .natAdd 16 16 12, .natStore 10 16, .jump 9, .jump 7, .jump 8, .jump 9]







private def scanExpansionDepths : List ArithmeticInstruction :=
  countedLoopFromZero 9 15 55 shiftExpansionDepthCell

def reserveExpansionDepthsBlock : List ArithmeticInstruction :=
  appendBlock readExpansionDepths scanExpansionDepths







end VehicleRoutingSurvey.Routing
end RppSource_ExpansionDepthRAM

/-! matching/ExpansionPathRAM.lean -/
section RppSource_ExpansionPathRAM
namespace VehicleRoutingSurvey.Routing









private def readExpansionPair : List ArithmeticInstruction :=
  [.natLoad 1 23, .natAdd 23 23 9, .natLoad 17 23, .natAdd 23 23 9,
    .natLoad 18 23, .natAdd 23 23 9, .natLoad 2 23, .natAdd 23 23 9,
    .natLoad 19 23, .natAdd 23 23 9, .natLoad 22 23, .natAdd 23 23 9]

private def writeExpansionPair : List ArithmeticInstruction :=
  [.natAdd 6 1 1, .natAdd 6 90 6, .natStore 6 17, .natAdd 6 6 9, .natStore 6 18,
    .natAdd 6 2 2, .natAdd 6 90 6, .natStore 6 19, .natAdd 6 6 9, .natStore 6 22,
    .natAdd 0 2 14]









/-- Read two records, grow their alternating forest pair and install both parent witnesses. -/
def expansionGrowPairBlock : List ArithmeticInstruction :=
  appendBlock readExpansionPair (appendBlock alternatingForestGrowBlock writeExpansionPair)



end VehicleRoutingSurvey.Routing
end RppSource_ExpansionPathRAM

/-! matching/ExpansionPairLoop.lean -/
section RppSource_ExpansionPairLoop
namespace VehicleRoutingSurvey.Routing

def expandForestPairsBlock : List ArithmeticInstruction :=
  countedLoopFromZero 9 15 95 expansionGrowPairBlock







end VehicleRoutingSurvey.Routing
end RppSource_ExpansionPairLoop

/-! matching/ExpansionBaseRAM.lean -/
section RppSource_ExpansionBaseRAM
namespace VehicleRoutingSurvey.Routing

def prepareExpansionPairsBlock : List ArithmeticInstruction :=
  [.natAdd 0 96 14, .natAdd 23 94 14, .natAdd 3 51 14, .natAdd 4 52 14, .natAdd 5 53 14]



/-- Reattach the original base below the last outer predecessor, using
the new parent witness from the final record. -/
def reattachExpansionBaseBlock : List ArithmeticInstruction :=
  [.natAdd 23 23 9, .natLoad 17 23, .natAdd 23 23 9, .natLoad 18 23,
    .natAdd 6 52 97, .natStore 6 0,
    .natAdd 6 97 97, .natAdd 6 90 6, .natStore 6 17, .natAdd 6 6 9, .natStore 6 18]



end VehicleRoutingSurvey.Routing
end RppSource_ExpansionBaseRAM

/-! matching/ExpansionForestRAM.lean -/
section RppSource_ExpansionForestRAM
namespace VehicleRoutingSurvey.Routing



def expandAlternatingForestBlock : List ArithmeticInstruction :=
  appendBlock reserveExpansionDepthsBlock (appendBlock prepareExpansionPairsBlock
    (appendBlock expandForestPairsBlock reattachExpansionBaseBlock))



end VehicleRoutingSurvey.Routing
end RppSource_ExpansionForestRAM

/-! matching/MatchingBlossomDualRAM.lean -/
section RppSource_MatchingBlossomDualRAM
namespace VehicleRoutingSurvey.Routing

def blossomNodeAt (s : ArithmeticState) (i : ℕ) : ℕ :=
  s.nm (s.nr 74 + i)







/-- Change only nontrivial top-level cut variables with an outer or inner label.
Hidden children keep their stored duals until they reappear at the top level. -/
def advanceMatchingBlossomDualCell : List ArithmeticInstruction :=
  [.natAdd 6 74 7, .natLoad 10 6, .natBranch 10 14 13 3,
   .natAdd 6 51 7, .natLoad 11 6, .natBranch 11 14 13 6,
   .natAdd 6 75 10, .realLoad 0 6, .natBranch 11 9 9 11,
   .realAdd 0 0 1, .jump 12, .realSub 0 0 1, .realStore 6 0]





def advanceMatchingBlossomDualBlock : List ArithmeticInstruction :=
  countedLoopFromZero 9 7 55 advanceMatchingBlossomDualCell







end VehicleRoutingSurvey.Routing
end RppSource_MatchingBlossomDualRAM

/-! matching/MatchingEffectiveUpdateRAM.lean -/
section RppSource_MatchingEffectiveUpdateRAM
namespace VehicleRoutingSurvey.Routing





/-- Read the current top-level label and apply its dual step to one effective-potential cell. -/
def advanceEffectivePotentialCell : List ArithmeticInstruction :=
  [.natAdd 6 57 7, .natLoad 10 6, .natAdd 6 51 10, .natLoad 11 6,
    .natAdd 6 62 7, .realLoad 0 6, .natConst 12 0, .natBranch 11 12 14 8,
    .natConst 12 1, .natBranch 11 12 10 12, .realAdd 0 0 1, .jump 13, .realSub 0 0 1, .realStore 6 0]





def advanceEffectivePotentialBlock : List ArithmeticInstruction :=
  countedLoopFromZero 9 7 55 advanceEffectivePotentialCell





end VehicleRoutingSurvey.Routing
end RppSource_MatchingEffectiveUpdateRAM

/-! matching/MatchingGrowCutRAM.lean -/
section RppSource_MatchingGrowCutRAM
namespace VehicleRoutingSurvey.Routing





 def readGrowthInnerNode : List ArithmeticInstruction :=
  [.natAdd 6 74 28, .natLoad 10 6, .natAdd 18 55 55, .natAdd 18 18 28]

 def clearGrowthInnerCut : List ArithmeticInstruction :=
  [.natAdd 6 58 18, .natStore 6 14]

 def prepareGrowthInnerCut : List ArithmeticInstruction :=
  [.natAdd 6 75 10, .realLoad 0 6, .realConst 4 1, .natAdd 15 28 14, .natAdd 16 55 14]

/-- Install the newly inner blossom's cut event in the last candidate range.
Its endpoint pair is its representative and the out-of-range singleton sentinel. -/
def activateMatchingInnerCut : List ArithmeticInstruction :=
  appendBlock readGrowthInnerNode
    (branchOnAtMost 10 14 clearGrowthInnerCut (appendBlock prepareGrowthInnerCut storeMatchingCandidateCell))



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCutRAM

/-! matching/MatchingGrowEventRAM.lean -/
section RppSource_MatchingGrowEventRAM
namespace VehicleRoutingSurvey.Routing











/-- Read the chosen event's two original endpoints, their current block representatives,
and the left representative's role. -/
def readMatchingGrowEdge : List ArithmeticInstruction :=
  [.natSub 6 1 9, .natAdd 6 6 6, .natAdd 6 54 6, .natLoad 10 6, .natAdd 6 6 9, .natLoad 11 6,
    .natAdd 6 57 10, .natLoad 10 6, .natAdd 6 57 11, .natLoad 11 6,
    .natAdd 6 51 10, .natLoad 12 6, .natConst 14 0]



 def copyGrowEndpoints (x y : ℕ) : List ArithmeticInstruction := [.natAdd 0 x 14, .natAdd 1 y 14]



 def orientGrowEndpoints : List ArithmeticInstruction :=
  branchOnAtMost 12 14 (copyGrowEndpoints 11 10) (copyGrowEndpoints 10 11)



 def readGrowMateAndBases : List ArithmeticInstruction :=
  [.natAdd 6 50 1, .natLoad 2 6, .natAdd 3 51 14, .natAdd 4 52 14, .natAdd 5 53 14]



def prepareMatchingGrowBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock readMatchingGrowEdge orientGrowEndpoints) readGrowMateAndBases



def applyMatchingGrowEventBlock : List ArithmeticInstruction :=
  appendBlock prepareMatchingGrowBlock alternatingForestGrowBlock



end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowEventRAM

/-! matching/MatchingGrowRerateRAM.lean -/
section RppSource_MatchingGrowRerateRAM
namespace VehicleRoutingSurvey.Routing



/-- Incoming rows of newly outer originals become empty, since those edges are now
represented in the outer-pair cache. Incoming rows of newly inner originals keep their
edge and slack, with rate zero. Register 26 holds the new outer representative and 28
the new inner representative. -/
def rerateGrowthIncomingCell : List ArithmeticInstruction :=
  [.natAdd 6 57 7, .natLoad 10 6, .natAdd 11 55 7,
   .natBranch 10 26 4 8, .natBranch 26 10 5 8,
   .natAdd 6 58 11, .natStore 6 14, .jump 14,
   .natBranch 10 28 9 14, .natBranch 28 10 10 14,
   .natAdd 6 60 11, .realConst 2 0, .realStore 6 2, .jump 14]









def rerateGrowthIncomingBlock : List ArithmeticInstruction :=
  countedLoopFromZero 9 7 55 rerateGrowthIncomingCell





end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowRerateRAM

/-! matching/MatchingGrowCode.lean -/
section RppSource_MatchingGrowCode
namespace VehicleRoutingSurvey.Routing

def advanceMatchingTime : List ArithmeticInstruction :=
  [.natConst 14 0, .realAdd 15 15 1]

def advanceMatchingEventDuals : List ArithmeticInstruction :=
  appendBlock advanceMatchingTime (appendBlock advanceEffectivePotentialBlock advanceMatchingBlossomDualBlock)

def saveMatchingGrowthBlocks : List ArithmeticInstruction :=
  [.natConst 14 0, .natAdd 26 2 14, .natAdd 28 1 14]

def resetMatchingSelector : List ArithmeticInstruction :=
  [.natAdd 3 58 14, .natAdd 4 59 14, .natAdd 5 60 14, .natAdd 8 61 14, .natConst 1 0]

/-- Growth consumes the selected edge identifier, updates the forest, then refreshes the
candidate cache and reinstates the selector's input registers. -/
def matchingGrowHandlerBlock : List ArithmeticInstruction :=
  appendBlock advanceMatchingEventDuals
    (appendBlock applyMatchingGrowEventBlock
      (appendBlock saveMatchingGrowthBlocks
        (appendBlock rerateGrowthIncomingBlock
          (appendBlock activateMatchingInnerCut
            (appendBlock refreshMatchingNewOuterBlock resetMatchingSelector)))))

/-- Save the original selected edge across growth and write the two ordered parent witnesses. -/
def matchingGrowHandlerWithWitnesses : List ArithmeticInstruction :=
  appendBlock saveMatchingGrowthOriginalEdge (appendBlock matchingGrowHandlerBlock storeOrientedMatchingGrowthWitnesses)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCode

/-! matching/MatchingExpandCode.lean -/
section RppSource_MatchingExpandCode
namespace VehicleRoutingSurvey.Routing

def prepareMatchingExpansionArc : List ArithmeticInstruction :=
  appendBlock locateMatchingExpansionEndpoints
    (appendBlock chooseMatchingExpansionDirection emitMatchingExpansionPath)

/-- Publish the direct children and relabel the forest using the emitted path.
The registry header is read before the forest block reuses its scratch registers. -/
def commitMatchingExpansionBlock : List ArithmeticInstruction :=
  appendBlock publishExpansionSplit expandAlternatingForestBlock

def expandMatchingAfterMembersBlock : List ArithmeticInstruction :=
  appendBlock prepareMatchingExpansionArc commitMatchingExpansionBlock

def selectMatchingExpansionBase : List ArithmeticInstruction := [.natAdd 97 92 14]

def prepareExpansionChildrenBlock : List ArithmeticInstruction :=
  appendBlock selectMatchingExpansionBase mapMatchingCycleMembers

def expandMatchingRegistryHandlerBlock : List ArithmeticInstruction :=
  appendBlock advanceMatchingEventDuals (appendBlock prepareExpansionChildrenBlock expandMatchingAfterMembersBlock)

def expansionIncomingCell : List ArithmeticInstruction :=
  [.natAdd 6 79 7, .natLoad 10 6, .natBranch 55 10 15 3,
   .natAdd 6 51 10, .natLoad 19 6, .natAdd 11 55 7, .natBranch 19 14 7 11,
   .natAdd 6 60 11, .realConst 2 1, .realStore 6 2, .jump 15,
   .natBranch 19 9 12 15, .natAdd 6 58 11, .natStore 6 14, .jump 15]

def restoreExpansionIncomingRates : List ArithmeticInstruction :=
  countedLoopFromZero 9 7 55 expansionIncomingCell

def readExpansionCutOwner : List ArithmeticInstruction :=
  [.natAdd 6 79 7, .natLoad 10 6]

def readExpansionCutRole : List ArithmeticInstruction :=
  [.natAdd 28 7 14, .natAdd 6 51 28, .natLoad 19 6]

def clearExpansionCut : List ArithmeticInstruction :=
  [.natAdd 18 55 55, .natAdd 18 18 28, .natAdd 6 58 18, .natStore 6 14]

def handleExpansionCutRepresentative : List ArithmeticInstruction :=
  appendBlock readExpansionCutRole (branchOnAtMost 19 9 clearExpansionCut activateMatchingInnerCut)

/-- Inspect direct children only at their own representative positions.
Create the event for a non-singleton inner child, and clear obsolete cut slots. -/
def restoreExpansionCutCell : List ArithmeticInstruction :=
  appendBlock readExpansionCutOwner (branchOnAtMost 10 7 (branchOnAtMost 7 10 handleExpansionCutRepresentative []) [])

def restoreExpansionCuts : List ArithmeticInstruction :=
  countedLoopFromZero 9 7 55 restoreExpansionCutCell

def collectExpansionOuterCell : List ArithmeticInstruction :=
  [.natAdd 6 79 7, .natLoad 10 6, .natBranch 55 10 11 3,
   .natAdd 6 51 10, .natLoad 19 6, .natBranch 19 9 6 11, .natBranch 9 19 7 11,
   .natAdd 6 88 99, .natStore 6 7, .natAdd 99 99 9, .jump 11]

def collectExpansionOuterOriginals : List ArithmeticInstruction :=
  appendBlock [.natConst 99 0] (countedLoopFromZero 9 7 55 collectExpansionOuterCell)

def readExpansionOuterOriginal : List ArithmeticInstruction :=
  [.natAdd 6 88 24, .natLoad 15 6, .natAdd 6 57 15, .natLoad 26 6]

def refreshExpansionOuterCell : List ArithmeticInstruction :=
  appendBlock readExpansionOuterOriginal refreshSelectedOuterVertex

def refreshExpansionOuterOriginals : List ArithmeticInstruction :=
  countedLoopFromZero 9 24 99 refreshExpansionOuterCell

def restoreExpansionCacheBlock : List ArithmeticInstruction :=
  appendBlock collectExpansionOuterOriginals (appendBlock restoreExpansionIncomingRates
    (appendBlock restoreExpansionCuts (appendBlock refreshExpansionOuterOriginals resetMatchingSelector)))

def matchingExpandHandlerBlock : List ArithmeticInstruction :=
  appendBlock expandMatchingRegistryHandlerBlock restoreExpansionCacheBlock

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpandCode

/-! matching/MatchingStageBudget.lean -/
section RppSource_MatchingStageBudget
namespace VehicleRoutingSurvey.Routing

/-- During one augmenting search, outer vertices stay outer, and only blossoms inherited
from the previous stage can expand. -/
structure MatchingStageCounts where
  nonouterVertices : ℕ
  inheritedBlossoms : ℕ
  outerBlocks : ℕ

def MatchingStageCounts.credit (s : MatchingStageCounts) : ℕ :=
  5 * s.nonouterVertices + s.inheritedBlossoms + 3 * s.outerBlocks

/-- One charge covers an `O(n)` scan. Each search event pays a base charge, one per newly
outer vertex for scanning its neighbors, and one per absorbed row during a contraction. -/
inductive MatchingStageTransition : MatchingStageCounts → ℕ → MatchingStageCounts → Prop
  | grow {before after : MatchingStageCounts} (fresh : ℕ)
      (progress : 0 < fresh)
      (newOuter : before.nonouterVertices = after.nonouterVertices + fresh)
      (newBlocks : after.outerBlocks ≤ before.outerBlocks + fresh)
      (oldBlossoms : after.inheritedBlossoms ≤ before.inheritedBlossoms) :
      MatchingStageTransition before (1 + fresh) after
  | shrink {before after : MatchingStageCounts} (fresh absorbed : ℕ)
      (progress : 2 ≤ absorbed)
      (newOuter : before.nonouterVertices = after.nonouterVertices + fresh)
      (merged : after.outerBlocks + absorbed = before.outerBlocks + 1)
      (oldBlossoms : after.inheritedBlossoms ≤ before.inheritedBlossoms) :
      MatchingStageTransition before (1 + fresh + absorbed) after
  | expand {before after : MatchingStageCounts} (fresh : ℕ)
      (newOuter : before.nonouterVertices = after.nonouterVertices + fresh)
      (newBlocks : after.outerBlocks ≤ before.outerBlocks + fresh)
      (removed : after.inheritedBlossoms < before.inheritedBlossoms) :
      MatchingStageTransition before (1 + fresh) after











end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageBudget

/-! matching/AlternatingContractionParity.lean -/
section RppSource_AlternatingContractionParity
namespace VehicleRoutingSurvey.Routing

def AlternatingForestRole.outerTag {α : Type*} : AlternatingForestRole α → Bool
  | .outer _ => true
  | _ => false



























end VehicleRoutingSurvey.Routing
end RppSource_AlternatingContractionParity

/-! matching/MatchingExpansionOwnerMap.lean -/
section RppSource_MatchingExpansionOwnerMap
namespace VehicleRoutingSurvey.Routing

/-- The typed direct-child partition describes the entries of the registry tree
visited by the member-map program. -/
structure MatchingChildMemberTree {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    (registry : MatchingExpansionChildPorts state B) (tree : MatchingMemberTree) : Prop where
  assignment : ∀ v ∈ B, (v.val, (registry.owner v).val) ∈ matchingMemberAssignments tree
  absent : ∀ v ∉ B, v.val ∉ tree.leaves







end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionOwnerMap

/-! matching/MatchingSearchDualRAM.lean -/
section RppSource_MatchingSearchDualRAM
namespace VehicleRoutingSurvey.Routing







/-- The effective table is indexed by original vertices, while cut duals live at
stable registry IDs. Only top-level nonsingletons appear in the update table. -/
structure MatchingSearchDualMemory {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (s : ArithmeticState) where
  dimension : s.nr 55 = k
  separated : s.nr 62 + k ≤ s.nr 75
  reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (part.representative v).val
  roles : AlternatingForestMemory forest (s.nr 51) s.nm
  effective : ∀ v : Fin k, s.rm (s.nr 62 + v.val) = effectiveVertexPotential state.cuts state.potential state.cutDual v
  node : Finset (Fin k) → ℕ
  nodeNonzero : ∀ B ∈ state.cuts, node B ≠ 0
  nodeInjective : Set.InjOn node (↑state.cuts : Set (Finset (Fin k)))
  cutValues : ∀ B ∈ state.cuts, s.rm (s.nr 75 + node B) = state.cutDual B
  top : ∀ v : Fin k, blossomNodeAt s v =
    if part.representative v = v ∧ (part.blocks.block v).card ≠ 1 then node (part.blocks.block v) else 0










end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchDualRAM

/-! matching/MatchingSearchWitnesses.lean -/
section RppSource_MatchingSearchWitnesses
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Every forest parent link stores its original tight edge, oriented from the
parent's block to the child's block. -/
def MatchingForestOriginalWitnesses {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (s : ArithmeticState) : Prop :=
  ∀ {child parent : Fin k}, (forest.role child).parent = some parent →
    ∃ a b : Fin k, matchingForestWitnessAt s.nm (s.nr 90) child.val = (a.val, b.val) ∧
      part.representative a = parent ∧ part.representative b = child ∧
      oddCutDualEdgeValue state.cuts state.potential state.cutDual s(a, b) = edgeCost cost s(a, b)










end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchWitnesses

/-! matching/WeightedCacheMerge.lean -/
section RppSource_WeightedCacheMerge
namespace VehicleRoutingSurvey.Routing

/-- One cache cell stores an actual least-slack constraint, or is empty when its group is empty. -/
structure LeastSlackEntry {Event : Type*} (full : List (DualSlack Event))
    (cached : Option (DualSlack Event)) : Prop where
  sound : ∀ {rep}, cached = some rep → rep ∈ full
  covers : ∀ x ∈ full, ∃ rep, cached = some rep ∧ rep.slack ≤ x.slack







end VehicleRoutingSurvey.Routing
end RppSource_WeightedCacheMerge

/-! matching/MatchingClassifyEventRAM.lean -/
section RppSource_MatchingClassifyEventRAM
namespace VehicleRoutingSurvey.Routing



def matchingEventLeftRep (s : ArithmeticState) : ℕ :=
  s.nm (s.nr 57 + (matchingOriginalGrowthEvent s).1)

def matchingEventRightRep (s : ArithmeticState) : ℕ :=
  s.nm (s.nr 57 + (matchingOriginalGrowthEvent s).2)

def matchingEventClass (s : ArithmeticState) : ℕ :=
  if s.nr 55 ≤ (matchingOriginalGrowthEvent s).2 then 2
  else if s.nm (s.nr 51 + matchingEventLeftRep s) = 0 ∨ s.nm (s.nr 51 + matchingEventRightRep s) = 0
    then 0 else 1

/-- Decode the selected dictionary record. Tag zero is growth, tag two is a cut
expansion, and tag one requires tracing two outer representatives in registers 0 and 2.
Registers 91–93 retain the selected ID and the original dictionary endpoints. -/
def classifyMatchingSelectedEvent : List ArithmeticInstruction :=
  [.natConst 14 0, .natAdd 91 1 14, .natSub 6 1 9, .natAdd 6 6 6, .natAdd 6 54 6,
   .natLoad 92 6, .natAdd 6 6 9, .natLoad 93 6, .natBranch 55 93 23 9,
   .natAdd 6 57 92, .natLoad 0 6, .natAdd 6 57 93, .natLoad 2 6,
   .natAdd 6 51 0, .natLoad 10 6, .natAdd 6 51 2, .natLoad 11 6,
   .natBranch 10 14 21 18, .natBranch 11 14 21 19,
   .natConst 35 1, .jump 25, .natConst 35 0, .jump 25, .natConst 35 2, .jump 25]





end VehicleRoutingSurvey.Routing
end RppSource_MatchingClassifyEventRAM

/-! matching/MatchingEventMemory.lean -/
section RppSource_MatchingEventMemory
namespace VehicleRoutingSurvey.Routing

/-- Event identifiers address pairs of natural words. The compact dimension is the
second-word code for the registered cut at the first-word representative. -/
def decodeMatchingDictionaryEvent (k : ℕ) (cutAt : Fin k → Finset (Fin k))
    (s : ArithmeticState) (id : ℕ) : Option (MatchingDualEvent k) :=
  let slot := id - 1
  let address := s.nr 54 + (slot + slot)
  let a := s.nm address
  let b := s.nm (address + 1)
  if id = 0 then none
  else if first : a < k then
    if second : b < k then some (.edge s(⟨a, first⟩, ⟨b, second⟩))
    else if b = k then some (.cut (cutAt ⟨a, first⟩))
    else none
  else none

def MatchingEventRecord {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (words : ℕ × ℕ) :
    MatchingDualEvent k → Prop
  | .edge e => ∃ u v : Fin k, words = (u.val, v.val) ∧ e = s(u, v)
  | .cut B => ∃ u : Fin k, words = (u.val, k) ∧ B = cutAt u






end VehicleRoutingSurvey.Routing
end RppSource_MatchingEventMemory

/-! matching/MatchingCandidateMemory.lean -/
section RppSource_MatchingCandidateMemory
namespace VehicleRoutingSurvey.Routing

/-- Read a candidate using the same identifier and event dictionary as the selector. -/
def readMatchingCandidate {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    (s : ArithmeticState) (i : ℕ) : Option (DualSlack (MatchingDualEvent k)) :=
  (decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58 + i))).map
    fun event => ⟨event, s.rm (s.nr 59 + i), s.rm (s.nr 60 + i)⟩

/-- An occupied row refers to its own dictionary record, which is a valid event. -/
def MatchingCandidateRowValid {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    (s : ArithmeticState) (i : ℕ) : Prop :=
  let id := s.nm (s.nr 58 + i)
  id = 0 ∨ (id = i + 1 ∧ ∃ event, decodeMatchingDictionaryEvent k cutAt s id = some event)








end VehicleRoutingSurvey.Routing
end RppSource_MatchingCandidateMemory

/-! matching/MatchingPairBucketMemory.lean -/
section RppSource_MatchingPairBucketMemory
namespace VehicleRoutingSurvey.Routing

/-- Bucket scores are stored with the common outer-edge offset already added. -/
def readMatchingPairBucket {k : ℕ} (s : ArithmeticState) (i : ℕ) :
    Option (DualSlack (MatchingDualEvent k)) :=
  let addr := s.nr 65 + (i + i)
  let a := s.nm addr
  let b := s.nm (addr + 1)
  if first : a < k then
    if second : b < k then some ⟨.edge s(⟨a, first⟩, ⟨b, second⟩), s.rm (s.nr 66 + i), 2⟩ else none
  else none

def MatchingPairBucketValid (k : ℕ) (s : ArithmeticState) (i : ℕ) : Prop :=
  let addr := s.nr 65 + (i + i)
  s.nm addr < k → s.nm (addr + 1) < k










end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairBucketMemory

/-! matching/MatchingGrowCacheRows.lean -/
section RppSource_MatchingGrowCacheRows
namespace VehicleRoutingSurvey.Routing

/-- The three candidate ranges and the pair buckets occupy separate memory ranges. -/
structure MatchingCacheLayout (k : ℕ) (s : ArithmeticState) : Prop where
  dimension : s.nr 55 = k
  rows : s.nr 61 = 3 * k
  idsBefore : s.nr 58 + s.nr 61 ≤ s.nr 54
  recordsBefore : s.nr 54 + 2 * s.nr 61 ≤ s.nr 65
  slacksBefore : s.nr 59 + s.nr 61 ≤ s.nr 60
  ratesBefore : s.nr 60 + s.nr 61 ≤ s.nr 66






end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRows

/-! matching/MatchingExpansionGeometry.lean -/
section RppSource_MatchingExpansionGeometry
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The live cyclic record of one blossom, with the current child bases and
its original witnesses in forward traversal order. Logical geometry is
independent of the scratch registers used to select the blossom. -/
structure MatchingExpansionGeometry {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)} (registry : MatchingExpansionChildPorts state B)
    (tree : MatchingMemberTree) (base : Fin k) where
  members : MatchingChildMemberTree registry tree
  cycle : List (Fin k)
  edges : Fin cycle.length → Fin k × Fin k
  baseSlot : Fin cycle.length
  children : List (Fin k)
  distinct : cycle.Nodup
  odd : Odd cycle.length
  rotate : cycle.rotate baseSlot.val = base :: children
  atBase : cycle[baseSlot.val] = base
  ports : registry.ports = cycle.toFinset
  source : ∀ i : Fin cycle.length, (edges i).1 ∈ registry.block (cycle.get i)
  target : ∀ i : Fin cycle.length, (edges i).2 ∈ registry.block
    (cycle.get ⟨(i.val + 1) % cycle.length, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)
  tight : ∀ i, oddCutDualEdgeValue state.cuts state.potential state.cutDual s((edges i).1, (edges i).2) =
    edgeCost cost s((edges i).1, (edges i).2)
  matched : ∀ a b, s(a,b) ∈ alternatingEdges children → state.partialMate a = some b ∧ state.partialMate b = some a







end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionGeometry

/-! matching/MatchingCacheGroups.lean -/
section RppSource_MatchingCacheGroups
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

inductive MatchingCandidateGroup (n : ℕ)
  | outer (blockRep : Fin n)
  | incoming (originalTarget : Fin n)
  | cut (blockRep : Fin n)







noncomputable def incomingCandidateRate {n : ℕ} (role : AlternatingForestRole (Fin n)) : ℝ :=
  match role with | .unlabelled => 1 | _ => 0

def MatchingCandidateGroup.admits {n : ℕ} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks Finset.univ cuts) (forest : AlternatingForestState (Fin n))
    (rep : Finset (Fin n) → Fin n) (d : DualSlack (MatchingDualEvent n)) : MatchingCandidateGroup n → Prop
  | .outer i => d.rate = 2 ∧ ∃ u v, d.event = .edge s(u, v) ∧ rep (blocks.block u) = i
  | .incoming v => d.rate = incomingCandidateRate (forest.role (rep (blocks.block v))) ∧
      ∃ u, d.event = .edge s(u, v) ∧ blocks.block u ≠ blocks.block v ∧
        (∃ parent, forest.role (rep (blocks.block u)) = .outer parent) ∧
        (forest.role (rep (blocks.block v)) = .unlabelled ∨
          ∃ parent, forest.role (rep (blocks.block v)) = .inner parent)
  | .cut i => d.rate = 1 ∧ ∃ S, d.event = .cut S ∧ rep S = i







end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheGroups

/-! matching/MatchingActiveSelection.lean -/
section RppSource_MatchingActiveSelection
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Address the three candidate ranges by their physical row index. -/
def MatchingCandidateGroup.slot {k : ℕ} : MatchingCandidateGroup k → ℕ
  | .outer u => u.val
  | .incoming v => k + v.val
  | .cut u => 2 * k + u.val










end VehicleRoutingSurvey.Routing
end RppSource_MatchingActiveSelection

/-! matching/MatchingTypedDispatch.lean -/
section RppSource_MatchingTypedDispatch
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The classified dictionary event with its typed original ports and search labels. -/
def MatchingEventClassView {k : ℕ} {cuts : Finset (Finset (Fin k))}
    (blocks : TopLevelMatchingBlocks Finset.univ cuts) (forest : AlternatingForestState (Fin k))
    (rep : Finset (Fin k) → Fin k) (cutAt : Fin k → Finset (Fin k))
    (s : ArithmeticState) (event : MatchingDualEvent k) : Prop :=
    match event with
    | .cut S => ∃ u : Fin k, matchingOriginalGrowthEvent s = (u.val, k) ∧ S = cutAt u ∧
        matchingEventClass s = 2 ∧ S ∈ Finset.univ.image blocks.block ∧ S.card ≠ 1 ∧
        ∃ parent, forest.role (rep S) = .inner parent
    | .edge e => ∃ u v : Fin k, matchingOriginalGrowthEvent s = (u.val, v.val) ∧ e = s(u, v) ∧
        blocks.block u ≠ blocks.block v ∧ matchingEventLeftRep s = (rep (blocks.block u)).val ∧
        matchingEventRightRep s = (rep (blocks.block v)).val ∧
        let i := rep (blocks.block u)
        let j := rep (blocks.block v)
        (matchingEventClass s = 1 ∧ ∃ p q, forest.role i = .outer p ∧ forest.role j = .outer q) ∨
        (matchingEventClass s = 0 ∧
          ((∃ p, forest.role i = .outer p ∧ forest.role j = .unlabelled) ∨
            (∃ p, forest.role i = .unlabelled ∧ forest.role j = .outer p)))




end VehicleRoutingSurvey.Routing
end RppSource_MatchingTypedDispatch

/-! matching/MatchingSearchSelection.lean -/
section RppSource_MatchingSearchSelection
namespace VehicleRoutingSurvey.Routing

noncomputable def matchingSearchSlacks {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) : List (DualSlack (MatchingDualEvent k)) :=
  let label := part.dualLabel forest positive
  matchingDualSlacks cost (compactMatchingEdges k) state.cuts state.potential
    (forestVertexDirection part.blocks label) state.cutDual (forestCutDirection part.blocks label)

/-- The table used by the selector at the start of an active search iteration. -/
structure MatchingSearchRows {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (cutAt : Fin k → Finset (Fin k))
    (s : ArithmeticState) : Prop where
  layout : MatchingCacheLayout k s
  count : s.nr 8 = s.nr 61
  ids : s.nr 3 = s.nr 58
  slacks : s.nr 4 = s.nr 59
  rates : s.nr 5 = s.nr 60
  valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i
  least : ∀ group : MatchingCandidateGroup k,
    LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits part.blocks forest (part.representativeOf positive) d)))
      (readMatchingCandidate cutAt s group.slot)






end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchSelection

/-! matching/MatchingRegistryUnique.lean -/
section RppSource_MatchingRegistryUnique
namespace VehicleRoutingSurvey.Routing

namespace MatchingMemberTree







end MatchingMemberTree

/-- Only nonzero top-level registry entries can contribute live blossom nodes.
Each typed tree is determined by that entry and the immutable cycle words. -/
structure MatchingTopMemberTrees (k : ℕ) (s : ArithmeticState) where
  tree : Fin k → MatchingMemberTree
  roots : ∀ v : Fin k, (tree v).rootKeys =
    let blossom := s.nm (s.nr 74 + v.val)
    if blossom = 0 then [] else [MatchingMemberTree.rootKey v.val blossom]
  proper : ∀ v, (tree v).proper
  encoded : ∀ v, (tree v).encoded s.nm (s.nr 77) (s.nr 78)




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryUnique

/-! matching/MatchingExpansionSelection.lean -/
section RppSource_MatchingExpansionSelection
namespace VehicleRoutingSurvey.Routing

/-- A cut dictionary port is its active top representative. Empty entries
cannot decode to a live cut. -/
def matchingTopCutAt {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (v : Fin k) : Finset (Fin k) :=
  if part.representative v = v then part.blocks.block v else ∅















end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSelection

/-! matching/MatchingRebaseStack.lean -/
section RppSource_MatchingRebaseStack
namespace VehicleRoutingSurvey.Routing







/-- Recompute the stack base at the start of each augmentation because other
event handlers use registers 81 and 82 as scratch. -/
def resetMatchingRebaseJobsBlock : List ArithmeticInstruction :=
  [.natAdd 6 55 55, .natAdd 6 6 55, .natAdd 81 80 6, .natConst 82 0]



/-- Pop the next registered node and desired exposed vertex into registers 22 and 29. -/
def popMatchingRebaseJobBlock : List ArithmeticInstruction :=
  [.natSub 82 82 9, .natAdd 6 82 82, .natAdd 6 81 6,
   .natLoad 22 6, .natAdd 6 6 9, .natLoad 29 6]




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseStack

/-! matching/MatchingRebaseWrite.lean -/
section RppSource_MatchingRebaseWrite
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Install the chosen original edge and record its two endpoints as the roots of the
two children. Registers 28 and 7 are their cycle indices. -/
def installRebasedCyclePairBlock : List ArithmeticInstruction :=
  [.natAdd 6 50 12, .natStore 6 13, .natAdd 6 50 13, .natStore 6 12,
   .natAdd 6 28 28, .natAdd 6 6 6, .natAdd 6 18 6, .natStore 6 12,
   .natAdd 6 7 7, .natAdd 6 6 6, .natAdd 6 18 6, .natStore 6 13]







private def pushMatchingRebaseJob (node port : ℕ) : List ArithmeticInstruction :=
  [.natAdd 6 82 82, .natAdd 6 81 6, .natStore 6 node, .natAdd 6 6 9,
   .natStore 6 port, .natAdd 82 82 9]



/-- A singleton child has identifier zero. Only registered child nodes need a further
rebasing job after their crossing mate and exposed original have been chosen. -/
def queueMatchingRebaseChildBlock (node port : ℕ) : List ArithmeticInstruction :=
  branchOnAtMost node 14 [] (pushMatchingRebaseJob node port)



/-- Save the left index, read and install one chosen crossing pair, and enqueue its two
registered child nodes. The caller advances once more to start the next pair. -/
def rebaseMatchingCyclePairBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock (appendBlock [.natAdd 28 7 14] readRebasedCyclePairBlock)
    installRebasedCyclePairBlock) (queueMatchingRebaseChildBlock 11 12)) (queueMatchingRebaseChildBlock 25 13)








end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseWrite

/-! matching/MatchingRebaseNode.lean -/
section RppSource_MatchingRebaseNode
namespace VehicleRoutingSurvey.Routing

def startMatchingRebaseChildSearch : List ArithmeticInstruction :=
  [.natAdd 6 79 29, .natLoad 27 6, .natAdd 46 19 14, .natConst 47 0]

def saveMatchingRebaseChildIndex : List ArithmeticInstruction :=
  [.natAdd 46 7 14, .natAdd 47 25 14]

def selectMatchingRebaseChild : List ArithmeticInstruction :=
  branchOnAtMost 15 27 (branchOnAtMost 27 15 saveMatchingRebaseChildIndex []) []

def considerMatchingRebaseChild : List ArithmeticInstruction :=
  appendBlock readMatchingCycleChild selectMatchingRebaseChild

/-- Replace the free child's representative with the requested exposed original.
The external edge already occupies that original's mate slot. -/
def writeMatchingRebaseFreeChildBlock : List ArithmeticInstruction :=
  [.natAdd 7 46 14, .natAdd 6 7 7, .natAdd 6 6 6, .natAdd 6 18 6, .natStore 6 29]



def locateMatchingRebaseFreeChild : List ArithmeticInstruction :=
  appendBlock startMatchingRebaseChildSearch
    (countedLoopFromZero 9 7 19 considerMatchingRebaseChild)

def rebaseMatchingPairIteration : List ArithmeticInstruction :=
  appendBlock rebaseMatchingCyclePairBlock advanceMatchingCycleIndexBlock

def rebaseMatchingPairLoop : List ArithmeticInstruction :=
  countedLoopFromZero 9 24 95 rebaseMatchingPairIteration

def rebaseMatchingPairedChildren : List ArithmeticInstruction :=
  appendBlock [.natSub 46 19 9] (appendBlock halveExpansionDistance rebaseMatchingPairLoop)

/-- Update the child chosen by the descendant map, then match the remaining children. -/
def rebaseMatchingCycleBlock : List ArithmeticInstruction :=
  appendBlock locateMatchingRebaseFreeChild (appendBlock writeMatchingRebaseFreeChildBlock
    (appendBlock (queueMatchingRebaseChildBlock 47 29)
      (appendBlock advanceMatchingCycleIndexBlock rebaseMatchingPairedChildren)))

/-- Retain the popped node while walking its descendants, then reload its own header. -/
def loadMatchingRebaseCycleBlock : List ArithmeticInstruction :=
  appendBlock [.natAdd 27 22 14] (appendBlock mapMatchingCycleNodeMembers
    (appendBlock [.natAdd 22 27 14] readMatchingCycleHeader))

/-- Pop one blossom, locate the child of its requested exposed original, and pair the
rest consecutively in cycle order. Processing nested children is deferred to the work stack. -/
def rebaseMatchingNodeJobBlock : List ArithmeticInstruction :=
  appendBlock popMatchingRebaseJobBlock (appendBlock loadMatchingRebaseCycleBlock rebaseMatchingCycleBlock)

/-- Each registered node is processed at most once. The stage invariant bounds the
number of live blossom nodes by the number of original vertices. -/
def rebaseMatchingQueuedNodesBlock : List ArithmeticInstruction :=
  countedLoopFromZero 9 43 55 (branchOnUnequal 82 14 rebaseMatchingNodeJobBlock)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseNode

/-! matching/MatchingAugmentApply.lean -/
section RppSource_MatchingAugmentApply
namespace VehicleRoutingSurvey.Routing

def initializeAugmentationRepresentative : List ArithmeticInstruction :=
  [.natAdd 6 89 44, .natStore 6 44]

private def moveMatchingAugmentationRepresentative (port : ℕ) : List ArithmeticInstruction :=
  [.natAdd 6 57 port, .natLoad 26 6, .natAdd 6 89 26, .natStore 6 port,
   .natAdd 6 74 26, .natLoad 22 6, .natStore 6 14, .natAdd 6 74 port, .natStore 6 22]

/-- Move the selected port's top-level node entry to the newly exposed original and
record the old-to-new representative for the final sweep over original vertices. -/
def recordAugmentationRepresentativeBlock (port : ℕ) : List ArithmeticInstruction :=
  appendBlock (moveMatchingAugmentationRepresentative port) (queueMatchingRebaseChildBlock 22 port)





def loadInstallAugmentationCrossingBlock : List ArithmeticInstruction :=
  [.natAdd 6 44 44, .natAdd 6 86 6, .natLoad 12 6, .natAdd 6 6 9, .natLoad 13 6,
   .natAdd 6 50 12, .natStore 6 13, .natAdd 6 50 13, .natStore 6 12]

def installAugmentationCrossingBlock : List ArithmeticInstruction :=
  appendBlock loadInstallAugmentationCrossingBlock
    (appendBlock (recordAugmentationRepresentativeBlock 12) (recordAugmentationRepresentativeBlock 13))

def remapAugmentationOriginalBlock : List ArithmeticInstruction :=
  [.natAdd 15 57 44, .natLoad 26 15, .natAdd 6 89 26, .natLoad 26 6, .natStore 15 26]



/-- Install the alternating path's new crossing edges, update the top representatives,
then rebase the affected laminar trees so the original mate table is consistent. -/
def applyMatchingAugmentationCrossingsBlock : List ArithmeticInstruction :=
  appendBlock [.natConst 9 1, .natConst 14 0] (appendBlock resetMatchingRebaseJobsBlock
    (appendBlock (countedLoopFromZero 9 44 55 initializeAugmentationRepresentative)
      (appendBlock (countedLoopFromZero 9 44 87 installAugmentationCrossingBlock)
        (appendBlock (countedLoopFromZero 9 44 55 remapAugmentationOriginalBlock) rebaseMatchingQueuedNodesBlock))))


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentApply

/-! matching/MatchingAugmentCrossingCell.lean -/
section RppSource_MatchingAugmentCrossingCell
namespace VehicleRoutingSurvey.Routing



/-- Append a pair of already-loaded original endpoints. Register 86 is the
output base and register 87 counts the pairs already emitted. -/
def appendAugmentationCrossingPair (first second : ℕ) : List ArithmeticInstruction :=
  [.natAdd 5 87 87, .natAdd 5 86 5, .natStore 5 first, .natAdd 5 5 6,
    .natStore 5 second, .natAdd 87 87 6]













/-- Read the saved original witness for the child found at the current
index in one trace. The database stores every edge from parent to child. -/
def readAugmentationTraceWitness : List ArithmeticInstruction :=
  [.natAdd 5 3 7, .natLoad 15 5, .natAdd 5 15 15, .natAdd 5 90 5,
    .natLoad 16 5, .natAdd 5 5 6, .natLoad 17 5]





def appendAugmentationTraceWitness (flip : Bool) : List ArithmeticInstruction :=
  appendBlock readAugmentationTraceWitness
    (appendAugmentationCrossingPair (if flip then 17 else 16) (if flip then 16 else 17))



end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossingCell

/-! matching/MatchingAugmentCrossingLoop.lean -/
section RppSource_MatchingAugmentCrossingLoop
namespace VehicleRoutingSurvey.Routing







private def scanAugmentationTraceTail (forward : Bool) : List ArithmeticInstruction :=
  [.natSub 4 4 18, (if forward then .natAdd 7 7 18 else .natSub 7 7 18), .jump 0]

/-- Register 4 counts the remaining vertices, including the final outer
endpoint. Advance by two after each emitted edge. -/
def scanAugmentationTraceBlock (forward : Bool) : List ArithmeticInstruction :=
  [.natBranch 4 6 17 1] ++
    (appendAugmentationTraceWitness forward).map (relocateInstruction 1) ++
    scanAugmentationTraceTail forward











end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossingLoop

/-! matching/AlternatingForestTraceRAM.lean -/
section RppSource_AlternatingForestTraceRAM
namespace VehicleRoutingSurvey.Routing







/-- Register 2 is the current vertex, 3 the output base, 4 the output
length, and 6 the constant 1. Registers 52 and 55 hold the parent base
and compact dimension. Scratch register 5 addresses the output and input. -/
def traceForestParentLoop : List ArithmeticInstruction :=
  [.natBranch 55 2 7 1, .natAdd 5 3 4, .natStore 5 2,
    .natAdd 5 52 2, .natLoad 2 5, .natAdd 4 4 6, .jump 0]

















end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTraceRAM

/-! matching/MatchingAugmentTraceLeg.lean -/
section RppSource_MatchingAugmentTraceLeg
namespace VehicleRoutingSurvey.Routing

def prepareAugmentationTraceLeg (forward : Bool) : List ArithmeticInstruction :=
  [.natConst 6 1, .natConst 18 2, .natConst 19 0,
    .natAdd 3 (if forward then 84 else 83) 19, .natAdd 4 (if forward then 11 else 10) 19,
    if forward then .natConst 7 1 else .natSub 7 4 18]





def writeAugmentationTraceLeg (forward : Bool) : List ArithmeticInstruction :=
  appendBlock (prepareAugmentationTraceLeg forward) (scanAugmentationTraceBlock forward)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentTraceLeg

/-! matching/MatchingAugmentCrossings.lean -/
section RppSource_MatchingAugmentCrossings
namespace VehicleRoutingSurvey.Routing



def writeAugmentationCrossingsBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock [.natConst 87 0] (writeAugmentationTraceLeg false))
    (appendAugmentationCrossingPair 92 93)) (writeAugmentationTraceLeg true)







end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossings

/-! matching/MatchingStageCountEncoding.lean -/
section RppSource_MatchingStageCountEncoding
namespace VehicleRoutingSurvey.Routing

def MatchingMemberTree.registryIds : MatchingMemberTree → List ℕ
  | .nil => []
  | .leaf _ tail => tail.registryIds
  | .blossom _ node children tail => node :: (children.registryIds ++ tail.registryIds)

def MatchingTopMemberTrees.registryIds {k : ℕ} {s : ArithmeticState} (record : MatchingTopMemberTrees k s) : List ℕ :=
  (List.finRange k).flatMap fun v => (record.tree v).registryIds

noncomputable def matchingLiveRegistryIds (k : ℕ) (s : ArithmeticState) : List ℕ := by
  classical
  exact if h : Nonempty (MatchingTopMemberTrees k s) then (Classical.choice h).registryIds else []



/-- Count nonouter originals and outer representatives directly from their table
words. The live, uniquely decoded registry gives the inherited blossom count. -/
noncomputable def matchingStageCountsFromRAM (k : ℕ) (s : ArithmeticState) (initialNode : ℕ) : MatchingStageCounts :=
  ⟨((Finset.univ : Finset (Fin k)).filter (fun v => s.nm (s.nr 51 + s.nm (s.nr 57 + v.val)) ≠ 1)).card,
    ((matchingLiveRegistryIds k s).filter fun node => decide (node < initialNode)).length,
    ((Finset.univ : Finset (Fin k)).filter (fun v => s.nm (s.nr 57 + v.val) = v.val ∧ s.nm (s.nr 51 + v.val) = 1)).card⟩

def CompactMatchingPartition.outerBlock {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (B : Finset (Fin k)) : Prop :=
  alternatingRoleCode (forest.role (part.representativeOf positive B)) = 1

noncomputable instance {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k) :
    DecidablePred (part.outerBlock forest positive) := fun B =>
      inferInstanceAs (Decidable (alternatingRoleCode (forest.role (part.representativeOf positive B)) = 1))




end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageCountEncoding

/-! matching/MatchingCycleRecordOrder.lean -/
section RppSource_MatchingCycleRecordOrder
namespace VehicleRoutingSurvey.Routing

def matchingCycleRecordStart (s : ArithmeticState) (node : ℕ) : ℕ := s.nm (s.nr 77 + node)

def matchingCycleRecordEnd (s : ArithmeticState) (node : ℕ) : ℕ :=
  matchingCycleRecordStart s node + 4 * s.nm (s.nr 78 + node)

def matchingRebaseScratchEnd (s : ArithmeticState) : ℕ := s.nr 80 + 5 * s.nr 55

/-- Allocation appends ordered cycle rows after both traversal stacks.
Retired registry IDs retain their reserved intervals. -/
structure MatchingCycleRecordOrder (s : ArithmeticState) : Prop where
  scratch : matchingRebaseScratchEnd s ≤ s.nr 68
  cursor : 1 ≤ s.nr 76
  bounded : ∀ node, 0 < node → node < s.nr 76 →
    matchingRebaseScratchEnd s ≤ matchingCycleRecordStart s node ∧ matchingCycleRecordEnd s node ≤ s.nr 68
  ordered : ∀ left right, 0 < left → left < right → right < s.nr 76 →
    matchingCycleRecordEnd s left ≤ matchingCycleRecordStart s right










end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordOrder

/-! matching/MatchingRebaseArchive.lean -/
section RppSource_MatchingRebaseArchive
namespace VehicleRoutingSurvey.Routing

def matchingRebaseNodeState (s : ArithmeticState) (node : ℕ) : ArithmeticState :=
  {s with nr := Function.update s.nr 22 node}
















end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseArchive

/-! matching/MatchingLiveCycleGeometry.lean -/
section RppSource_MatchingLiveCycleGeometry
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Typed forward edge words of an allocated node. This also describes an
interior node when the top-node table no longer points directly to it. -/
structure MatchingNodeCycleRows {k : ℕ} (s : ArithmeticState) (node : ℕ)
    (cycle : List (Fin k)) (edge : Fin cycle.length → Fin k × Fin k) : Prop where
  length : s.nm (s.nr 78 + node) = cycle.length
  records : ∀ i : Fin cycle.length,
    let row := matchingCycleChildAt s.nm (matchingCycleRecordStart s node + 4*i.val)
    row.representative = (cycle.get i).val ∧
      (row.endpointA, row.endpointB) = ((edge i).1.val,(edge i).2.val)



/-- All matching edges internal to the blossom after its distinguished port
has been removed. -/
noncomputable def matchingCycleInterior {k : ℕ} {cost : Fin k → Fin k → ℝ} (state : CompactMatchingPrimalDual k cost)
    (B : Finset (Fin k)) (p : Fin k) : Finset (Sym2 (Fin k)) := by
  classical
  exact state.edges.filter fun e => ∀ v ∈ e, v ∈ B.erase p

/-- Mathematical content of one registered node, independent of temporary
registers and of its current position in the registry forest. -/
structure MatchingLiveCycle {k : ℕ} {cost : Fin k → Fin k → ℝ} (state : CompactMatchingPrimalDual k cost)
    (node : Finset (Fin k) → ℕ) (B : Finset (Fin k)) where
  base : Fin k
  tree : MatchingMemberTree
  ports : MatchingExpansionChildPorts state B
  geometry : MatchingExpansionGeometry ports tree base
  arity : tree.arity = geometry.cycle.length
  keys : tree.rootKeys.map Prod.fst = geometry.cycle.map Fin.val
  owner : ∀ job ∈ tree.jobs none, ∀ p : Fin k, job.representative = p.val →
    p ∈ ports.ports ∧ ∀ v : Fin k, v.val ∈ job.tree.leaves ↔ v ∈ ports.block p
  childNode : ∀ job ∈ tree.jobs none, ∀ p : Fin k, job.representative = p.val →
    job.node = if (ports.block p).card = 1 then 0 else node (ports.block p)
  descendants : ∀ C ∈ state.cuts.erase B, C ⊆ B → ∃ p ∈ ports.ports, C ⊆ ports.block p
  internal : IsPerfectMatchingOn (B.erase base) (matchingCycleInterior state B base)
  matchedRow : ∀ i : Fin geometry.cycle.length,
    let p := geometry.cycle.get i
    let q := geometry.cycle.get ⟨(i.val+1) % geometry.cycle.length, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    state.partialMate p = some q → geometry.edges i = (p,q)

/-- The stored child labels and ordered endpoints, at a known allocated ID.
These same row witnesses are consumed by expansion and by recursive rebase. -/
structure MatchingLiveCycleMemory {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)} (entry : MatchingLiveCycle state node B)
    (s : ArithmeticState) where
  members : MatchingMemberRoot (matchingRebaseNodeState s (node B)) entry.tree
  rows : MatchingNodeCycleRows s (node B) entry.geometry.cycle entry.geometry.edges



end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleGeometry

/-! matching/MatchingBlossomRegistry.lean -/
section RppSource_MatchingBlossomRegistry
namespace VehicleRoutingSurvey.Routing

/-- With (k) compact vertices, a search has at most (6k) events and there are at
most (k/2) augmentations. Allocate fresh node identifiers across the whole run. -/
def matchingBlossomCapacity (k : ℕ) : ℕ := 3 * (k * k) + 1

















end VehicleRoutingSurvey.Routing
end RppSource_MatchingBlossomRegistry

/-! matching/MatchingRegistryBudget.lean -/
section RppSource_MatchingRegistryBudget
namespace VehicleRoutingSurvey.Routing

/-- New identifiers can be allocated only when an event spends credit. This
ties the monotonically increasing registry cursor to the global header capacity. -/
structure MatchingRegistryBudget (k stage : ℕ) (s : ArithmeticState) (counts : MatchingStageCounts) : Prop where
  cutoff : s.nr 39 ≤ 6 * k * stage + 1
  allowance : s.nr 76 + counts.credit ≤ s.nr 39 + 6 * k
  cutoff_le_cursor : s.nr 39 ≤ s.nr 76












end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryBudget

/-! matching/MatchingRegistryView.lean -/
section RppSource_MatchingRegistryView
namespace VehicleRoutingSurvey.Routing

/-- The live registry contains exactly the current cuts, with one allocated ID
per cut. Its immutable cycle records lie above the writable cache ranges. -/
structure MatchingRegistryView {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (dual : MatchingSearchDualMemory part forest s) where
  trees : MatchingTopMemberTrees k s
  readable : ∀ v, (trees.tree v).readable s.nm (s.nr 77) (s.nr 78) (fun a => s.nr 65 + 2 * (k * k) ≤ a)
  unique : trees.registryIds.Nodup
  keys : ∀ n, n ∈ trees.registryIds ↔ ∃ B ∈ state.cuts, dual.node B = n
  allocated : ∀ B ∈ state.cuts, dual.node B < s.nr 76
  nontrivial : ∀ B ∈ state.cuts, 1 < B.card
  laminar : ∀ A ∈ state.cuts, ∀ B ∈ state.cuts, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A
  nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v












end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryView

/-! matching/MatchingLiveCycles.lean -/
section RppSource_MatchingLiveCycles
namespace VehicleRoutingSurvey.Routing

/-- Every current cut has one live cycle at its allocated ID. Tops are the
same trees used by the selector budget and each registered child refers to
the corresponding subtree and its current exposed original port. -/
structure MatchingLiveCycles {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {s : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    (registry : MatchingRegistryView dual) where
  entry : ∀ B ∈ state.cuts, MatchingLiveCycle state dual.node B
  memory : ∀ B h, MatchingLiveCycleMemory (entry B h) s
  top : ∀ (p : Fin k) (h : part.blocks.block p ∈ state.cuts), part.representative p = p →
    let e := entry (part.blocks.block p) h
    e.base = p ∧ registry.trees.tree p = .blossom p.val (dual.node (part.blocks.block p)) e.tree .nil
  child : ∀ B h, ∀ job ∈ (entry B h).tree.jobs none, ∀ sub, job.children = some sub →
    ∃ (C : Finset (Fin k)) (hc : C ∈ state.cuts), dual.node C = job.node ∧ (entry C hc).tree = sub ∧
      (entry C hc).base.val = job.representative ∧ C = (entry B h).ports.block (entry C hc).base
  ids : ∀ B h, ∀ n ∈ (entry B h).tree.registryIds, n ∈ registry.trees.registryIds



end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycles

/-! matching/MatchingForestTraceSetup.lean -/
section RppSource_MatchingForestTraceSetup
namespace VehicleRoutingSurvey.Routing







def startMatchingForestTraceBlock (source output : ℕ) : List ArithmeticInstruction :=
  [.natConst 4 0, .natConst 6 1, .natAdd 2 source 4, .natAdd 3 output 4]



def publishMatchingForestTraceCountBlock (destination : ℕ) : List ArithmeticInstruction :=
  [.natConst 8 0, .natAdd destination 4 8]



def writeMatchingForestTraceBlock (source output destination : ℕ) : List ArithmeticInstruction :=
  appendBlock (appendBlock (startMatchingForestTraceBlock source output) traceForestParentLoop)
    (publishMatchingForestTraceCountBlock destination)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestTraceSetup

/-! matching/MatchingContractRowsRAM.lean -/
section RppSource_MatchingContractRowsRAM
namespace VehicleRoutingSurvey.Routing





def tracedRepresentative (s : ArithmeticState) (i : ℕ) : ℕ :=
  s.nm (s.nr 18 + i)

def tracedRepresentativeOuter (s : ArithmeticState) (i : ℕ) : Prop :=
  s.nm (s.nr 51 + tracedRepresentative s i) = 1

instance (s : ArithmeticState) (i : ℕ) : Decidable (tracedRepresentativeOuter s i) :=
  inferInstanceAs (Decidable (s.nm (s.nr 51 + tracedRepresentative s i) = 1))

/-- For a trace at register 18, append the current representative to the absorbed row
list exactly when its role is outer. Register 87 is the count already written. -/
def appendTracedOuterRep : List ArithmeticInstruction :=
  [.natAdd 6 18 7, .natLoad 10 6, .natAdd 6 51 10, .natLoad 11 6,
   .natBranch 11 9 5 10, .natBranch 9 11 6 10,
   .natAdd 6 86 87, .natStore 6 10, .natAdd 87 87 9, .jump 10]





def collectTracedOuterReps : List ArithmeticInstruction :=
  countedLoopFromZero 9 7 19 appendTracedOuterRep









/-- Write the common base once, then list the absorbed outer representatives along both
ancestor-exclusive traces. The trace case distinction has already found a common base. -/
def collectAbsorbedOuterRows : List ArithmeticInstruction :=
  appendBlock [.natStore 86 12, .natConst 87 1, .natConst 23 0, .natAdd 18 83 23, .natAdd 19 13 23]
    (appendBlock collectTracedOuterReps
      (appendBlock [.natAdd 18 84 23, .natAdd 19 14 23] collectTracedOuterReps))











end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractRowsRAM

/-! matching/MatchingRefreshRows.lean -/
section RppSource_MatchingRefreshRows
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

/-- Tables read by an outer original's complete cache sweep. The metric,
effective potentials, and representative and label data lie before the cache. -/
structure MatchingRefreshInput {k : ℕ} (s : ArithmeticState) (rep : Fin k → Fin k)
    (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) : Prop where
  layout : MatchingCacheLayout k s
  offsetsBefore : s.nr 21 + k ≤ s.nr 58
  representativesBefore : s.nr 57 + k ≤ s.nr 58
  rolesBefore : s.nr 51 + k ≤ s.nr 58
  metricBefore : s.nr 20 + k * k ≤ s.nr 59
  effectiveBefore : s.nr 62 + k ≤ s.nr 59
  offsets : ∀ j : Fin k, s.nm (s.nr 21 + j.val) = k * j.val
  representatives : ∀ j : Fin k, s.nm (s.nr 57 + j.val) = (rep j).val
  roles : ∀ r : Fin k, s.nm (s.nr 51 + r.val) = role r
  metric : ∀ i j : Fin k, s.rm (s.nr 20 + k * i.val + j.val) = cost i j
  potentials : ∀ j : Fin k, s.rm (s.nr 62 + j.val) = effective j















end VehicleRoutingSurvey.Routing
end RppSource_MatchingRefreshRows

/-! matching/MatchingStageStorage.lean -/
section RppSource_MatchingStageStorage
namespace VehicleRoutingSurvey.Routing

/-- Fixed base addresses shared by all four event handlers. The variable
cycle cursor and the two job-stack registers are tracked separately. -/
structure MatchingStageStorage (k : ℕ) (original s : ArithmeticState) : Prop where
  warm : MatchingWarmLayout s k
  inputFloor : s.nr 62 = original.nr 64
  nodes : s.nr 74 = s.nr 65+2*(k*k)
  cutDuals : s.nr 75 = s.nr 66+k*k
  starts : s.nr 77 = s.nr 74+k
  lengths : s.nr 78 = s.nr 77+matchingBlossomCapacity k
  traceLeft : s.nr 83 = s.nr 78+matchingBlossomCapacity k
  traceRight : s.nr 84 = s.nr 83+k
  traceMarks : s.nr 85 = s.nr 84+k
  witnesses : s.nr 90 = s.nr 85+k
  records : s.nr 86 = s.nr 90+2*k
  promotion : s.nr 88 = s.nr 86+k
  mask : s.nr 89 = s.nr 88+k
  memberMap : s.nr 79 = s.nr 89+k
  memberStack : s.nr 80 = s.nr 79+k
  metricBelowInput : s.nr 20+k*k ≤ s.nr 62








end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageStorage

/-! matching/MatchingAugmentCode.lean -/
section RppSource_MatchingAugmentCode
namespace VehicleRoutingSurvey.Routing

def prepareMatchingAugmentationBlock : List ArithmeticInstruction :=
  appendBlock writeAugmentationCrossingsBlock advanceMatchingEventDuals

def finishMatchingAugmentationBlock : List ArithmeticInstruction :=
  [.natConst 1 0, .natConst 33 0]

/-- Read the crossing witnesses before the dual sweep reuses the trace registers.
Advance the duals before changing any representatives, then publish the augmentation. -/
def matchingAugmentationHandlerBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock prepareMatchingAugmentationBlock applyMatchingAugmentationCrossingsBlock)
    finishMatchingAugmentationBlock

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCode

/-! matching/AlternatingForestTraceIndex.lean -/
section RppSource_AlternatingForestTraceIndex
namespace VehicleRoutingSurvey.Routing



def initializeForestTraceIndexCell : List ArithmeticInstruction :=
  [.natAdd 5 85 7, .natStore 5 55]

def initializeForestTraceIndexBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 55 initializeForestTraceIndexCell









def indexForestTraceCell : List ArithmeticInstruction :=
  [.natAdd 5 83 7, .natLoad 8 5, .natAdd 5 85 8, .natStore 5 7]

def indexForestTraceBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 10 indexForestTraceCell









end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTraceIndex

/-! matching/AlternatingForestAncestorRAM.lean -/
section RppSource_AlternatingForestAncestorRAM
namespace VehicleRoutingSurvey.Routing







/-- Read the right trace until its first vertex in the left index table. The
outputs are the shared vertex, left position, and right position in registers
12, 13, and 14. Exhaustion produces the sentinel and full lengths. -/
def findForestTraceSplitLoop : List ArithmeticInstruction :=
  [.natBranch 11 14 8 1, .natAdd 5 84 14, .natLoad 12 5, .natAdd 5 85 12,
    .natLoad 13 5, .natBranch 55 13 6 10, .natAdd 14 14 6, .jump 0,
    .natAdd 12 55 8, .natAdd 13 10 8]













end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAncestorRAM

/-! matching/MatchingForestTrace.lean -/
section RppSource_MatchingForestTrace
namespace VehicleRoutingSurvey.Routing

def prepareForestSplitScanBlock : List ArithmeticInstruction :=
  [.natConst 8 0, .natConst 14 0]



def traceMatchingForestBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock (appendBlock
    (appendBlock (writeMatchingForestTraceBlock 0 83 10) (writeMatchingForestTraceBlock 1 84 11))
      initializeForestTraceIndexBlock) indexForestTraceBlock) prepareForestSplitScanBlock)
    findForestTraceSplitLoop







end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestTrace

/-! matching/MatchingForestLinkMemory.lean -/
section RppSource_MatchingForestLinkMemory
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- When an outer child has a parent, their matching edge joins the actual
incoming and outgoing bases. The program retains these oriented endpoints. -/
structure MatchingForestLinkMemory {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (s : ArithmeticState) : Prop where
  inactive : ∀ v, part.representative v ≠ v → forest.role v = .unlabelled
  matched : ∀ {child parent}, forest.role child = .outer (some parent) →
    matchingForestWitnessAt s.nm (s.nr 90) child.val = (parent.val, child.val)








end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestLinkMemory

/-! matching/MatchingPairMeaning.lean -/
section RppSource_MatchingPairMeaning
namespace VehicleRoutingSurvey.Routing

/-- An original edge's normalized score while both endpoints are in outer blocks. -/
def normalizedOuterEdge {k : ℕ} (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ)
    (time : ℝ) (u v : Fin k) : DualSlack (MatchingDualEvent k) :=
  ⟨.edge s(u,v), time + time + (cost u v - effective u - effective v), 2⟩







/-- The full, ordered Cartesian product for a directed bucket, with normalized scores. -/
noncomputable def normalizedOuterPairEntries {k : ℕ} (rep : Fin k → Fin k) (cost : Fin k → Fin k → ℝ)
    (effective : Fin k → ℝ) (time : ℝ) (a b : Fin k) : List (DualSlack (MatchingDualEvent k)) :=
  ((List.finRange k).filter fun u => decide (rep u = a)).flatMap fun u =>
    ((List.finRange k).filter fun v => decide (rep v = b)).map (normalizedOuterEdge cost effective time u)



/-- Active outer pairs carry their normalized minimum. Slots indexed by an
original vertex which has not become outer are still empty. -/
structure MatchingSearchOuterBuckets {k : ℕ} (s : ArithmeticState) (rep : Fin k → Fin k)
    (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) : Prop where
  valid : ∀ i < k*k, MatchingPairBucketValid k s i
  least : ∀ a b : Fin k, a ≠ b → role a = 1 → role b = 1 →
    LeastSlackEntry (normalizedOuterPairEntries rep cost effective (s.rr 15) a b)
      (readMatchingPairBucket (k := k) s (k*a.val+b.val))
  inactive : ∀ a b : Fin k, role (rep a) ≠ 1 ∨ role (rep b) ≠ 1 →
    readMatchingPairBucket (k := k) s (k*a.val+b.val) = none





end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairMeaning

/-! matching/MatchingFreshCutOuter.lean -/
section RppSource_MatchingFreshCutOuter
namespace VehicleRoutingSurvey.Routing

/-- Each blossom allocated during the current stage lies wholly in outer
originals. This also applies if later contractions hide that blossom. -/
def MatchingFreshCutOuter {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (node : Finset (Fin k) → ℕ) (cutoff : ℕ) : Prop :=
  ∀ B ∈ state.cuts, cutoff ≤ node B → ∀ v ∈ B, (forest.role (part.representative v)).outerTag = true









end VehicleRoutingSurvey.Routing
end RppSource_MatchingFreshCutOuter

/-! matching/MatchingStageEntry.lean -/
section RppSource_MatchingStageEntry
namespace VehicleRoutingSurvey.Routing

/-- Data passed to event handlers after a stage is prepared. The registry and
selector tables carry their exact meanings at the current dual point. -/
structure MatchingActiveStage {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (cutAt : Fin k → Finset (Fin k))
    (original : ArithmeticState) (stage : ℕ) (s : ArithmeticState) where
  primal : CompactMatchingPrimalDualMemory state original s
  top : CompactTopMatching part
  internal : state.InternalCuts
  search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween
  witnesses : MatchingForestOriginalWitnesses part forest s
  links : MatchingForestLinkMemory part forest s
  dual : MatchingSearchDualMemory part forest s
  registry : MatchingRegistryView dual
  freshCuts : MatchingFreshCutOuter part forest dual.node (s.nr 39)
  rows : MatchingSearchRows part forest positive cutAt s
  pairs : MatchingSearchOuterBuckets s part.representative (fun v => alternatingRoleCode (forest.role v))
    cost (effectiveVertexPotential state.cuts state.potential state.cutDual)
  reads : MatchingRefreshInput s part.representative (fun v => alternatingRoleCode (forest.role v)) cost
    (effectiveVertexPotential state.cuts state.potential state.cutDual)
  budget : MatchingRegistryBudget k stage s (matchingStageCountsFromRAM k s (s.nr 39))
  winnerEmpty : s.nr 1 = 0
  unit : s.nr 9 = 1






end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageEntry

/-! matching/MatchingChosenStage.lean -/
section RppSource_MatchingChosenStage
namespace VehicleRoutingSurvey.Routing

/-- Physical state passed from the selector into tracing and the event arms.
The selector has advanced the slack entries. Vertex and cut dual arrays have
their old values until the common dual-update instructions run. -/
structure MatchingChosenStage {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (cutAt : Fin k → Finset (Fin k))
    (original s : ArithmeticState) where
  event : MatchingDualEvent k
  chosen : MatchingEventRecord cutAt (matchingOriginalGrowthEvent s) event
  kind : MatchingEventClassView part.blocks forest (part.representativeOf positive) cutAt s event
  adjustment : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
    (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
    (forestCutDirection part.blocks (part.dualLabel forest positive)) ⟨event, s.rr 1⟩
  primal : CompactMatchingPrimalDualMemory state original s
  dual : MatchingSearchDualMemory part forest s
  registry : MatchingRegistryView dual
  reads : MatchingRefreshInput s part.representative (fun v => alternatingRoleCode (forest.role v)) cost
    (effectiveVertexPotential state.cuts state.potential state.cutDual)
  witnesses : MatchingForestOriginalWitnesses part forest s
  links : MatchingForestLinkMemory part forest s
  pairs : MatchingSearchOuterBuckets s part.representative (fun v => alternatingRoleCode (forest.role v)) cost
    (effectiveVertexPotential state.cuts state.potential state.cutDual)
  valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i
  least : let direction := forestVertexDirection part.blocks (part.dualLabel forest positive)
    let cutDirection := forestCutDirection part.blocks (part.dualLabel forest positive)
    ∀ g : MatchingCandidateGroup k, LeastSlackEntry ((matchingDualSlacks cost (compactMatchingEdges k) state.cuts
      (fun v => state.potential v + s.rr 1 * direction v) direction
      (fun B => state.cutDual B + s.rr 1 * cutDirection B) cutDirection).filter fun d =>
      @decide _ (Classical.propDecidable (g.admits part.blocks forest (part.representativeOf positive) d)))
      (readMatchingCandidate cutAt s g.slot)




end VehicleRoutingSurvey.Routing
end RppSource_MatchingChosenStage

/-! matching/MatchingContractCacheRAM.lean -/
section RppSource_MatchingContractCacheRAM
namespace VehicleRoutingSurvey.Routing







/-- Read one old row from the list of absorbed outer representatives in register 86.
Register 17 is the surviving outer representative. A nonempty bucket is represented
by its flat index plus one. Its original endpoints can be read after the minimum scan. -/
def readContractedBucket : List ArithmeticInstruction :=
  [.natAdd 6 86 7, .natLoad 10 6, .natAdd 6 21 10, .natLoad 10 6, .natAdd 10 10 17,
   .natAdd 6 10 10, .natAdd 6 65 6, .natLoad 11 6, .natBranch 55 11 9 11,
   .natConst 0 0, .jump 14,
   .natAdd 0 10 9, .natAdd 6 66 10, .realLoad 0 6]





def considerContractedBucket : List ArithmeticInstruction :=
  appendBlock readContractedBucket mergeSlackEntryBlock









def minimumContractedBucket : List ArithmeticInstruction :=
  appendBlock [.natConst 1 0] (countedLoopFromZero 9 7 87 considerContractedBucket)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractCacheRAM

/-! matching/MatchingContractPublish.lean -/
section RppSource_MatchingContractPublish
namespace VehicleRoutingSurvey.Routing

def readMinimumContractedBucket : List ArithmeticInstruction :=
  [.natSub 18 1 9, .natAdd 6 18 18, .natAdd 6 65 6, .natLoad 15 6,
   .natAdd 6 6 9, .natLoad 16 6, .realAdd 5 15 15, .realSub 0 1 5]

/-- Publish the chosen absorbed row's original edge in both directions of the merged
bucket. Convert its normalization offset back to a raw slack for the selector table. -/
def publishMinimumContractedBucket : List ArithmeticInstruction :=
  appendBlock [.natConst 23 0, .natConst 14 0]
    (branchOnUnequal 1 23 (appendBlock readMinimumContractedBucket insertMatchingOuterEdgeBlock))





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractPublish

/-! matching/MatchingContractRepresentativesRAM.lean -/
section RppSource_MatchingContractRepresentativesRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

def originalTopRepresentative (s : ArithmeticState) (i : ℕ) : ℕ := s.nm (s.nr 57 + i)

def wasContractedRepresentative (s : ArithmeticState) (r : ℕ) : Prop := 0 < s.nm (s.nr 89 + r)

instance (s : ArithmeticState) (r : ℕ) : Decidable (wasContractedRepresentative s r) :=
  inferInstanceAs (Decidable (0 < s.nm (s.nr 89 + r)))

def newlyOuterOriginalInContraction (s : ArithmeticState) (i : ℕ) : Prop :=
  wasContractedRepresentative s (originalTopRepresentative s i) ∧
    2 ≤ s.nm (s.nr 51 + originalTopRepresentative s i)

instance (s : ArithmeticState) (i : ℕ) : Decidable (newlyOuterOriginalInContraction s i) :=
  inferInstanceAs (Decidable (wasContractedRepresentative s (originalTopRepresentative s i) ∧
    2 ≤ s.nm (s.nr 51 + originalTopRepresentative s i)))



/-- Map one original compact vertex to the common outer base when its old block is
absorbed. If it became outer in this contraction, append it to the fresh-vertex list. -/
def contractMatchingRepresentativeCell : List ArithmeticInstruction :=
  [.natAdd 6 57 7, .natLoad 10 6, .natAdd 11 89 10, .natLoad 11 11,
   .natBranch 11 23 13 5, .natStore 6 12, .natAdd 6 51 10, .natLoad 11 6,
   .natConst 10 2, .natBranch 10 11 10 13,
   .natAdd 6 88 99, .natStore 6 7, .natAdd 99 99 9]



def contractMatchingRepresentativeBlock : List ArithmeticInstruction :=
  appendBlock [.natConst 23 0, .natConst 99 0]
    (countedLoopFromZero 9 7 55 contractMatchingRepresentativeCell)











end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractRepresentativesRAM

/-! matching/MatchingContractCode.lean -/
section RppSource_MatchingContractCode
namespace VehicleRoutingSurvey.Routing

def readParentCycleWitness (child : ℕ) (reverse : Bool) : List ArithmeticInstruction :=
  [.natAdd 6 child child, .natAdd 6 90 6, .natLoad (if reverse then 17 else 16) 6,
    .natAdd 6 6 9, .natLoad (if reverse then 16 else 17) 6]

def copyClosingCycleWitness : List ArithmeticInstruction :=
  [.natAdd 16 93 23, .natAdd 17 92 23]

def readLeftCycleRepresentative : List ArithmeticInstruction :=
  [.natAdd 6 83 7, .natLoad 15 6]

def leftMatchingCycleChild : List ArithmeticInstruction :=
  appendBlock readLeftCycleRepresentative (appendBlock (readParentCycleWitness 15 true) appendMatchingCycleChild)

def readCycleSuccessor (index : ℕ) : List ArithmeticInstruction :=
  [.natSub 6 index 9, .natAdd 6 84 6, .natLoad 18 6]

def chooseCycleSuccessor (index : ℕ) : List ArithmeticInstruction :=
  branchOnAtMost index 23 copyClosingCycleWitness
    (appendBlock (readCycleSuccessor index) (readParentCycleWitness 18 false))

def commonMatchingCycleChild : List ArithmeticInstruction :=
  appendBlock [.natAdd 15 12 23]
    (appendBlock (chooseCycleSuccessor 14) appendMatchingCycleChild)

def readRightCycleRepresentative : List ArithmeticInstruction :=
  [.natAdd 18 7 9, .natSub 18 14 18, .natAdd 6 84 18, .natLoad 15 6]

def rightMatchingCycleChild : List ArithmeticInstruction :=
  appendBlock readRightCycleRepresentative
    (appendBlock (chooseCycleSuccessor 18) appendMatchingCycleChild)

/-- Save the contracted odd cycle in left-to-base-to-right order. Every record keeps
the old child node identifier and the original edge to the next child. -/
def writeMatchingContractionCycle : List ArithmeticInstruction :=
  appendBlock [.natConst 23 0] (appendBlock startMatchingCycleRecord
    (appendBlock (countedLoopFromZero 9 7 13 leftMatchingCycleChild)
      (appendBlock commonMatchingCycleChild (countedLoopFromZero 9 7 14 rightMatchingCycleChild))))

def clearCycleMark : List ArithmeticInstruction :=
  [.natAdd 6 89 7, .natStore 6 23]

def markCycleTraceRepresentative : List ArithmeticInstruction :=
  [.natAdd 6 18 7, .natLoad 10 6, .natAdd 6 89 10, .natStore 6 9]

/-- Initialize a mask for the current contraction cycle from its common base and both
exclusive trace prefixes. The role and representative tables are untouched. -/
def markMatchingContractionCycle : List ArithmeticInstruction :=
  appendBlock [.natConst 23 0] (appendBlock (countedLoopFromZero 9 7 55 clearCycleMark)
    (appendBlock [.natAdd 6 89 12, .natStore 6 9, .natAdd 18 83 23, .natAdd 19 13 23]
      (appendBlock (countedLoopFromZero 9 7 19 markCycleTraceRepresentative)
        (appendBlock [.natAdd 18 84 23, .natAdd 19 14 23]
          (countedLoopFromZero 9 7 19 markCycleTraceRepresentative)))))

/-- Absorbed representatives become inactive in the forest and active node-ID table.
Their historical child records remain available in the cycle registry. -/
def hideContractedForestRepresentative : List ArithmeticInstruction :=
  [.natAdd 6 51 7, .natStore 6 23, .natAdd 6 52 7, .natStore 6 55,
    .natAdd 6 74 7, .natStore 6 23]

/-- Redirect a surviving inner node whose parent was absorbed. Its stored witness
continues to connect the surviving node to the merged parent. -/
def redirectContractedForestParent : List ArithmeticInstruction :=
  [.natAdd 6 51 7, .natLoad 10 6, .natConst 11 2, .natBranch 11 10 4 10,
   .natAdd 6 52 7, .natLoad 10 6, .natAdd 11 89 10, .natLoad 10 11,
   .natBranch 10 23 10 9, .natStore 6 12]

def readContractionMask : List ArithmeticInstruction :=
  [.natAdd 6 89 7, .natLoad 10 6]

def contractMatchingForestCell : List ArithmeticInstruction :=
  appendBlock readContractionMask (branchOnAtMost 10 23 redirectContractedForestParent
    (branchOnAtMost 7 12 (branchOnAtMost 12 7 redirectContractedForestParent hideContractedForestRepresentative)
      hideContractedForestRepresentative))

def contractMatchingForestBlock : List ArithmeticInstruction :=
  countedLoopFromZero 9 7 55 contractMatchingForestCell

/-- Once all child identifiers are saved and absorbed rows are hidden, publish the
new top-level node at the common existing representative. -/
def installNewTopMatchingBlossom : List ArithmeticInstruction :=
  [.natAdd 6 74 12, .natStore 6 76, .natAdd 76 76 9]

def stabilizeMatchingContractionData : List ArithmeticInstruction :=
  [.natConst 23 0, .natAdd 81 12 23, .natAdd 82 14 23]

def restoreMatchingContractionData : List ArithmeticInstruction :=
  [.natAdd 12 81 14, .natAdd 14 82 14]

def clearContractedCandidateRows : List ArithmeticInstruction :=
  [.natAdd 6 89 7, .natLoad 10 6, .natBranch 10 23 9 3,
   .natAdd 6 58 7, .natStore 6 23, .natAdd 6 55 55,
   .natAdd 6 6 7, .natAdd 6 58 6, .natStore 6 23]

def clearPromotedIncomingCandidate : List ArithmeticInstruction :=
  [.natAdd 6 88 7, .natLoad 10 6, .natAdd 6 55 10, .natAdd 6 58 6, .natStore 6 23]

def writeMergedBucketForOuter : List ArithmeticInstruction :=
  appendBlock [.natAdd 17 24 23] (appendBlock minimumContractedBucket publishMinimumContractedBucket)

def readSurvivingForestRole : List ArithmeticInstruction :=
  [.natAdd 6 51 24, .natLoad 10 6]

def repairMergedBucketForColumn : List ArithmeticInstruction :=
  appendBlock readSurvivingForestRole
    (branchOnAtMost 10 9
      (branchOnAtMost 9 10 (branchOnUnequal 24 26 writeMergedBucketForOuter) []) [])

def scanFreshContractedOriginal : List ArithmeticInstruction :=
  appendBlock [.natAdd 6 88 24, .natLoad 15 6] refreshSelectedOuterVertex

/-- Rebuild the merged pair row from the absorbed outer rows, then add original edges
of vertices newly entering the outer forest. The nested scans are paid for by the
absorbed-row and newly-outer charges. -/
def repairMatchingContractionCache : List ArithmeticInstruction :=
  appendBlock [.natConst 23 0, .natConst 14 0, .natAdd 26 12 23]
    (appendBlock (countedLoopFromZero 9 7 55 clearContractedCandidateRows)
      (appendBlock (countedLoopFromZero 9 7 99 clearPromotedIncomingCandidate)
        (appendBlock (countedLoopFromZero 9 24 55 repairMergedBucketForColumn)
          (countedLoopFromZero 9 24 99 scanFreshContractedOriginal))))

def finishMatchingContractionStructure : List ArithmeticInstruction :=
  appendBlock writeMatchingContractionCycle (appendBlock markMatchingContractionCycle (appendBlock collectAbsorbedOuterRows
    (appendBlock contractMatchingRepresentativeBlock (appendBlock contractMatchingForestBlock installNewTopMatchingBlossom))))

def matchingContractionStructure : List ArithmeticInstruction :=
  appendBlock stabilizeMatchingContractionData (appendBlock advanceMatchingEventDuals
    (appendBlock restoreMatchingContractionData finishMatchingContractionStructure))

/-- Contract the tight cycle chosen by the trace. Persist the cycle before hiding
its children, update the partition and forest, and rebuild the affected cache rows. -/
def matchingContractionHandlerBlock : List ArithmeticInstruction :=
  appendBlock matchingContractionStructure (appendBlock repairMatchingContractionCache resetMatchingSelector)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractCode

/-! matching/WeightedStageDriver.lean -/
section RppSource_WeightedStageDriver
namespace VehicleRoutingSurvey.Routing

/-- The stage reserves registers 30–34 for its counter, limit, zero, active flag, and one. -/
def matchingStageSnapshot (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr 30 0}

















end VehicleRoutingSurvey.Routing
end RppSource_WeightedStageDriver

/-! matching/MatchingPreparedStage.lean -/
section RppSource_MatchingPreparedStage
namespace VehicleRoutingSurvey.Routing

/-- The whole active-loop payload. The stage index is the number of original
matching edges already installed. The program decodes its cut events from
the current top-level partition. -/
structure MatchingPreparedStage {k : ℕ} (cost : Fin k → Fin k → ℝ) (original : ArithmeticState)
    (i : ℕ) (s : ArithmeticState) where
  state : CompactMatchingPrimalDual k cost
  part : CompactMatchingPartition state
  forest : AlternatingForestState (Fin k)
  positive : 0 < k
  count : state.edges.card = i
  active : MatchingActiveStage part forest positive (matchingTopCutAt part) original i s
  cycles : MatchingLiveCycles active.registry
  storage : MatchingStageStorage k original s
  order : MatchingCycleRecordOrder s




end VehicleRoutingSurvey.Routing
end RppSource_MatchingPreparedStage

/-! matching/MatchingTraceDispatch.lean -/
section RppSource_MatchingTraceDispatch
namespace VehicleRoutingSurvey.Routing

private def putTracedOuterEndpoints : List ArithmeticInstruction :=
  [.natConst 14 0, .natAdd 1 2 14]

/-- Preserve the saved ID and the trace outputs. Distinct trees have the sentinel
ancestor and choose augmentation. -/
def resolveMatchingOuterTag : List ArithmeticInstruction :=
  [.natConst 36 0, .natAdd 1 91 36, .natBranch 55 12 5 3,
   .natConst 35 1, .jump 6, .natConst 35 3]





def resolveMatchingOuterEvent : List ArithmeticInstruction :=
  appendBlock putTracedOuterEndpoints (appendBlock traceMatchingForestBlock resolveMatchingOuterTag)









 def initMatchingDispatchTags : List ArithmeticInstruction :=
  [.natConst 36 0, .natConst 37 1, .natConst 38 2]





/-- Resolve the selected cache event to one of the four action tags. Only an event
between two outer representatives uses the trace scratch. -/
def classifyAndTraceMatchingEvent : List ArithmeticInstruction :=
  appendBlock classifyMatchingSelectedEvent
    (appendBlock initMatchingDispatchTags
      (branchOnAtMost 35 37 (branchOnAtMost 35 36 [] resolveMatchingOuterEvent) []))









end VehicleRoutingSurvey.Routing
end RppSource_MatchingTraceDispatch

/-! matching/MatchingDispatchState.lean -/
section RppSource_MatchingDispatchState
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- All input to the real event dispatcher, including the physical
allocation bound and the cycle data for nested augmentation or expansion. -/
structure MatchingDispatchState {k : ℕ} (cost : Fin k → Fin k → ℝ)
    (original : ArithmeticState) (i : ℕ) (s : ArithmeticState) where
  state : CompactMatchingPrimalDual k cost
  part : CompactMatchingPartition state
  forest : AlternatingForestState (Fin k)
  positive : 0 < k
  count : state.edges.card = i
  top : CompactTopMatching part
  internal : state.InternalCuts
  search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween
  selected : MatchingChosenStage part forest positive (matchingTopCutAt part) original s
  cycles : MatchingLiveCycles selected.registry
  storage : MatchingStageStorage k original s
  order : MatchingCycleRecordOrder s
  fresh : MatchingFreshCutOuter part forest selected.dual.node (s.nr 39)
  budget : MatchingRegistryBudget k i s (matchingStageCountsFromRAM k s (s.nr 39))
  one : s.nr 9 = 1








end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchState

/-! matching/MatchingProgram.lean -/
section RppSource_MatchingProgram
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Execute the selected event and repair the appropriate candidate ranges. -/
def weightedBlossomEventHandler : List ArithmeticInstruction :=
  appendBlock classifyAndTraceMatchingEvent
    (dispatchMatchingActionBlock matchingGrowHandlerWithWitnesses matchingContractionHandlerBlock
      matchingExpandHandlerBlock matchingAugmentationHandlerBlock)














end VehicleRoutingSurvey.Routing
end RppSource_MatchingProgram

/-! matching/MatchingLoopRefinement.lean -/
section RppSource_MatchingLoopRefinement
namespace VehicleRoutingSurvey.Routing



noncomputable abbrev matchingLoopCounts (k : ℕ) (_i : ℕ) (s : ArithmeticState) : MatchingStageCounts :=
  matchingStageCountsFromRAM k s (s.nr 39)








end VehicleRoutingSurvey.Routing
end RppSource_MatchingLoopRefinement



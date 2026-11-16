-- Prove2me | Definitions.Def_EditApproxScheme_10
-- name    : EditApproxScheme_10
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:40:58.407988+00:00
-- url     : https://prove2.me/theorems/fe288e6c-93e3-4aff-aae0-ae3e135a0b2b
-- title:
--   Edit-distance approximation scheme, part 10 of 20: band actions and occurrence indexes
-- statement:
--   This is **part 10 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains counting, the band-action predicate and the computed band actions, the rational minimum over wide actions, keyed online bands, unskipped cell bands, costed insertion, the construction of symbol-occurrence indexes, warmup step queries, and ranked memo addressing. It also proves 5 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L5426-L6050 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 10 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_09

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.PositionCounts

def count : OAI.EditApproximation.PositionCounts → ℕ
  | .empty => 0
  | .node n _ _ => n

def left : OAI.EditApproximation.PositionCounts → OAI.EditApproximation.PositionCounts
  | .empty => .empty
  | .node _ l _ => l

def right : OAI.EditApproximation.PositionCounts → OAI.EditApproximation.PositionCounts
  | .empty => .empty
  | .node _ _ r => r

def storageBits : OAI.EditApproximation.PositionCounts → ℕ
  | .empty => 0
  | .node n l r => Nat.size n + 3 + l.storageBits + r.storageBits

def add (tree : OAI.EditApproximation.PositionCounts) : ℕ → ℕ → OAI.EditApproximation.PositionCounts
  | 0, _ => .node (tree.count + 1) tree.left tree.right
  | d + 1, i =>
    if i < 2 ^ d then
      .node (tree.count + 1) (tree.left.add d i) tree.right
    else .node (tree.count + 1) tree.left (tree.right.add d (i - 2 ^ d))

def addWithWork (tree : OAI.EditApproximation.PositionCounts) : ℕ → ℕ → OAI.EditApproximation.PositionCounts × ℕ
  | 0, _ => (.node (tree.count + 1) tree.left tree.right, 1)
  | d + 1, i =>
    if i < 2 ^ d then
      let result := tree.left.addWithWork d i
      (.node (tree.count + 1) result.1 tree.right, result.2 + 2)
    else
      let result := tree.right.addWithWork d (i - 2 ^ d)
      (.node (tree.count + 1) tree.left result.1, result.2 + 2)

def prefixWithWork (tree : OAI.EditApproximation.PositionCounts) : ℕ → ℕ → ℕ × ℕ
  | 0, t => (if t = 0 then 0 else tree.count, 1)
  | d + 1, t =>
    if t ≤ 2 ^ d then
      let result := tree.left.prefixWithWork d t
      (result.1, result.2 + 2)
    else
      let result := tree.right.prefixWithWork d (t - 2 ^ d)
      (tree.left.count + result.1, result.2 + 2)

end OAI.EditApproximation.PositionCounts

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BitQuery.Footprint

def bind {ι : Type u_1} {α : Type u_2} {β : Type u_3} {program : OAI.EditApproximation.BitQuery ι α} (heap : OAI.EditApproximation.BitQuery.Footprint program)
    (next : α → OAI.EditApproximation.BitQuery ι β) (allocation : ∀ value, OAI.EditApproximation.BitQuery.Footprint (next value)) :
    OAI.EditApproximation.BitQuery.Footprint (program.bind next) :=
  match heap with
  | .done result => allocation result
  | .read key continuation stored => .read key _ (fun word => (stored word).bind next allocation)
  | .charge localCells tail => .charge localCells (tail.bind next allocation)

def compute {ι : Type u_1} {β : Type u_2} (execution : β × ℕ) (allocation : ℕ) :
    OAI.EditApproximation.BitQuery.Footprint (OAI.EditApproximation.BitQuery.compute (ι := ι) execution) :=
  .charge allocation (.done execution.1)

def chargeOf {ι : Type u_1} {β : Type u_2} {steps : ℕ} {program : OAI.EditApproximation.BitQuery ι β} (allocation : ℕ)
    (tail : OAI.EditApproximation.BitQuery.Footprint program) : OAI.EditApproximation.BitQuery.Footprint (.charge steps program) :=
  .charge allocation tail

def runCells {ι : Type u_1} {κ : Type u_2}
    (ask : ι → OAI.EditApproximation.BinaryMemo OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitRecursiveMemoResult κ)
    (childCells : ι → OAI.EditApproximation.BinaryMemo OAI.EditApproximation.BinaryFraction → ℕ)
    {program : OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction} : OAI.EditApproximation.BitQuery.Footprint program → OAI.EditApproximation.BinaryMemo OAI.EditApproximation.BinaryFraction → ℕ
  | .done _, _ => 0
  | .read key _ continuation, memory =>
    let first := ask key memory
    3 + childCells key memory + (continuation first.value).runCells ask childCells first.memory
  | .charge cells next, memory => cells + next.runCells ask childCells memory

def computeOf {ι : Type u_1} {β : Type u_2} (execution : β × ℕ) (allocation : ℕ) :
    OAI.EditApproximation.BitQuery.Footprint (OAI.EditApproximation.BitQuery.compute (ι := ι) execution) :=
  OAI.EditApproximation.BitQuery.Footprint.compute execution allocation

def collect {ι : Type u_1} {κ : Type u_2} {β : Type u_3} (reader : κ → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (allocation : ∀ key, OAI.EditApproximation.BitQuery.Footprint (reader key)) :
    (inputs : List κ) → (next : List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β) →
      (∀ words, OAI.EditApproximation.BitQuery.Footprint (next words)) → OAI.EditApproximation.BitQuery.Footprint (OAI.EditApproximation.BitQuery.collect reader inputs next)
  | [], _, continuation => continuation []
  | key :: rest, next, continuation =>
    (allocation key).bind _ fun word => .charge 1
      (collect reader allocation rest (fun words => next (word :: words))
        (fun words => continuation (word :: words)))

def mapKeysWithWork {ι : Type u_1} {κ : Type u_2} {β : Type u_3} (f : ι → κ × ℕ) (allocation : ι → ℕ)
    {program : OAI.EditApproximation.BitQuery ι β} (heap : OAI.EditApproximation.BitQuery.Footprint program) : OAI.EditApproximation.BitQuery.Footprint (program.mapKeysWithWork f) :=
  match heap with
  | .done result => .done result
  | .read key next continuation =>
    OAI.EditApproximation.BitQuery.Footprint.chargeOf (allocation key)
      (.read (f key).1 _ (fun word => (continuation word).mapKeysWithWork f allocation))
  | .charge localCells next => .charge localCells (next.mapKeysWithWork f allocation)

def restrictWithWork {ι : Type u_1} (P : ι → Prop)
    (test : ι → Bool × ℕ) (htest : ∀ key, (test key).1 = true ↔ P key)
    (allocation : ι → ℕ)
    {program : OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction} (heap : OAI.EditApproximation.BitQuery.Footprint program) :
    OAI.EditApproximation.BitQuery.Footprint (program.restrictWithWork P test htest) :=
  match heap with
  | .done result => .done result
  | .charge localCells next => .charge localCells (next.restrictWithWork P test htest allocation)
  | .read key next continuation =>
    OAI.EditApproximation.BitQuery.Footprint.chargeOf (allocation key)
      (by
        split
        · exact .read _ _ (fun word => (continuation word).restrictWithWork P test htest allocation)
        · exact (continuation (OAI.EditApproximation.BinaryFraction.nat 0)).restrictWithWork P test htest allocation)

def normalize {ι : Type u_1} {program : OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction} (heap : OAI.EditApproximation.BitQuery.Footprint program)
    (base : List Bool) (hbase : 0 < OAI.EditApproximation.bitWordValue base) (remaining : ℕ) :
    OAI.EditApproximation.BitQuery.Footprint (program.normalize base hbase remaining) :=
  heap.bind _ fun word => OAI.EditApproximation.BitQuery.Footprint.computeOf (OAI.EditApproximation.BinaryFraction.finishCachedWithWork (word, 0) base hbase remaining)
    (OAI.EditApproximation.BinaryFraction.finishCachedAllocation (word, 0) 0 base hbase remaining)

end OAI.EditApproximation.BitQuery.Footprint

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def bandActionPredicate {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b : ℕ) (tau theta velocity : ℚ)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) (states : Fin M → OAI.EditApproximation.TargetInterval ny) : Prop :=
  OAI.EditApproximation.endpointActionConnection r states = 0 ∧
    (∀ i, Nat.dist (r.lo + ((OAI.EditApproximation.sourceChild parent i).lo - parent.lo)) (states i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((OAI.EditApproximation.sourceChild parent i).hi - parent.lo)) (states i).hi ≤ 6 * b) ∧
    ∀ j : Fin M, 0 < j.val →
      |bandCutShift parent states j - ((r.lo : ℚ) - parent.lo) - velocity *
        OAI.EditApproximation.rationalWidePrefixMinimum parent r actions hnonempty child j.val (OAI.EditApproximation.bandCutShift parent states j)| ≤
          tau * theta * b / M

def queryOnlineSourceGather {ι : Type u_1} {β : Type u_2} {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent H : ℕ) (hP : 0 < P) (tau a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (q : OAI.EditApproximation.TargetInterval ny)
    (reader : (ℕ × OAI.EditApproximation.TargetInterval ny) → ℕ → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (next : List (ℕ × OAI.EditApproximation.TargetInterval ny) → List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β) : OAI.EditApproximation.BitQuery ι β :=
  let query := initial q
  .charge query.2 ((OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork N P F hP a query.1 q)).bind
    fun keys => OAI.EditApproximation.BitQuery.collect (fun key =>
      (OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryOnlineRangeWithWork parent P exponent H tau child key)).bind
        (reader key)) keys (next keys))

def coarseLabelChildren {B d : ℕ} {α : Type u_1} (Q lam allowance : ℚ)
    (work : OAI.EditApproximation.CoarseSourceTree B α d → OAI.EditApproximation.CoarseThresholdDraws B d → ℚ → ℕ) :
    List (OAI.EditApproximation.CoarseSourceTree B α d × Fin B × OAI.EditApproximation.CoarseThresholdDraws B d) → ℕ
  | [] => 0
  | (child, draw, below) :: rest =>
    work child below (lam * OAI.EditApproximation.coarseChildThreshold B Q allowance draw) +
      coarseLabelChildren Q lam allowance work rest

instance bandActionPredicateDecidable {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b : ℕ) (tau theta velocity : ℚ)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) (states : Fin M → OAI.EditApproximation.TargetInterval ny) :
    Decidable (OAI.EditApproximation.bandActionPredicate parent r b tau theta velocity actions hnonempty child states) := by
  unfold OAI.EditApproximation.bandActionPredicate
  infer_instance

def computedBandActions {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) : List (Fin M → OAI.EditApproximation.TargetInterval ny) :=
  let actions := OAI.EditApproximation.wideActionList M parent r b P
  if h : actions = [] then [] else
    if |velocity| ≤ 1 - tau then
      actions.filter (fun states => decide (OAI.EditApproximation.bandActionPredicate parent r b tau theta velocity actions h child states))
    else []

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset

def rationalEndpointActionValue {ny M : ℕ} (r : OAI.EditApproximation.TargetInterval ny)
    (states : Fin M → OAI.EditApproximation.TargetInterval ny) (child : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) : ℚ :=
  OAI.EditApproximation.endpointActionConnection r states + ∑ i, child i (states i)

def rationalActualWideActions {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) (P : ℕ) :
    List (OAI.EditApproximation.RationalBellmanAction (OAI.EditApproximation.TargetInterval ny) (Fin M × OAI.EditApproximation.TargetInterval ny) M) :=
  representatives.flatMap fun br => (OAI.EditApproximation.wideActionList M parent br.2 br.1 P).map fun states =>
    ⟨br.2, OAI.EditApproximation.endpointActionConnection br.2 states, fun i => (i, states i)⟩

def groupQueriedChildLabels (M Q b : ℕ) (h : ℚ)
    (draw : Fin (OAI.EditApproximation.groupSampleCount M Q b h) → Fin M) : Finset (Fin M) :=
  if OAI.EditApproximation.groupSampleCount M Q b h = M then univ else univ.image draw

def rationalWideActionMinimum {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b P : ℕ) (hnonempty : OAI.EditApproximation.wideActionList M parent r b P ≠ [])
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) : ℚ :=
  OAI.EditApproximation.rationalMinimum (OAI.EditApproximation.rationalEndpointActionValue r ((OAI.EditApproximation.wideActionList M parent r b P).head hnonempty) child)
    ((OAI.EditApproximation.wideActionList M parent r b P).map fun states => OAI.EditApproximation.rationalEndpointActionValue r states child)

def groupCurrentInputCover {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (b exponent Q : ℕ) (cell : ℕ × ℕ) (h : ℚ)
    (draw : Fin (OAI.EditApproximation.groupSampleCount M Q b h) → Fin M) : Finset (Fin M × OAI.EditApproximation.TargetInterval target.length) :=
  (OAI.EditApproximation.groupQueriedChildLabels M Q b h draw).biUnion fun i =>
    (OAI.EditApproximation.groupRoundedStateList source target parent b exponent cell i h).toFinset.image fun r => (i, r)

def representativeBandActions {α : Type u_1} (source target : List α)
    {M : ℕ} (parent : OAI.EditApproximation.TargetInterval source.length) (r : OAI.EditApproximation.TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (child : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ) :
    List (Fin M → OAI.EditApproximation.TargetInterval target.length) :=
  if h : OAI.EditApproximation.wideActionList M parent r b P = [] then [] else
    let Z := OAI.EditApproximation.rationalWideActionMinimum parent r b P h child
    if 0 < Z then
      OAI.EditApproximation.computedBandActions parent r b P tau theta
        (OAI.EditApproximation.rationalStateGap (OAI.EditApproximation.substring source parent.lo parent.hi) target r / Z) child
    else []

structure UnskippedBand {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (b P thetaExponent : ℕ)
    (tau F : ℚ) (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ) where
  center : OAI.EditApproximation.TargetInterval target.length
  nonempty : OAI.EditApproximation.representativeBandActions source target parent center b P tau
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child ≠ []
  sum_guard : (∑ i, OAI.EditApproximation.bandChildEnvelope b (OAI.EditApproximation.representativeBandActions source target parent center b P tau
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child) initial i) ≤ 64 * F * b
  wide_guard : OAI.EditApproximation.canonicalRoundedBandAction thetaExponent b
    (OAI.EditApproximation.representativeBandActions source target parent center b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child) nonempty initial ∈ OAI.EditApproximation.wideActionList M parent center b P
  imbalance_guard : ∀ i, |rationalStateGap
    (OAI.EditApproximation.substring source (OAI.EditApproximation.sourceChild parent i).lo (OAI.EditApproximation.sourceChild parent i).hi) target
    (OAI.EditApproximation.canonicalRoundedBandAction thetaExponent b
      (OAI.EditApproximation.representativeBandActions source target parent center b P tau
        ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child) nonempty initial i)| ≤
      2 * OAI.EditApproximation.bandChildEnvelope b (OAI.EditApproximation.representativeBandActions source target parent center b P tau
        ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child) initial i

def keyedOnlineBandG {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (P exponent H b : ℕ) (tau : ℚ)
    (child : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ) (r : OAI.EditApproximation.TargetInterval target.length) : ℕ :=
  H + (OAI.EditApproximation.bandCoordinates (OAI.EditApproximation.representativeBandActions source target parent r b P tau
    ((2 : ℚ) ^ (-(exponent : ℤ))) child).toFinset).card + 2

def testUnskippedBand {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (b P thetaExponent : ℕ)
    (tau F : ℚ) (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ)
    (center : OAI.EditApproximation.TargetInterval target.length) :
    Option (OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial) :=
  let band := OAI.EditApproximation.representativeBandActions source target parent center b P tau
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child
  if hband : band = [] then none else
    if hsum : (∑ i, OAI.EditApproximation.bandChildEnvelope b band initial i) ≤ 64 * F * b then
      let rounded := OAI.EditApproximation.canonicalRoundedBandAction thetaExponent b band hband initial
      if hwide : rounded ∈ OAI.EditApproximation.wideActionList M parent center b P then
        if hgap : ∀ i, |rationalStateGap
            (OAI.EditApproximation.substring source (OAI.EditApproximation.sourceChild parent i).lo (OAI.EditApproximation.sourceChild parent i).hi) target (rounded i)| ≤
              2 * OAI.EditApproximation.bandChildEnvelope b band initial i then
          some ⟨center, hband, hsum, hwide, hgap⟩
        else none
      else none
    else none

def unskippedBandList {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (b P thetaExponent : ℕ)
    (tau F : ℚ) (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ)
    (centers : List (OAI.EditApproximation.TargetInterval target.length)) :
    List (OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial) :=
  centers.filterMap (OAI.EditApproximation.testUnskippedBand source target parent b P thetaExponent tau F child initial)

theorem _root_.OAI.EditApproximation.Lemmas.optimizerTriangularMass_succ (K : ℕ) :
    OAI.EditApproximation.optimizerTriangularMass (K + 1) = OAI.EditApproximation.optimizerTriangularMass K + (K + 1) := by
  unfold OAI.EditApproximation.optimizerTriangularMass
  rw [sum_range_succ]

theorem _root_.OAI.EditApproximation.Lemmas.optimizerTriangularMass_twice (K : ℕ) :
    2 * OAI.EditApproximation.optimizerTriangularMass K = K * (K + 1) := by
  induction K with
  | zero => simp [OAI.EditApproximation.optimizerTriangularMass]
  | succ K ih =>
    rw [OAI.EditApproximation.Lemmas.optimizerTriangularMass_succ]
    nlinarith

theorem _root_.OAI.EditApproximation.Lemmas.optimizerTriangularMass_positive (K : ℕ) (hK : LT.lt.{0} 0 K) :
    0 < OAI.EditApproximation.optimizerTriangularMass K := by
  have hproduct : 0 < K * (K + 1) := Nat.mul_pos hK (by omega)
  rw [← OAI.EditApproximation.Lemmas.optimizerTriangularMass_twice K] at hproduct
  omega

theorem _root_.OAI.EditApproximation.Lemmas.keyedOnlineBandG_positive {α : Type u_1} (source : List.{u_1} α) (target : List.{u_1} α) {M : ℕ} (parent : OAI.EditApproximation.TargetInterval (List.length.{u_1} source)) (P : ℕ) (exponent : ℕ) (H : ℕ) (b : ℕ) (tau : ℚ) (child : Fin M → OAI.EditApproximation.TargetInterval (List.length.{u_1} target) → ℚ) (r : OAI.EditApproximation.TargetInterval (List.length.{u_1} target)) :
    0 < OAI.EditApproximation.keyedOnlineBandG source target parent P exponent H b tau child r := by
  unfold OAI.EditApproximation.keyedOnlineBandG
  omega

def keyedOnlineCandidate {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (P F exponent H b : ℕ) (tau eta kappa : ℚ)
    (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ)
    (children : OAI.EditApproximation.PhysicalChildTables M target.length) (t : ℕ)
    (r : OAI.EditApproximation.TargetInterval target.length) (integer : ℕ) :
    Option (OAI.EditApproximation.PhysicalRationalAction M target.length) := by
  exact
    let band := OAI.EditApproximation.representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child
    let envelope := OAI.EditApproximation.bandChildEnvelope b band initial
    let G := OAI.EditApproximation.keyedOnlineBandG source target parent P exponent H b tau child r
    let K := G ^ 80
    let accepted := OAI.EditApproximation.boundedOnlineInteger (OAI.EditApproximation.optimizerTriangularMass K)
      (OAI.EditApproximation.Lemmas.optimizerTriangularMass_positive _
        (pow_pos (OAI.EditApproximation.Lemmas.keyedOnlineBandG_positive source target parent P exponent H b tau child r) 80)) integer
    if hband : band = [] then none else
      match OAI.EditApproximation.testUnskippedBand source target parent b P exponent tau F child initial r with
      | none => none
      | some _ => some (OAI.EditApproximation.sharedBandRationalAction r
          (OAI.EditApproximation.finiteOptimizerActionDraw band hband envelope
            (OAI.EditApproximation.rationalOnlineLinear eta kappa
              (OAI.EditApproximation.childGain envelope (fun s coordinate => children coordinate.1 s coordinate.2))
              (OAI.EditApproximation.childDecrement envelope (fun s coordinate => children coordinate.1 s coordinate.2)) t)
            G K accepted))

def cellUnskippedBands {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (b P F thetaExponent : ℕ) (tau a : ℚ)
    (parentInitial : OAI.EditApproximation.TargetInterval target.length → ℚ)
    (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ) (cell : ℕ × ℕ) :=
  OAI.EditApproximation.unskippedBandList source target parent b P thetaExponent tau F child initial
    (OAI.EditApproximation.cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) cell)

def localOnlineCandidates {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : OAI.EditApproximation.TargetInterval target.length → ℚ)
    (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ)
    (children : OAI.EditApproximation.PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → OAI.EditApproximation.TargetInterval target.length → ℕ)
    (q : OAI.EditApproximation.TargetInterval target.length) : List (OAI.EditApproximation.PhysicalRationalAction M target.length) :=
  (OAI.EditApproximation.dyadicQueryWindow N (parentInitial q) a F).filterMap fun b =>
    let r := OAI.EditApproximation.roundInterval (OAI.EditApproximation.seedGridSpacing b P) q
    if (b : ℚ) / (4 * a) ≤ parentInitial r ∧ parentInitial r ≤ 8 * F * b then
      OAI.EditApproximation.keyedOnlineCandidate source target parent P F exponent H b tau eta kappa
        child initial children t r (integer b r)
    else none

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryMemo

variable {α : Type u_1}

def value : OAI.EditApproximation.BinaryMemo α → Option α
  | .empty => none
  | .node v _ _ => v

def left : OAI.EditApproximation.BinaryMemo α → OAI.EditApproximation.BinaryMemo α
  | .empty => .empty
  | .node _ l _ => l

def right : OAI.EditApproximation.BinaryMemo α → OAI.EditApproximation.BinaryMemo α
  | .empty => .empty
  | .node _ _ r => r

def lookup (tree : OAI.EditApproximation.BinaryMemo α) : List Bool → Option α
  | [] => tree.value
  | false :: rest => tree.left.lookup rest
  | true :: rest => tree.right.lookup rest

def insert (tree : OAI.EditApproximation.BinaryMemo α) : List Bool → α → OAI.EditApproximation.BinaryMemo α
  | [], a => .node (some a) tree.left tree.right
  | false :: rest, a => .node tree.value (tree.left.insert rest a) tree.right
  | true :: rest, a => .node tree.value tree.left (tree.right.insert rest a)

def lookupCosted (tree : OAI.EditApproximation.BinaryMemo α) : List Bool → Option α × ℕ
  | [] => (tree.value, 1)
  | false :: rest =>
    let result := tree.left.lookupCosted rest
    (result.1, result.2 + 1)
  | true :: rest =>
    let result := tree.right.lookupCosted rest
    (result.1, result.2 + 1)

def insertCosted (tree : OAI.EditApproximation.BinaryMemo α) : List Bool → α → OAI.EditApproximation.BinaryMemo α × ℕ
  | [], a => (.node (some a) tree.left tree.right, 1)
  | false :: rest, a =>
    let result := tree.left.insertCosted rest a
    (.node tree.value result.1 tree.right, result.2 + 1)
  | true :: rest, a =>
    let result := tree.right.insertCosted rest a
    (.node tree.value tree.left result.1, result.2 + 1)

end OAI.EditApproximation.BinaryMemo

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def rankedMemoEvaluate {κ : Type u_1} (rank : κ → ℕ)
    (program : (key : κ) → OAI.EditApproximation.FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (key : κ) (memory : OAI.EditApproximation.BinaryMemo ℚ) : OAI.EditApproximation.RecursiveMemoResult κ :=
  let found := memory.lookupCosted (OAI.EditApproximation.binaryMemoKey bits (encode key))
  match found.1 with
  | some result => ⟨result, memory, [], found.2, 1⟩
  | none =>
    let result := OAI.EditApproximation.FiniteQuery.run (fun child previous =>
      rankedMemoEvaluate rank program bits encode child.val previous) (program key) memory
    let stored := result.memory.insertCosted (OAI.EditApproximation.binaryMemoKey bits (encode key)) result.value
    ⟨result.value, stored.1, key :: result.freshKeys,
      found.2 + result.dictionaryVisits + stored.2, result.requests + 1⟩
termination_by rank key
decreasing_by exact child.property

def localWarmupStepQuery {ι : Type u_1} {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F : ℕ) (a : ℚ) (initialRead : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.FiniteQuery ι)
    (childRead : Fin M × OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.FiniteQuery ι) (q : OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.FiniteQuery ι :=
  OAI.EditApproximation.FiniteQuery.bind (initialRead q) fun value =>
    let centers := OAI.EditApproximation.rawRefinementCenters N P F a value q
    OAI.EditApproximation.FiniteQuery.collect initialRead centers fun answers =>
      let initial := fun r => if r = q then value else OAI.EditApproximation.finiteAnswerTable centers answers r
      let representatives := OAI.EditApproximation.localRefinementRepresentatives N P F a initial q
      let inputs := OAI.EditApproximation.wideWarmupInputs (M := M) parent P representatives
      OAI.EditApproximation.FiniteQuery.collect childRead inputs fun values =>
        .done (OAI.EditApproximation.rationalBellman initial (fun q r => OAI.EditApproximation.targetEndpointDistance q r) (128 * F)
          (OAI.EditApproximation.rationalActualWideActions parent representatives P) (OAI.EditApproximation.finiteAnswerTable inputs values) q)

def keyedOnlineSourceRange {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (P exponent H : ℕ) (tau : ℚ)
    (child : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ) (key : ℕ × OAI.EditApproximation.TargetInterval target.length) : ℕ :=
  OAI.EditApproximation.optimizerTriangularMass (OAI.EditApproximation.keyedOnlineBandG source target parent P exponent H key.1 tau child key.2 ^ 80)

def occurrenceBuild (symbolBits positionBits : ℕ) : List (ℕ × ℕ) → OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts
  | [] => .empty
  | e :: es =>
    let table := occurrenceBuild symbolBits positionBits es
    let key := OAI.EditApproximation.binaryMemoKey symbolBits e.1
    let old := (table.lookup key).getD .empty
    table.insert key (old.add positionBits e.2)

def occurrenceBuildWithWork (symbolBits positionBits : ℕ) :
    List (ℕ × ℕ) → OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts × ℕ
  | [] => (.empty, 0)
  | e :: es =>
    let previous := occurrenceBuildWithWork symbolBits positionBits es
    let key := OAI.EditApproximation.binaryMemoKey symbolBits e.1
    let found := previous.1.lookupCosted key
    let inserted := (found.1.getD .empty).addWithWork positionBits e.2
    let updated := previous.1.insertCosted key inserted.1
    (updated.1, previous.2 + symbolBits + found.2 + inserted.2 + updated.2 + 2)

def occurrenceQueryWithWork (table : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts)
    (symbolBits positionBits a lo hi : ℕ) : Bool × ℕ :=
  let key := OAI.EditApproximation.binaryMemoKey symbolBits a
  let found := table.lookupCosted key
  let tree := found.1.getD .empty
  let first := tree.prefixWithWork positionBits lo
  let last := tree.prefixWithWork positionBits hi
  (decide (first.1 < last.1), symbolBits + found.2 + first.2 + last.2 + 2)

def rankedBitMemoEvaluate {κ : Type u_1} (rank : κ → ℕ)
    (program : (key : κ) → OAI.EditApproximation.BitQuery {child : κ // rank child < rank key} OAI.EditApproximation.BinaryFraction)
    (bits : ℕ) (encode : κ → ℕ) (key : κ) (memory : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.BinaryFraction) :
    OAI.EditApproximation.BitRecursiveMemoResult κ :=
  let found := memory.lookupCosted (OAI.EditApproximation.binaryMemoKey bits (encode key))
  match found.1 with
  | some result => ⟨result, memory, [], found.2, 1, 0⟩
  | none =>
    let result := OAI.EditApproximation.BitQuery.runMemo (fun child previous =>
      rankedBitMemoEvaluate rank program bits encode child.val previous) (program key) memory
    let stored := result.memory.insertCosted (OAI.EditApproximation.binaryMemoKey bits (encode key)) result.value
    ⟨result.value, stored.1, key :: result.freshKeys,
      found.2 + result.dictionaryVisits + stored.2, result.requests + 1, result.localWork⟩
termination_by rank key
decreasing_by exact child.property

def physicalWarmupStepQuery {ι : Type u_1} {α : Type u_2} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : OAI.EditApproximation.PhysicalEntry M J target.length → OAI.EditApproximation.FiniteQuery ι)
    (childRead : Fin M × OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.FiniteQuery ι)
    (node : OAI.EditApproximation.PhysicalNode M J) (q : OAI.EditApproximation.TargetInterval target.length) : OAI.EditApproximation.FiniteQuery ι :=
  OAI.EditApproximation.localWarmupStepQuery (OAI.EditApproximation.physicalSourceInterval source.length node) N P F (OAI.EditApproximation.refinementFactor A F)
    (fun r => OAI.EditApproximation.physicalInitialQuery source target N P F A seedRead (node, r)) childRead q

def indexedSingletonCostWithWork (table : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts)
    (symbolBits positionBits a lo hi : ℕ) : ℕ × ℕ :=
  if lo = hi then (1, 1) else
    let query := OAI.EditApproximation.occurrenceQueryWithWork table symbolBits positionBits a lo hi
    (hi - lo - if query.1 = true then 1 else 0, query.2 + 4)

def integerOccurrenceIndex (source target : List ℤ) : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts :=
  OAI.EditApproximation.occurrenceBuild (OAI.EditApproximation.integerInputSymbolBits source target) (OAI.EditApproximation.integerInputPositionBits target)
    (target.map OAI.EditApproximation.integerSymbolCode).zipIdx

def integerOccurrenceBuildWithWork (source target : List ℤ) : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts × ℕ :=
  OAI.EditApproximation.occurrenceBuildWithWork (OAI.EditApproximation.integerInputSymbolBits source target) (OAI.EditApproximation.integerInputPositionBits target)
    (target.map OAI.EditApproximation.integerSymbolCode).zipIdx

def rankedMemoAddressWork {κ : Type u_1} (rank : κ → ℕ)
    (program : (key : κ) → OAI.EditApproximation.FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode cost : κ → ℕ) (key : κ) (memory : OAI.EditApproximation.BinaryMemo ℚ) : ℕ :=
  match (memory.lookupCosted (OAI.EditApproximation.binaryMemoKey bits (encode key))).1 with
  | some _ => cost key
  | none => cost key + OAI.EditApproximation.FiniteQuery.requestWork
      (fun child previous => OAI.EditApproximation.rankedMemoEvaluate rank program bits encode child.val previous)
      (fun child previous => rankedMemoAddressWork rank program bits encode cost child.val previous)
      (program key) memory + cost key
termination_by rank key
decreasing_by exact child.property

def rankedMemoKernelWork {κ : Type u_1} (rank : κ → ℕ)
    (program : (key : κ) → OAI.EditApproximation.FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode cost : κ → ℕ) (key : κ) (memory : OAI.EditApproximation.BinaryMemo ℚ) : ℕ :=
  match (memory.lookupCosted (OAI.EditApproximation.binaryMemoKey bits (encode key))).1 with
  | some _ => 0
  | none => cost key + OAI.EditApproximation.FiniteQuery.requestWork
      (fun child previous => OAI.EditApproximation.rankedMemoEvaluate rank program bits encode child.val previous)
      (fun child previous => rankedMemoKernelWork rank program bits encode cost child.val previous)
      (program key) memory
termination_by rank key
decreasing_by exact child.property

def physicalWarmupRequestQuery {α : Type u_1} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (pass copy T S j : ℕ) (node : OAI.EditApproximation.PhysicalNode M J) (q : OAI.EditApproximation.TargetInterval target.length)
    (seedRead : OAI.EditApproximation.PhysicalEntry M J target.length →
      OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J target.length //
        child.combinedRank T S < (OAI.EditApproximation.PhysicalTableRequest.warmup pass copy node j q).combinedRank T S}) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J target.length //
      child.combinedRank T S < (OAI.EditApproximation.PhysicalTableRequest.warmup pass copy node j q).combinedRank T S} :=
  match j with
  | 0 => OAI.EditApproximation.physicalInitialQuery source target N P F A seedRead (node, q)
  | t + 1 =>
    if hbelow : node.1.val < J then
      if (OAI.EditApproximation.physicalSourceInterval source.length node).hi -
          (OAI.EditApproximation.physicalSourceInterval source.length node).lo ≤ 1 then
        OAI.EditApproximation.physicalInitialQuery source target N P F A seedRead (node, q)
      else OAI.EditApproximation.physicalWarmupStepQuery source target N P F A seedRead
        (OAI.EditApproximation.physicalWarmupChildQuery pass copy T S t node hbelow q) node q
    else OAI.EditApproximation.physicalInitialQuery source target N P F A seedRead (node, q)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

abbrev PhysicalLocalOnlineKey (M J N n : ℕ) :=
  OAI.EditApproximation.PhysicalInternalNode M J × Fin (OAI.EditApproximation.dyadicScales N).length × OAI.EditApproximation.TargetInterval n

abbrev ClampedPhysicalSeed (M J ny N : ℕ) := OAI.EditApproximation.PhysicalEntry M J ny → Fin (N + 1)

def finalTargetState (n : ℕ) : OAI.EditApproximation.TargetInterval n := ⟨0, n, Nat.zero_le _, le_rfl⟩

abbrev PhysicalCommonKey (M J N n exponent B : ℕ) :=
  Sum (OAI.EditApproximation.CommonRangeKey (OAI.EditApproximation.PhysicalLocalOnlineKey M J N n) B)
    (OAI.EditApproximation.PhysicalLocalGroupKey M J N n exponent)

def clampedSeedNat {M J ny N : ℕ} (seed : OAI.EditApproximation.ClampedPhysicalSeed M J ny N)
    (state : OAI.EditApproximation.PhysicalEntry M J ny) : ℕ := (seed state).val

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset

theorem _root_.OAI.EditApproximation.Lemmas.triangularMassWithWork_value (K : ℕ) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.triangularMassWithWork K).1 = OAI.EditApproximation.optimizerTriangularMass K := by
  simp only [OAI.EditApproximation.triangularMassWithWork, OAI.EditApproximation.Lemmas.binaryNaturalAddWithWork_value, OAI.EditApproximation.Lemmas.binaryNaturalMulWithWork_value,
    (OAI.EditApproximation.Lemmas.binaryNaturalDivModWithWork_spec _ 2 (by decide)).1]
  rw [← OAI.EditApproximation.Lemmas.optimizerTriangularMass_twice K, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

def triangularChoiceWithWork (K : ℕ) : Fin (OAI.EditApproximation.optimizerTriangularMass K) → Fin K × ℕ:= by
  exact fun integer => match K, integer with
    | 0, integer => Fin.elim0 integer
    | K + 1, integer =>
      let threshold := OAI.EditApproximation.triangularMassWithWork K
      let test := OAI.EditApproximation.binaryNaturalCompareWithWork integer.val (OAI.EditApproximation.bitWordValue threshold.1)
      if h : test.1 = .lt then
        let hsmall : integer.val < OAI.EditApproximation.optimizerTriangularMass K := by
          have ht := (OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt _ _).mp h
          simpa only [threshold, OAI.EditApproximation.Lemmas.triangularMassWithWork_value] using ht
        let chosen := triangularChoiceWithWork K ⟨integer.val, hsmall⟩
        (chosen.1.castSucc, threshold.2 + test.2 + chosen.2 + 2)
      else (⟨K, by omega⟩, threshold.2 + test.2 + 1)

def triangularChoiceAllocation (K : ℕ) : Fin (OAI.EditApproximation.optimizerTriangularMass K) → ℕ:= by
  exact fun integer => match K, integer with
    | 0, integer => Fin.elim0 integer
    | K + 1, integer =>
      let threshold := OAI.EditApproximation.triangularMassWithWork K
      let test := OAI.EditApproximation.binaryNaturalCompareWithWork integer.val (OAI.EditApproximation.bitWordValue threshold.1)
      let localCells := OAI.EditApproximation.triangularMassAllocation K + integer.val.bits.length +
        (OAI.EditApproximation.bitWordValue threshold.1).bits.length
      if h : test.1 = .lt then
        let hsmall : integer.val < OAI.EditApproximation.optimizerTriangularMass K := by
          have ht := (OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt _ _).mp h
          simpa only [threshold, OAI.EditApproximation.Lemmas.triangularMassWithWork_value] using ht
        localCells + triangularChoiceAllocation K ⟨integer.val, hsmall⟩
      else localCells

end OAI.EditApproximation

end



-- Prove2me | Definitions.Def_EditApproxScheme_06
-- name    : EditApproxScheme_06
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:35:04.762199+00:00
-- url     : https://prove2.me/theorems/06cb6e89-55b4-49d7-a025-8d2354f7340c
-- title:
--   Edit-distance approximation scheme, part 6 of 20: interval states and initial cones
-- statement:
--   This is **part 6 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains source children, grid state boxes and gap states, comparisons of slices and intervals, rounded states, initial cone values and cone centers, ordered child inputs, physical entry codes, and online keys. It also proves 13 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L2818-L3313 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 6 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_05

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

theorem _root_.OAI.EditApproximation.Lemmas.balancedCut_monotone (lo : ℕ) (width : ℕ) (M : ℕ) : Monotone (OAI.EditApproximation.balancedCut lo width M) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_right width hij)) lo

theorem _root_.OAI.EditApproximation.Lemmas.balancedCut_last (lo : ℕ) (width : ℕ) (M : ℕ) (hM : LT.lt.{0} 0 M) :
    OAI.EditApproximation.balancedCut lo width M M = lo + width := by
  simp only [OAI.EditApproximation.balancedCut, Nat.mul_div_cancel_left _ hM]

theorem _root_.OAI.EditApproximation.Lemmas.balancedCut_bounds (lo : ℕ) (width : ℕ) (M : ℕ) (i : ℕ) (hM : LT.lt.{0} 0 M) (hi : LE.le.{0} i M) :
    lo ≤ OAI.EditApproximation.balancedCut lo width M i ∧ OAI.EditApproximation.balancedCut lo width M i ≤ lo + width := by
  constructor
  · exact Nat.le_add_right _ _
  · rw [← OAI.EditApproximation.Lemmas.balancedCut_last lo width M hM]
    exact OAI.EditApproximation.Lemmas.balancedCut_monotone lo width M hi

def sourceChild {n M : ℕ} (parent : OAI.EditApproximation.TargetInterval n) (child : Fin M) : OAI.EditApproximation.TargetInterval n := by
  exact
    { lo := OAI.EditApproximation.balancedCut parent.lo (parent.hi - parent.lo) M child.val
      hi := OAI.EditApproximation.balancedCut parent.lo (parent.hi - parent.lo) M (child.val + 1)
      ordered := OAI.EditApproximation.Lemmas.balancedCut_monotone _ _ _ (Nat.le_succ _)
      valid := by
        have hM : 0 < M := Nat.zero_lt_of_lt child.isLt
        have hbound := (OAI.EditApproximation.Lemmas.balancedCut_bounds parent.lo (parent.hi - parent.lo) M (child.val + 1)
          hM (by omega)).2
        rw [Nat.add_sub_of_le parent.ordered] at hbound
        exact hbound.trans parent.valid }

theorem _root_.OAI.EditApproximation.Lemmas.gridRound_mono (spacing : ℕ) : Monotone (OAI.EditApproximation.gridRound spacing) := by
  intro p q hpq
  exact Nat.mul_le_mul_left spacing (Nat.div_le_div_right hpq)

theorem _root_.OAI.EditApproximation.Lemmas.gridRound_le (spacing : ℕ) (position : ℕ) : OAI.EditApproximation.gridRound spacing position ≤ position :=
  Nat.mul_div_le _ _

def roundInterval {n : ℕ} (spacing : ℕ) (state : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.TargetInterval n := by
  exact {
    lo := OAI.EditApproximation.gridRound spacing state.lo
    hi := OAI.EditApproximation.gridRound spacing state.hi
    ordered := OAI.EditApproximation.Lemmas.gridRound_mono spacing state.ordered
    valid := (OAI.EditApproximation.Lemmas.gridRound_le spacing state.hi).trans state.valid
  }

def localTargetStates (n g radius : ℕ) (q : OAI.EditApproximation.TargetInterval n) : List (OAI.EditApproximation.TargetInterval n) :=
  (OAI.EditApproximation.gridPointsBetween g (q.lo - radius) (q.lo + radius)).flatMap fun lo =>
    (OAI.EditApproximation.gridPointsBetween g (q.hi - radius) (q.hi + radius)).filterMap fun hi =>
      OAI.EditApproximation.makeTargetState n lo hi

def rationalStateGap {α : Type u_1} (source target : List α) (q : OAI.EditApproximation.TargetInterval target.length) : ℚ :=
  (q.hi : ℚ) - q.lo - source.length

def gridStateBox (n g radius lo hi : ℕ) : List (OAI.EditApproximation.TargetInterval n) :=
  (OAI.EditApproximation.gridPointsBetween g (lo - radius) (lo + radius)).flatMap fun s =>
    (OAI.EditApproximation.gridPointsBetween g (hi - radius) (hi + radius)).filterMap fun t =>
      OAI.EditApproximation.makeTargetState n s t

abbrev PhysicalEntry (M J ny : ℕ) := OAI.EditApproximation.PhysicalNode M J × OAI.EditApproximation.TargetInterval ny

theorem _root_.OAI.EditApproximation.Lemmas.wordLEWithWork_value (a : List.{0} Bool) (b : List.{0} Bool) :
    (OAI.EditApproximation.wordLEWithWork a b).1 = true ↔ OAI.EditApproximation.bitWordValue a ≤ OAI.EditApproximation.bitWordValue b := by
  simp only [OAI.EditApproximation.wordLEWithWork, Bool.not_eq_true', decide_eq_false_iff_not,
    OAI.EditApproximation.Lemmas.bitCompareWithWork_lt, not_lt]

def makeStateWithWork (n lo hi : ℕ) : Option (OAI.EditApproximation.TargetInterval n) × ℕ := by
  exact
    let first := OAI.EditApproximation.wordLEWithWork lo.bits hi.bits
    let second := OAI.EditApproximation.wordLEWithWork hi.bits n.bits
    if h : (first.1 && second.1) = true then
      (some ⟨lo, hi,
        by have hp : first.1 = true ∧ second.1 = true := by simpa only [Bool.and_eq_true] using h
           simpa only [first, OAI.EditApproximation.Lemmas.wordLEWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits] using hp.1,
        by have hp : first.1 = true ∧ second.1 = true := by simpa only [Bool.and_eq_true] using h
           simpa only [second, OAI.EditApproximation.Lemmas.wordLEWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits] using hp.2⟩,
        first.2 + second.2 + 4)
    else (none, first.2 + second.2 + 2)

def cellTargetStates (n g : ℕ) (side : ℚ) (cell : ℕ × ℕ) : List (OAI.EditApproximation.TargetInterval n) :=
  (OAI.EditApproximation.cellGridPoints side g cell.1).flatMap fun lo =>
    (OAI.EditApproximation.cellGridPoints side g cell.2).filterMap fun hi => OAI.EditApproximation.makeTargetState n lo hi

def gridGapStates (n g anchor radius sourceLength gapRadius : ℕ) : List (OAI.EditApproximation.TargetInterval n) :=
  (OAI.EditApproximation.gridPointsBetween g (anchor - radius) (anchor + radius)).flatMap fun lo =>
    (OAI.EditApproximation.gridPointsBetween g (lo + sourceLength - gapRadius) (lo + sourceLength + gapRadius)).filterMap
      fun hi => OAI.EditApproximation.makeTargetState n lo hi

abbrev PhysicalChildTables (M ny : ℕ) := Fin M → ℕ → OAI.EditApproximation.TargetInterval ny → ℚ

abbrev PhysicalRationalAction (M ny : ℕ) :=
  OAI.EditApproximation.RationalBellmanAction (OAI.EditApproximation.TargetInterval ny) (Fin M × OAI.EditApproximation.TargetInterval ny) M

def localTargetCells {n : ℕ} (side : ℚ) (radius : ℕ) (q : OAI.EditApproximation.TargetInterval n) : List (ℕ × ℕ) :=
  (OAI.EditApproximation.localCellCoordinates side q.lo radius).flatMap fun lo =>
    (OAI.EditApproximation.localCellCoordinates side q.hi radius).map fun hi => (lo, hi)

def coordinateEqualWithWork {M n : ℕ} (a b : Fin M × OAI.EditApproximation.TargetInterval n) : Bool × ℕ :=
  let child := OAI.EditApproximation.naturalEqualWithWork a.1.val b.1.val
  let lo := OAI.EditApproximation.naturalEqualWithWork a.2.lo b.2.lo
  let hi := OAI.EditApproximation.naturalEqualWithWork a.2.hi b.2.hi
  (child.1 && lo.1 && hi.1, child.2 + lo.2 + hi.2 + 2)

def queryIntervalEqualWithWork {n : ℕ} (a b : OAI.EditApproximation.TargetInterval n) : Bool × ℕ :=
  let lo := OAI.EditApproximation.naturalEqualWithWork a.lo b.lo
  let hi := OAI.EditApproximation.naturalEqualWithWork a.hi b.hi
  (lo.1 && hi.1, lo.2 + hi.2 + 1)

def childInputCode {M n : ℕ} (input : Fin M × OAI.EditApproximation.TargetInterval n) : ℕ :=
  input.1.val + M * (input.2.lo + (n + 1) * input.2.hi)

def queryChildCodeWithWork {M n : ℕ} (input : Fin M × OAI.EditApproximation.TargetInterval n) : ℕ × ℕ :=
  let width := OAI.EditApproximation.binaryNaturalAddWithWork n 1
  let high := OAI.EditApproximation.binaryNaturalMulWithWork (OAI.EditApproximation.bitWordValue width.1) input.2.hi
  let coordinate := OAI.EditApproximation.binaryNaturalAddWithWork input.2.lo (OAI.EditApproximation.bitWordValue high.1)
  let scaled := OAI.EditApproximation.binaryNaturalMulWithWork M (OAI.EditApproximation.bitWordValue coordinate.1)
  let result := OAI.EditApproximation.binaryNaturalAddWithWork input.1.val (OAI.EditApproximation.bitWordValue scaled.1)
  (OAI.EditApproximation.bitWordValue result.1, width.2 + high.2 + coordinate.2 + scaled.2 + result.2 + 5)

def querySliceHeadWithWork {α : Type u_1} (source : List α)
    (interval : OAI.EditApproximation.TargetInterval source.length) : Option α × ℕ :=
  let test := OAI.EditApproximation.binaryNaturalCompareWithWork interval.lo interval.hi
  (if test.1 = .lt then source[interval.lo]? else none,
    test.2 + Nat.size interval.lo + Nat.size interval.hi + 3)

def rankedBitProgramValue {κ : Type u_1} (rank : κ → ℕ)
    (program : (key : κ) → OAI.EditApproximation.BitQuery {child : κ // rank child < rank key} OAI.EditApproximation.BinaryFraction)
    (key : κ) : OAI.EditApproximation.BinaryFraction :=
  (program key).value (fun child => rankedBitProgramValue rank program child.val)
termination_by rank key
decreasing_by exact child.property

def scheduledRefinementWordWithWork (N pass : ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  if pass < OAI.EditApproximation.computedSeedPassCount N then
    let e := OAI.EditApproximation.dyadicSeedExponent (OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.computedSeedInitialExponent N) pass -
      OAI.EditApproximation.smallLogExponent N
    let value := OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork (e : ℤ)
    (value.1, value.2 + 5)
  else (OAI.EditApproximation.BinaryFraction.nat 1, 3)

def coordinateEqualAllocation {M n : ℕ} (a b : Fin M × OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.naturalEqualAllocation a.1.val b.1.val + OAI.EditApproximation.naturalEqualAllocation a.2.lo b.2.lo +
    OAI.EditApproximation.naturalEqualAllocation a.2.hi b.2.hi + 2

def queryIntervalEqualAllocation {n : ℕ} (a b : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.naturalEqualAllocation a.lo b.lo + OAI.EditApproximation.naturalEqualAllocation a.hi b.hi + 1

def sourceChildAllocation {n M : ℕ} (parent : OAI.EditApproximation.TargetInterval n) (i : Fin M) : ℕ :=
  let width := (OAI.EditApproximation.saturatingSubtractWithWork parent.hi parent.lo).1
  let next := (OAI.EditApproximation.binaryNaturalAddWithWork i.val 1).1
  OAI.EditApproximation.saturatingSubtractAllocation parent.hi parent.lo + OAI.EditApproximation.binaryNaturalAddAllocation i.val 1 +
    OAI.EditApproximation.balancedCutAllocation parent.lo (OAI.EditApproximation.bitWordValue width) M i.val +
    OAI.EditApproximation.balancedCutAllocation parent.lo (OAI.EditApproximation.bitWordValue width) M (OAI.EditApproximation.bitWordValue next) + 2

def zeroConnectionAllocation {n : ℕ} (start : ℕ) : List (OAI.EditApproximation.TargetInterval n) → ℕ → ℕ
  | [], finish => OAI.EditApproximation.naturalEqualAllocation start finish
  | state :: rest, finish => OAI.EditApproximation.naturalEqualAllocation start state.lo +
    zeroConnectionAllocation state.hi rest finish + 1

def queryChildCodeAllocation {M n : ℕ} (input : Fin M × OAI.EditApproximation.TargetInterval n) : ℕ :=
  let width := (OAI.EditApproximation.binaryNaturalAddWithWork n 1).1
  let high := (OAI.EditApproximation.binaryNaturalMulWithWork (OAI.EditApproximation.bitWordValue width) input.2.hi).1
  let coordinate := (OAI.EditApproximation.binaryNaturalAddWithWork input.2.lo (OAI.EditApproximation.bitWordValue high)).1
  let scaled := (OAI.EditApproximation.binaryNaturalMulWithWork M (OAI.EditApproximation.bitWordValue coordinate)).1
  OAI.EditApproximation.binaryNaturalAddAllocation n 1 + OAI.EditApproximation.binaryNaturalMulAllocation (OAI.EditApproximation.bitWordValue width) input.2.hi +
    OAI.EditApproximation.binaryNaturalAddAllocation input.2.lo (OAI.EditApproximation.bitWordValue high) +
    OAI.EditApproximation.binaryNaturalMulAllocation M (OAI.EditApproximation.bitWordValue coordinate) +
    OAI.EditApproximation.binaryNaturalAddAllocation input.1.val (OAI.EditApproximation.bitWordValue scaled)

def roundStateAllocation {n : ℕ} (spacing : ℕ) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.binaryGridRoundAllocation spacing q.lo + OAI.EditApproximation.binaryGridRoundAllocation spacing q.hi + 2

def actionEqualAllocation {n M : ℕ} (a b : Fin M → OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.allAllocation (fun i => OAI.EditApproximation.naturalEqualAllocation (a i).lo (b i).lo +
    OAI.EditApproximation.naturalEqualAllocation (a i).hi (b i).hi) (List.finRange M)

structure RawUnskippedBand (M ny : ℕ) where
  center : OAI.EditApproximation.TargetInterval ny
  actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)
  nonempty : actions ≠ []

def sourceIntervalAt (M n : ℕ) : (d : ℕ) → OAI.EditApproximation.TreeLayer M d → OAI.EditApproximation.TargetInterval n
  | 0, _ => ⟨0, n, Nat.zero_le _, le_rfl⟩
  | d + 1, node => OAI.EditApproximation.sourceChild (sourceIntervalAt M n d node.1) node.2

def initialConeValue {α : Type u_1} (source target : List α)
    (U : OAI.EditApproximation.TargetInterval target.length → ℕ) (a L0 : ℚ)
    (query center : OAI.EditApproximation.TargetInterval target.length) : ℚ :=
  OAI.EditApproximation.scaledSeedValue (U center) a (OAI.EditApproximation.rationalStateGap source target center) +
    L0 * OAI.EditApproximation.targetEndpointDistance query center

def wideChildStateList {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b P : ℕ) (i : Fin M) : List (OAI.EditApproximation.TargetInterval ny) :=
  OAI.EditApproximation.gridStateBox ny (OAI.EditApproximation.seedGridSpacing b P) (10 * b)
    (r.lo + ((OAI.EditApproximation.sourceChild parent i).lo - parent.lo))
    (r.lo + ((OAI.EditApproximation.sourceChild parent i).hi - parent.lo))

def bandCutShift {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (states : Fin M → OAI.EditApproximation.TargetInterval ny) (j : Fin M) : ℚ :=
  (states j).lo - ((OAI.EditApproximation.sourceChild parent j).lo : ℚ)

def localInitialConeCenters {n : ℕ} (N P : ℕ) (A : ℚ)
    (U : OAI.EditApproximation.TargetInterval n → ℕ) (q : OAI.EditApproximation.TargetInterval n) : List (OAI.EditApproximation.TargetInterval n) :=
  ((OAI.EditApproximation.dyadicScales N).filter (fun (b : ℕ) => decide
      ((U q : ℚ) / (16 * A ^ 2) ≤ (b : ℚ) ∧ (b : ℚ) ≤ 4 * A * U q))).flatMap fun b =>
    (OAI.EditApproximation.localTargetStates n (OAI.EditApproximation.seedGridSpacing b P) (U q) q).filter fun r =>
      decide ((b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b)

def gridStateBoxWithWork (n g radius lo hi : ℕ) : List (OAI.EditApproximation.TargetInterval n) × ℕ :=
  let leftLow := OAI.EditApproximation.saturatingSubtractWithWork lo radius
  let leftHigh := OAI.EditApproximation.binaryNaturalAddWithWork lo radius
  let rightLow := OAI.EditApproximation.saturatingSubtractWithWork hi radius
  let rightHigh := OAI.EditApproximation.binaryNaturalAddWithWork hi radius
  let left := OAI.EditApproximation.gridPointsWithWork g (OAI.EditApproximation.bitWordValue leftLow.1) (OAI.EditApproximation.bitWordValue leftHigh.1)
  let right := OAI.EditApproximation.gridPointsWithWork g (OAI.EditApproximation.bitWordValue rightLow.1) (OAI.EditApproximation.bitWordValue rightHigh.1)
  let states := OAI.EditApproximation.arithmeticFlatMapWithWork (fun s => OAI.EditApproximation.filterMapWithWork (OAI.EditApproximation.makeStateWithWork n s) right.1) left.1
  (states.1, leftLow.2 + leftHigh.2 + rightLow.2 + rightHigh.2 + left.2 + right.2 + states.2 + 6)

theorem _root_.OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt (a : ℕ) (b : ℕ) :
    (OAI.EditApproximation.binaryNaturalCompareWithWork a b).1 = .lt ↔ a < b := by
  simpa only [OAI.EditApproximation.binaryNaturalCompareWithWork, OAI.EditApproximation.Lemmas.bitWordValue_bits] using OAI.EditApproximation.Lemmas.bitCompareWithWork_lt a.bits b.bits

theorem _root_.OAI.EditApproximation.Lemmas.binaryNaturalSubtractWithWork_value (a : ℕ) (b : ℕ) (h : LE.le.{0} b a) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalSubtractWithWork a b).1 = a - b := by
  simpa only [OAI.EditApproximation.binaryNaturalSubtractWithWork, OAI.EditApproximation.Lemmas.bitWordValue_bits] using
    OAI.EditApproximation.Lemmas.bitSubtractWithWork_sub a.bits b.bits (by simpa only [OAI.EditApproximation.Lemmas.bitWordValue_bits] using h)

theorem _root_.OAI.EditApproximation.Lemmas.saturatingSubtractWithWork_value (a : ℕ) (b : ℕ) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.saturatingSubtractWithWork a b).1 = a - b := by
  unfold OAI.EditApproximation.saturatingSubtractWithWork
  dsimp only
  split_ifs with h
  · have hlt := (OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt a b).mp h
    simp only [OAI.EditApproximation.bitWordValue, Nat.sub_eq_zero_of_le hlt.le]
  · exact OAI.EditApproximation.Lemmas.binaryNaturalSubtractWithWork_value a b (le_of_not_gt (fun hab =>
      h ((OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt a b).mpr hab)))

theorem _root_.OAI.EditApproximation.Lemmas.binaryNaturalMulWithWork_value (a : ℕ) (b : ℕ) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalMulWithWork a b).1 = a * b := by
  simp [OAI.EditApproximation.binaryNaturalMulWithWork, OAI.EditApproximation.Lemmas.bitMulWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits]

theorem _root_.OAI.EditApproximation.Lemmas.binaryNaturalAddWithWork_value (a : ℕ) (b : ℕ) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalAddWithWork a b).1 = a + b := by
  simp [OAI.EditApproximation.binaryNaturalAddWithWork, OAI.EditApproximation.Lemmas.bitAddWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits]

theorem _root_.OAI.EditApproximation.Lemmas.balancedCutWithWork_value (lo : ℕ) (width : ℕ) (M : ℕ) (i : ℕ) (hM : LT.lt.{0} 0 M) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.balancedCutWithWork lo width M i).1 = OAI.EditApproximation.balancedCut lo width M i := by
  simp only [OAI.EditApproximation.balancedCutWithWork, OAI.EditApproximation.Lemmas.binaryNaturalAddWithWork_value,
    (OAI.EditApproximation.Lemmas.binaryNaturalDivModWithWork_spec _ M hM).1, OAI.EditApproximation.Lemmas.binaryNaturalMulWithWork_value, OAI.EditApproximation.balancedCut]

def sourceChildWithWork {n M : ℕ} (parent : OAI.EditApproximation.TargetInterval n) (i : Fin M) : OAI.EditApproximation.TargetInterval n × ℕ := by
  exact
    let width := OAI.EditApproximation.saturatingSubtractWithWork parent.hi parent.lo
    let next := OAI.EditApproximation.binaryNaturalAddWithWork i.val 1
    let left := OAI.EditApproximation.balancedCutWithWork parent.lo (OAI.EditApproximation.bitWordValue width.1) M i.val
    let right := OAI.EditApproximation.balancedCutWithWork parent.lo (OAI.EditApproximation.bitWordValue width.1) M (OAI.EditApproximation.bitWordValue next.1)
    let heql : OAI.EditApproximation.bitWordValue left.1 = (OAI.EditApproximation.sourceChild parent i).lo := by
      simp only [left, width, OAI.EditApproximation.Lemmas.balancedCutWithWork_value _ _ _ _ (Nat.zero_lt_of_lt i.isLt),
        OAI.EditApproximation.Lemmas.saturatingSubtractWithWork_value, OAI.EditApproximation.sourceChild]
    let heqh : OAI.EditApproximation.bitWordValue right.1 = (OAI.EditApproximation.sourceChild parent i).hi := by
      simp only [right, width, next, OAI.EditApproximation.Lemmas.balancedCutWithWork_value _ _ _ _ (Nat.zero_lt_of_lt i.isLt),
        OAI.EditApproximation.Lemmas.saturatingSubtractWithWork_value, OAI.EditApproximation.Lemmas.binaryNaturalAddWithWork_value, OAI.EditApproximation.sourceChild]
    (⟨OAI.EditApproximation.bitWordValue left.1, OAI.EditApproximation.bitWordValue right.1,
      by rw [heql, heqh]; exact (OAI.EditApproximation.sourceChild parent i).ordered,
      by rw [heqh]; exact (OAI.EditApproximation.sourceChild parent i).valid⟩,
      width.2 + next.2 + left.2 + right.2 + 4)

def cellRepresentativeStates (n P F b : ℕ) (a : ℚ) (initial : OAI.EditApproximation.TargetInterval n → ℚ)
    (theta : ℚ) (cell : ℕ × ℕ) : List (OAI.EditApproximation.TargetInterval n) :=
  (OAI.EditApproximation.cellTargetStates n (OAI.EditApproximation.seedGridSpacing b P) (theta * b) cell).filter fun r => decide
    ((b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b)

def groupRoundedStateList {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (b exponent : ℕ) (cell : ℕ × ℕ)
    (i : Fin M) (h : ℚ) : List (OAI.EditApproximation.TargetInterval target.length) :=
  OAI.EditApproximation.gridGapStates target.length (OAI.EditApproximation.groupRoundSpacing exponent h)
    (⌊(cell.1 : ℚ) * ((2 : ℚ) ^ (-(exponent : ℤ)) * b)⌋₊ +
      ((OAI.EditApproximation.sourceChild parent i).lo - parent.lo)) (12 * b)
    (OAI.EditApproximation.substring source (OAI.EditApproximation.sourceChild parent i).lo (OAI.EditApproximation.sourceChild parent i).hi).length ⌈2 * h⌉₊

def rawInitialConeCenters {n : ℕ} (N P : ℕ) (A : ℚ) (value : ℕ)
    (q : OAI.EditApproximation.TargetInterval n) : List (OAI.EditApproximation.TargetInterval n) :=
  ((OAI.EditApproximation.dyadicScales N).filter fun (b : ℕ) => decide
    ((value : ℚ) / (16 * A ^ 2) ≤ b ∧ (b : ℚ) ≤ 4 * A * value)).flatMap fun b =>
      OAI.EditApproximation.localTargetStates n (OAI.EditApproximation.seedGridSpacing b P) value q

def historyInputCode {M n : ℕ} (input : Fin M × ℕ × OAI.EditApproximation.TargetInterval n) : ℕ :=
  Nat.pair input.2.1 (OAI.EditApproximation.childInputCode (input.1, input.2.2))

def localOnlineSourceKeys {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : OAI.EditApproximation.TargetInterval n → ℚ) (q : OAI.EditApproximation.TargetInterval n) :
    List (ℕ × OAI.EditApproximation.TargetInterval n) :=
  (OAI.EditApproximation.dyadicQueryWindow N (initial q) a F).map fun b => (b, OAI.EditApproximation.roundInterval (OAI.EditApproximation.seedGridSpacing b P) q)

def queryHistoryCodeWithWork {M n : ℕ} (input : Fin M × ℕ × OAI.EditApproximation.TargetInterval n) : ℕ × ℕ :=
  let child := OAI.EditApproximation.queryChildCodeWithWork (input.1, input.2.2)
  let pair := OAI.EditApproximation.queryPairWithWork input.2.1 child.1
  (pair.1, child.2 + pair.2 + 1)

def queryOrderedChildInputsWithWork {M n : ℕ} (inputs : List (Fin M × OAI.EditApproximation.TargetInterval n)) :
    List (Fin M × OAI.EditApproximation.TargetInterval n) × ℕ :=
  OAI.EditApproximation.queryOrderedInputsWithWork OAI.EditApproximation.coordinateEqualWithWork
    (OAI.EditApproximation.queryEncodedLEWithWork OAI.EditApproximation.queryChildCodeWithWork) inputs

def queryHistoryEqualWithWork {M n : ℕ} (a b : Fin M × ℕ × OAI.EditApproximation.TargetInterval n) : Bool × ℕ :=
  let child := OAI.EditApproximation.coordinateEqualWithWork (a.1, a.2.2) (b.1, b.2.2)
  let time := OAI.EditApproximation.naturalEqualWithWork a.2.1 b.2.1
  (child.1 && time.1, child.2 + time.2 + 1)

def queryGapStatesWithWork (n g anchor radius sourceLength gapRadius : ℕ) :
    List (OAI.EditApproximation.TargetInterval n) × ℕ :=
  let lo := OAI.EditApproximation.saturatingSubtractWithWork anchor radius
  let hi := OAI.EditApproximation.binaryNaturalAddWithWork anchor radius
  let left := OAI.EditApproximation.gridPointsWithWork g (OAI.EditApproximation.bitWordValue lo.1) (OAI.EditApproximation.bitWordValue hi.1)
  let states := OAI.EditApproximation.arithmeticFlatMapWithWork (fun first =>
    let center := OAI.EditApproximation.binaryNaturalAddWithWork first sourceLength
    let lower := OAI.EditApproximation.saturatingSubtractWithWork (OAI.EditApproximation.bitWordValue center.1) gapRadius
    let upper := OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue center.1) gapRadius
    let right := OAI.EditApproximation.gridPointsWithWork g (OAI.EditApproximation.bitWordValue lower.1) (OAI.EditApproximation.bitWordValue upper.1)
    let valid := OAI.EditApproximation.filterMapWithWork (OAI.EditApproximation.makeStateWithWork n first) right.1
    (valid.1, center.2 + lower.2 + upper.2 + right.2 + valid.2 + 4)) left.1
  (states.1, lo.2 + hi.2 + left.2 + states.2 + 3)

def queryOnlineKeyEqualWithWork {n : ℕ} (a b : ℕ × OAI.EditApproximation.TargetInterval n) : Bool × ℕ :=
  let scale := OAI.EditApproximation.naturalEqualWithWork a.1 b.1
  let state := OAI.EditApproximation.queryIntervalEqualWithWork a.2 b.2
  (scale.1 && state.1, scale.2 + state.2 + 1)

def physicalEntryCode {M J n : ℕ} (state : OAI.EditApproximation.PhysicalEntry M J n) : ℕ :=
  OAI.EditApproximation.childInputCode ((0 : Fin 1), state.2) + (n + 1) ^ 2 * OAI.EditApproximation.physicalNodeCode state.1

def rankedBitLocalWork {κ : Type u_1} (rank : κ → ℕ)
    (program : (key : κ) → OAI.EditApproximation.BitQuery {child : κ // rank child < rank key} OAI.EditApproximation.BinaryFraction)
    (key : κ) : ℕ :=
  (program key).work (fun child => OAI.EditApproximation.rankedBitProgramValue rank program child.val) (fun _ => 0)

def refinementParameterWordsWithWork (N pass : ℕ) (word : List Bool)
    (hpositive : 0 < OAI.EditApproximation.bitWordValue word) : OAI.EditApproximation.RefinementParameterWords × ℕ :=
  let online := OAI.EditApproximation.BinaryFraction.onlineParametersWithWork word hpositive
  let factor := OAI.EditApproximation.scheduledRefinementWordWithWork N pass
  let decrement := OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork word hpositive
  (⟨online.1.2, factor.1, online.1.1, online.1.2, decrement.1⟩,
    online.2 + factor.2 + decrement.2 + 5)

def queryHistoryEqualAllocation {M n : ℕ} (a b : Fin M × ℕ × OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.coordinateEqualAllocation (a.1, a.2.2) (b.1, b.2.2) + OAI.EditApproximation.naturalEqualAllocation a.2.1 b.2.1 + 1

def queryOnlineKeyEqualAllocation {n : ℕ} (a b : ℕ × OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.naturalEqualAllocation a.1 b.1 + OAI.EditApproximation.queryIntervalEqualAllocation a.2 b.2 + 1

def gridStateBoxAllocation (n g radius lo hi : ℕ) : ℕ :=
  let leftLow := (OAI.EditApproximation.saturatingSubtractWithWork lo radius).1
  let leftHigh := (OAI.EditApproximation.binaryNaturalAddWithWork lo radius).1
  let rightLow := (OAI.EditApproximation.saturatingSubtractWithWork hi radius).1
  let rightHigh := (OAI.EditApproximation.binaryNaturalAddWithWork hi radius).1
  let left := (OAI.EditApproximation.gridPointsWithWork g (OAI.EditApproximation.bitWordValue leftLow) (OAI.EditApproximation.bitWordValue leftHigh)).1
  let right := (OAI.EditApproximation.gridPointsWithWork g (OAI.EditApproximation.bitWordValue rightLow) (OAI.EditApproximation.bitWordValue rightHigh)).1
  OAI.EditApproximation.saturatingSubtractAllocation lo radius + OAI.EditApproximation.binaryNaturalAddAllocation lo radius +
    OAI.EditApproximation.saturatingSubtractAllocation hi radius + OAI.EditApproximation.binaryNaturalAddAllocation hi radius +
    OAI.EditApproximation.gridPointsAllocation g (OAI.EditApproximation.bitWordValue leftLow) (OAI.EditApproximation.bitWordValue leftHigh) +
    OAI.EditApproximation.gridPointsAllocation g (OAI.EditApproximation.bitWordValue rightLow) (OAI.EditApproximation.bitWordValue rightHigh) +
    OAI.EditApproximation.arithmeticFlatMapAllocation (fun s => OAI.EditApproximation.filterMapWithWork (OAI.EditApproximation.makeStateWithWork n s) right)
      (fun s => OAI.EditApproximation.filterMapAllocation (OAI.EditApproximation.makeStateWithWork n s) (OAI.EditApproximation.makeStateAllocation n s) right) left

def queryHistoryCodeAllocation {M n : ℕ} (input : Fin M × ℕ × OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.queryChildCodeAllocation (input.1, input.2.2) +
    OAI.EditApproximation.queryPairAllocation input.2.1 (OAI.EditApproximation.queryChildCodeWithWork (input.1, input.2.2)).1

def queryOrderedChildInputsAllocation {M n : ℕ} (inputs : List (Fin M × OAI.EditApproximation.TargetInterval n)) : ℕ :=
  OAI.EditApproximation.queryOrderedInputsAllocation OAI.EditApproximation.coordinateEqualWithWork (OAI.EditApproximation.queryEncodedLEWithWork OAI.EditApproximation.queryChildCodeWithWork)
    OAI.EditApproximation.coordinateEqualAllocation (OAI.EditApproximation.queryEncodedLEAllocation OAI.EditApproximation.queryChildCodeWithWork OAI.EditApproximation.queryChildCodeAllocation) inputs

def actionMemberAllocation {n M : ℕ} (a : Fin M → OAI.EditApproximation.TargetInterval n) : List (Fin M → OAI.EditApproximation.TargetInterval n) → ℕ
  | [] => 0
  | b :: rest => OAI.EditApproximation.actionEqualAllocation a b + actionMemberAllocation a rest

def queryGapStatesAllocation (n g anchor radius sourceLength gapRadius : ℕ) : ℕ :=
  let lo := (OAI.EditApproximation.saturatingSubtractWithWork anchor radius).1
  let hi := (OAI.EditApproximation.binaryNaturalAddWithWork anchor radius).1
  let left := (OAI.EditApproximation.gridPointsWithWork g (OAI.EditApproximation.bitWordValue lo) (OAI.EditApproximation.bitWordValue hi)).1
  let build := fun first =>
    let center := OAI.EditApproximation.binaryNaturalAddWithWork first sourceLength
    let lower := OAI.EditApproximation.saturatingSubtractWithWork (OAI.EditApproximation.bitWordValue center.1) gapRadius
    let upper := OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue center.1) gapRadius
    let right := OAI.EditApproximation.gridPointsWithWork g (OAI.EditApproximation.bitWordValue lower.1) (OAI.EditApproximation.bitWordValue upper.1)
    let valid := OAI.EditApproximation.filterMapWithWork (OAI.EditApproximation.makeStateWithWork n first) right.1
    (valid.1, center.2 + lower.2 + upper.2 + right.2 + valid.2 + 4)
  let allocation := fun first =>
    let center := (OAI.EditApproximation.binaryNaturalAddWithWork first sourceLength).1
    let lower := (OAI.EditApproximation.saturatingSubtractWithWork (OAI.EditApproximation.bitWordValue center) gapRadius).1
    let upper := (OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue center) gapRadius).1
    let right := (OAI.EditApproximation.gridPointsWithWork g (OAI.EditApproximation.bitWordValue lower) (OAI.EditApproximation.bitWordValue upper)).1
    OAI.EditApproximation.binaryNaturalAddAllocation first sourceLength + OAI.EditApproximation.saturatingSubtractAllocation (OAI.EditApproximation.bitWordValue center) gapRadius +
      OAI.EditApproximation.binaryNaturalAddAllocation (OAI.EditApproximation.bitWordValue center) gapRadius + OAI.EditApproximation.gridPointsAllocation g (OAI.EditApproximation.bitWordValue lower) (OAI.EditApproximation.bitWordValue upper) +
      OAI.EditApproximation.filterMapAllocation (OAI.EditApproximation.makeStateWithWork n first) (OAI.EditApproximation.makeStateAllocation n first) right
  OAI.EditApproximation.saturatingSubtractAllocation anchor radius + OAI.EditApproximation.binaryNaturalAddAllocation anchor radius +
    OAI.EditApproximation.gridPointsAllocation g (OAI.EditApproximation.bitWordValue lo) (OAI.EditApproximation.bitWordValue hi) + OAI.EditApproximation.arithmeticFlatMapAllocation build allocation left

def wideActionList {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b P : ℕ) : List (Fin M → OAI.EditApproximation.TargetInterval ny) :=
  OAI.EditApproximation.finiteAssignments M (OAI.EditApproximation.wideChildStateList parent r b P)

def physicalSourceInterval {M J : ℕ} (nx : ℕ) (node : OAI.EditApproximation.PhysicalNode M J) : OAI.EditApproximation.TargetInterval nx :=
  OAI.EditApproximation.sourceIntervalAt M nx node.1.val node.2

def localInitialConeTable {α : Type u_1} (source target : List α)
    (U : OAI.EditApproximation.TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (q : OAI.EditApproximation.TargetInterval target.length) : ℚ :=
  if U q = 0 then 0 else
    OAI.EditApproximation.rationalMinimum ((32 * F + 1) * N)
      ((OAI.EditApproximation.localInitialConeCenters N P A U q).map
        (OAI.EditApproximation.initialConeValue source target U a (32 * F) q))

def wideChildGridWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b P : ℕ) (i : Fin M) : List (OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let child := OAI.EditApproximation.sourceChildWithWork parent i
  let spacing := OAI.EditApproximation.seedGridSpacingWithWork b P
  let radius := OAI.EditApproximation.binaryNaturalMulWithWork 10 b
  let leftOffset := OAI.EditApproximation.saturatingSubtractWithWork child.1.lo parent.lo
  let rightOffset := OAI.EditApproximation.saturatingSubtractWithWork child.1.hi parent.lo
  let left := OAI.EditApproximation.binaryNaturalAddWithWork r.lo (OAI.EditApproximation.bitWordValue leftOffset.1)
  let right := OAI.EditApproximation.binaryNaturalAddWithWork r.lo (OAI.EditApproximation.bitWordValue rightOffset.1)
  let grid := OAI.EditApproximation.gridStateBoxWithWork ny (OAI.EditApproximation.bitWordValue spacing.1) (OAI.EditApproximation.bitWordValue radius.1)
    (OAI.EditApproximation.bitWordValue left.1) (OAI.EditApproximation.bitWordValue right.1)
  (grid.1, child.2 + spacing.2 + radius.2 + leftOffset.2 + rightOffset.2 + left.2 + right.2 + grid.2 + 8)

def queryOrderedHistoryInputsWithWork {M n : ℕ} (inputs : List (Fin M × ℕ × OAI.EditApproximation.TargetInterval n)) :
    List (Fin M × ℕ × OAI.EditApproximation.TargetInterval n) × ℕ :=
  OAI.EditApproximation.queryOrderedInputsWithWork OAI.EditApproximation.queryHistoryEqualWithWork
    (OAI.EditApproximation.queryEncodedLEWithWork OAI.EditApproximation.queryHistoryCodeWithWork) inputs

def queryNeededInputsWithWork {n M : ℕ}
    (selected online : List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval n) (Fin M × OAI.EditApproximation.TargetInterval n) M)) :
    List (Fin M × OAI.EditApproximation.TargetInterval n) × ℕ :=
  let first := OAI.EditApproximation.queryActionInputsWithWork selected
  let second := OAI.EditApproximation.queryActionInputsWithWork online
  let sorted := OAI.EditApproximation.queryOrderedChildInputsWithWork (first.1 ++ second.1)
  (sorted.1, first.2 + second.2 + first.1.length + sorted.2 + 2)

theorem _root_.OAI.EditApproximation.Lemmas.computed_small_word_pos (N : ℕ) : 0 < OAI.EditApproximation.bitWordValue (OAI.EditApproximation.inputSmallLog N).bits := by
  rw [OAI.EditApproximation.Lemmas.bitWordValue_bits]
  exact Nat.two_pow_pos _

def computedQueryParameters (N pass : ℕ) : OAI.EditApproximation.RefinementParameterWords := by
  exact
    (OAI.EditApproximation.refinementParameterWordsWithWork N pass (OAI.EditApproximation.inputSmallLog N).bits (OAI.EditApproximation.Lemmas.computed_small_word_pos N)).1

def wideChildGridAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b P : ℕ) (i : Fin M) : ℕ :=
  let child := (OAI.EditApproximation.sourceChildWithWork parent i).1
  let spacing := (OAI.EditApproximation.seedGridSpacingWithWork b P).1
  let radius := (OAI.EditApproximation.binaryNaturalMulWithWork 10 b).1
  let leftOffset := (OAI.EditApproximation.saturatingSubtractWithWork child.lo parent.lo).1
  let rightOffset := (OAI.EditApproximation.saturatingSubtractWithWork child.hi parent.lo).1
  let left := (OAI.EditApproximation.binaryNaturalAddWithWork r.lo (OAI.EditApproximation.bitWordValue leftOffset)).1
  let right := (OAI.EditApproximation.binaryNaturalAddWithWork r.lo (OAI.EditApproximation.bitWordValue rightOffset)).1
  OAI.EditApproximation.sourceChildAllocation parent i + OAI.EditApproximation.seedGridSpacingAllocation b P + OAI.EditApproximation.binaryNaturalMulAllocation 10 b +
    OAI.EditApproximation.saturatingSubtractAllocation child.lo parent.lo + OAI.EditApproximation.saturatingSubtractAllocation child.hi parent.lo +
    OAI.EditApproximation.binaryNaturalAddAllocation r.lo (OAI.EditApproximation.bitWordValue leftOffset) +
    OAI.EditApproximation.binaryNaturalAddAllocation r.lo (OAI.EditApproximation.bitWordValue rightOffset) +
    OAI.EditApproximation.gridStateBoxAllocation ny (OAI.EditApproximation.bitWordValue spacing) (OAI.EditApproximation.bitWordValue radius) (OAI.EditApproximation.bitWordValue left) (OAI.EditApproximation.bitWordValue right)

def queryOrderedHistoryInputsAllocation {M n : ℕ} (inputs : List (Fin M × ℕ × OAI.EditApproximation.TargetInterval n)) : ℕ :=
  OAI.EditApproximation.queryOrderedInputsAllocation OAI.EditApproximation.queryHistoryEqualWithWork (OAI.EditApproximation.queryEncodedLEWithWork OAI.EditApproximation.queryHistoryCodeWithWork)
    OAI.EditApproximation.queryHistoryEqualAllocation (OAI.EditApproximation.queryEncodedLEAllocation OAI.EditApproximation.queryHistoryCodeWithWork OAI.EditApproximation.queryHistoryCodeAllocation) inputs

def queryNeededInputsAllocation {n M : ℕ}
    (selected online : List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval n) (Fin M × OAI.EditApproximation.TargetInterval n) M)) : ℕ :=
  let first := (OAI.EditApproximation.queryActionInputsWithWork selected).1
  let second := (OAI.EditApproximation.queryActionInputsWithWork online).1
  OAI.EditApproximation.queryActionInputsAllocation selected + OAI.EditApproximation.queryActionInputsAllocation online + first.length +
    OAI.EditApproximation.queryOrderedChildInputsAllocation (first ++ second)

def physicalSource {α : Type u_1} {M J : ℕ} (source : List α) (node : OAI.EditApproximation.PhysicalNode M J) : List α :=
  OAI.EditApproximation.substring source (OAI.EditApproximation.physicalSourceInterval source.length node).lo (OAI.EditApproximation.physicalSourceInterval source.length node).hi

def wideActionGridWithWork {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b P : ℕ) : List (Vector (OAI.EditApproximation.TargetInterval ny) M) × ℕ :=
  let choices := OAI.EditApproximation.vectorMapWithWork M (OAI.EditApproximation.wideChildGridWithWork parent r b P)
  let product := OAI.EditApproximation.materializedAssignmentsWithWork M choices.1.get
  (product.1, choices.2 + product.2 + 1)

def physicalCoarsePreparationCost {M J : ℕ} (source target : List ℕ)
    (entry : OAI.EditApproximation.PhysicalEntry M J target.length) : ℕ :=
  let interval := OAI.EditApproximation.physicalSourceInterval source.length entry.1
  (OAI.EditApproximation.coarsePreparedSlicesWithWork source target interval.lo interval.hi entry.2.lo entry.2.hi).2

def wideActionGridAllocation {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b P : ℕ) : ℕ :=
  let choices := (OAI.EditApproximation.vectorMapWithWork M (OAI.EditApproximation.wideChildGridWithWork parent r b P)).1
  OAI.EditApproximation.vectorMapAllocation M (OAI.EditApproximation.wideChildGridAllocation parent r b P) + OAI.EditApproximation.materializedAssignmentsAllocation M choices.get

end OAI.EditApproximation

end



-- Prove2me | Definitions.Def_EditApproxScheme_02
-- name    : EditApproxScheme_02
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:30:39.072425+00:00
-- url     : https://prove2.me/theorems/1c4c511b-c9c7-4344-94c6-ddf5eab87e3b
-- title:
--   Edit-distance approximation scheme, part 2 of 20: comparisons, grid states and online integers
-- statement:
--   This is **part 2 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains encoded comparisons, padded reads of coarse source descriptors, the construction of interval states and grid points, binary multiplication of naturals, prepared source slices, the triangular mass and rational maximum used by the optimizer, and bounded online integers. It also proves 12 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L762-L1372 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 2 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_01

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def queryEncodedLEWithWork {α : Type u_1} (code : α → ℕ × ℕ) (a b : α) : Bool × ℕ :=
  let left := code a
  let right := code b
  let comparison := OAI.EditApproximation.wordLEWithWork left.1.bits right.1.bits
  (comparison.1, left.2 + right.2 + comparison.2 + Nat.size left.1 + Nat.size right.1 + 3)

instance largeAccuracyInput_decidable (N : ℕ) (epsilon : ℚ) : Decidable (OAI.EditApproximation.largeAccuracyInput N epsilon) :=
  inferInstanceAs (Decidable (2 ^ 1000 ≤ OAI.EditApproximation.inputSmallLog N ∧ 10 ≤ (OAI.EditApproximation.inputSmallLog N : ℚ) * epsilon))

def chargedSuffixDP {α : Type u_1} [DecidableEq α] : List α → List α → List ℕ × ℕ
  | [], target =>
    (List.ofFn (fun j : Fin (target.length + 1) => target.length - j.val),
      4 * (target.length + 1))
  | a :: rest, target =>
    let previous := chargedSuffixDP rest target
    let cells := List.ofFn fun j : Fin (target.length + 1) => OAI.EditApproximation.dpCell a target previous.1 j.val
    (cells.map Prod.fst, previous.2 + (cells.map Prod.snd).sum +
      2 * (OAI.EditApproximation.dpLength target).2 + 2 * cells.length + 3)

def computedCoarseDepth (N n : ℕ) : ℕ := Nat.clog (OAI.EditApproximation.integerParameters N).B (max 1 n)

def queryRangeValidWithWork (B range : ℕ) : Bool × ℕ :=
  let positive := OAI.EditApproximation.binaryNaturalCompareWithWork 0 range
  let bounded := OAI.EditApproximation.wordLEWithWork range.bits B.bits
  (decide (positive.1 = .lt) && bounded.1, positive.2 + bounded.2 + 2)

def coarsePaddedReadWithWork {α : Type u_1} (n : ℕ) (source : List α) (offset : ℕ) :
    Option (Option α) × ℕ :=
  let inside := OAI.EditApproximation.binaryNaturalCompareWithWork offset n
  (if inside.1 = .lt then some source[offset]? else none,
    inside.2 + Nat.size n + Nat.size offset + 2)

def coarseRangeCopyWithWork (read : ℕ → ℕ) : ℕ → ℕ → List ℕ × ℕ
  | _, 0 => ([], 1)
  | start, length + 1 =>
    let next := OAI.EditApproximation.binaryNaturalAddWithWork start 1
    let tail := coarseRangeCopyWithWork read (OAI.EditApproximation.bitWordValue next.1) length
    (read start :: tail.1, tail.2 + next.2 + Nat.size start + Nat.size (read start) + 3)

def bitMulAllocation : List Bool → List Bool → ℕ
  | [], _ => 0
  | bit :: bits, right =>
    bitMulAllocation bits right + 1 +
      if bit then OAI.EditApproximation.bitAddAllocation (false :: (OAI.EditApproximation.bitMulWithWork bits right).1) right false else 0

def bitDivModAllocation (divisor : List Bool) : List Bool → ℕ
  | [] => 0
  | bit :: bits =>
    let candidate := bit :: (OAI.EditApproximation.bitDivModWithWork divisor bits).2.1
    bitDivModAllocation divisor bits + 2 +
      if (OAI.EditApproximation.bitCompareWithWork candidate divisor).1 = .lt then 0
      else OAI.EditApproximation.bitSubtractAllocation candidate divisor false

def saturatingSubtractAllocation (a b : ℕ) : ℕ :=
  a.bits.length + b.bits.length +
    if (OAI.EditApproximation.binaryNaturalCompareWithWork a b).1 = .lt then 0 else OAI.EditApproximation.bitSubtractAllocation a.bits b.bits false

def makeStateAllocation (n lo hi : ℕ) : ℕ :=
  OAI.EditApproximation.naturalWordLEAllocation lo.bits hi.bits + OAI.EditApproximation.naturalWordLEAllocation hi.bits n.bits +
    if ((OAI.EditApproximation.wordLEWithWork lo.bits hi.bits).1 && (OAI.EditApproximation.wordLEWithWork hi.bits n.bits).1) = true then 2 else 0

def translatedEndpointAllocation (reference root endpoint : ℕ) : ℕ :=
  OAI.EditApproximation.bitSubtractAllocation endpoint.bits root.bits false +
    OAI.EditApproximation.binaryNaturalAddAllocation reference (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalSubtractWithWork endpoint root).1)

def wordInsertAllocation (a : List Bool) : List (List Bool) → ℕ
  | [] => 1
  | b :: rest => OAI.EditApproximation.wordLEAllocation a b +
    if (OAI.EditApproximation.wordLEWithWork a b).1 then 2 else wordInsertAllocation a rest + 1

def wordSortWithWork : List (List Bool) → List (List Bool) × ℕ
  | [] => ([], 1)
  | a :: rest =>
    let tail := wordSortWithWork rest
    let inserted := OAI.EditApproximation.wordInsertWithWork a tail.1
    (inserted.1, tail.2 + inserted.2 + 2)

def binaryGridRoundWithWork (spacing position : ℕ) : List Bool × ℕ :=
  let quotient := OAI.EditApproximation.binaryNaturalDivModWithWork position spacing
  let rounded := OAI.EditApproximation.bitMulWithWork spacing.bits quotient.1
  (rounded.1, quotient.2.2 + rounded.2 + 2)

def gridPointsWithWork (g lo hi : ℕ) : List ℕ × ℕ :=
  let lower := OAI.EditApproximation.bitCeilDivWithWork g.bits lo.bits
  let upper := OAI.EditApproximation.binaryNaturalDivModWithWork hi g
  let stop := OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue upper.1) 1
  let count := OAI.EditApproximation.saturatingSubtractWithWork (OAI.EditApproximation.bitWordValue stop.1) (OAI.EditApproximation.bitWordValue lower.1)
  let indices := List.range' (OAI.EditApproximation.bitWordValue lower.1) (OAI.EditApproximation.bitWordValue count.1)
  let points := OAI.EditApproximation.arithmeticMapWithWork (fun i =>
    let product := OAI.EditApproximation.binaryNaturalMulWithWork g i
    (OAI.EditApproximation.bitWordValue product.1, product.2 + Nat.size i + 2)) indices
  (points.1, lower.2 + upper.2.2 + stop.2 + count.2 + points.2 +
    Nat.size g + Nat.size lo + Nat.size hi + 5)

def seedGridSpacingWithWork (b P : ℕ) : List Bool × ℕ :=
  let quotient := OAI.EditApproximation.binaryNaturalDivModWithWork b P
  let test := OAI.EditApproximation.wordLEWithWork quotient.1 [true]
  (if test.1 then [true] else quotient.1, quotient.2.2 + test.2 + 2)

def balancedCutWithWork (lo width M i : ℕ) : List Bool × ℕ :=
  let product := OAI.EditApproximation.binaryNaturalMulWithWork i width
  let quotient := OAI.EditApproximation.binaryNaturalDivModWithWork (OAI.EditApproximation.bitWordValue product.1) M
  let result := OAI.EditApproximation.binaryNaturalAddWithWork lo (OAI.EditApproximation.bitWordValue quotient.1)
  (result.1, product.2 + quotient.2.2 + result.2 + 2)

def triangularMassWithWork (K : ℕ) : List Bool × ℕ :=
  let next := OAI.EditApproximation.binaryNaturalAddWithWork K 1
  let product := OAI.EditApproximation.binaryNaturalMulWithWork K (OAI.EditApproximation.bitWordValue next.1)
  let quotient := OAI.EditApproximation.binaryNaturalDivModWithWork (OAI.EditApproximation.bitWordValue product.1) 2
  (quotient.1, next.2 + product.2 + quotient.2.2 + 3)

def refinementBaseWithWork (ell : List Bool) : List Bool × ℕ :=
  let power := OAI.EditApproximation.bitPowerWithWork ell 10
  let increment := OAI.EditApproximation.bitAddWithWork power.1 [true] false
  let result := OAI.EditApproximation.trimBitWordWithWork increment.1
  (result.1, power.2 + increment.2 + result.2 + 2)

def queryPairWithWork (a b : ℕ) : ℕ × ℕ :=
  let test := OAI.EditApproximation.binaryNaturalCompareWithWork a b
  if test.1 = .lt then
    let square := OAI.EditApproximation.binaryNaturalMulWithWork b b
    let result := OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue square.1) a
    (OAI.EditApproximation.bitWordValue result.1, test.2 + square.2 + result.2 + 3)
  else
    let square := OAI.EditApproximation.binaryNaturalMulWithWork a a
    let linear := OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue square.1) a
    let result := OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue linear.1) b
    (OAI.EditApproximation.bitWordValue result.1, test.2 + square.2 + linear.2 + result.2 + 4)

def queryCellValidWithWork (n exponent : ℕ) (cell : ℕ × ℕ) : Bool × ℕ :=
  let cap := OAI.EditApproximation.binaryNaturalMulWithWork n (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.powerTwoWord exponent))
  let left := OAI.EditApproximation.wordLEWithWork cell.1.bits cap.1
  let right := OAI.EditApproximation.wordLEWithWork cell.2.bits cap.1
  (left.1 && right.1, cap.2 + left.2 + right.2 + exponent + 4)

theorem _root_.OAI.EditApproximation.Lemmas.bitOrdering_matches (high : Ordering) (a : Bool) (b : Bool) (x : ℕ) (y : ℕ) (h : OAI.EditApproximation.orderingMatches high x y) :
    OAI.EditApproximation.orderingMatches (OAI.EditApproximation.bitOrdering high a b) (a.toNat + 2 * x) (b.toNat + 2 * y) := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, by cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩
  · cases a <;> cases b <;> simp [OAI.EditApproximation.bitOrdering, OAI.EditApproximation.orderingMatches]
  · exact Or.inr (Or.inr ⟨rfl, by
      cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩)

theorem _root_.OAI.EditApproximation.Lemmas.bitCompareWithWork_matches (left : List.{0} Bool) (right : List.{0} Bool) :
    OAI.EditApproximation.orderingMatches (OAI.EditApproximation.bitCompareWithWork left right).1 (OAI.EditApproximation.bitWordValue left) (OAI.EditApproximation.bitWordValue right) := by
  induction left generalizing right with
  | nil =>
    simp only [OAI.EditApproximation.bitCompareWithWork]
    induction right with
    | nil => (simp [OAI.EditApproximation.bitCompareNilLeftWithWork, OAI.EditApproximation.orderingMatches, OAI.EditApproximation.bitWordValue])
    | cons b bs ih =>
      simpa only [OAI.EditApproximation.bitCompareNilLeftWithWork, OAI.EditApproximation.bitWordValue, Bool.toNat_false, Nat.add_zero, Nat.mul_zero,
        Nat.zero_add] using OAI.EditApproximation.Lemmas.bitOrdering_matches (OAI.EditApproximation.bitCompareNilLeftWithWork bs).1 false b 0 (OAI.EditApproximation.bitWordValue bs) ih
  | cons a as ih =>
    cases right with
    | nil =>
      simpa only [OAI.EditApproximation.bitCompareWithWork, OAI.EditApproximation.bitWordValue, Bool.toNat_false, Nat.add_zero, Nat.mul_zero,
        Nat.zero_add] using OAI.EditApproximation.Lemmas.bitOrdering_matches (OAI.EditApproximation.bitCompareWithWork as []).1 a false (OAI.EditApproximation.bitWordValue as) 0 (ih [])
    | cons b bs =>
      simpa only [OAI.EditApproximation.bitCompareWithWork, OAI.EditApproximation.bitWordValue] using
        OAI.EditApproximation.Lemmas.bitOrdering_matches (OAI.EditApproximation.bitCompareWithWork as bs).1 a b (OAI.EditApproximation.bitWordValue as) (OAI.EditApproximation.bitWordValue bs) (ih bs)

theorem _root_.OAI.EditApproximation.Lemmas.bitCompareWithWork_lt (left : List.{0} Bool) (right : List.{0} Bool) :
    (OAI.EditApproximation.bitCompareWithWork left right).1 = .lt ↔ OAI.EditApproximation.bitWordValue left < OAI.EditApproximation.bitWordValue right := by
  have h := OAI.EditApproximation.Lemmas.bitCompareWithWork_matches left right
  rcases h with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ <;> rw [h] <;> simp_all
  all_goals omega

theorem _root_.OAI.EditApproximation.Lemmas.bitSubtractor_value (a : Bool) (b : Bool) (borrow : Bool) :
    a.toNat + 2 * (OAI.EditApproximation.bitBorrow a b borrow).toNat =
      b.toNat + borrow.toNat + (OAI.EditApproximation.bitDifference a b borrow).toNat := by
  cases a <;> cases b <;> cases borrow <;> decide

theorem _root_.OAI.EditApproximation.Lemmas.bitSubtractionRippleEquation (a : ℕ) (b : ℕ) (borrow : ℕ) (nextBorrow : ℕ) (difference : ℕ) (left : ℕ) (right : ℕ) (result : ℕ) (tail : ℕ) (htail : Eq.{1} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} result right) nextBorrow) (HAdd.hAdd.{0, 0, 0} left tail)) (hbit : Eq.{1} (HAdd.hAdd.{0, 0, 0} a (HMul.hMul.{0, 0, 0} 2 nextBorrow))
  (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b borrow) difference)) :
    (difference + 2 * result) + (b + 2 * right) + borrow =
      (a + 2 * left) + 2 * tail := by
  omega

theorem _root_.OAI.EditApproximation.Lemmas.bitSubtractWithWork_value (left : List.{0} Bool) (right : List.{0} Bool) (borrow : Bool) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitSubtractWithWork left right borrow).1 + OAI.EditApproximation.bitWordValue right + borrow.toNat =
      OAI.EditApproximation.bitWordValue left + 2 ^ max left.length right.length *
        (OAI.EditApproximation.bitSubtractWithWork left right borrow).2.1.toNat := by
  induction left generalizing right borrow with
  | nil =>
    induction right generalizing borrow with
    | nil => (simp [OAI.EditApproximation.bitSubtractWithWork, OAI.EditApproximation.bitSubtractNilLeftWithWork, OAI.EditApproximation.bitWordValue])
    | cons b bs ih =>
      have h := ih (OAI.EditApproximation.bitBorrow false b borrow)
      have hb := OAI.EditApproximation.Lemmas.bitSubtractor_value false b borrow
      (simp only [OAI.EditApproximation.bitSubtractWithWork, OAI.EditApproximation.bitSubtractNilLeftWithWork, OAI.EditApproximation.bitWordValue,
        List.length_nil, List.length_cons, Nat.zero_max, pow_succ, Bool.toNat_false] at h hb ⊢)
      have hs := OAI.EditApproximation.Lemmas.bitSubtractionRippleEquation 0 b.toNat borrow.toNat (OAI.EditApproximation.bitBorrow false b borrow).toNat
        (OAI.EditApproximation.bitDifference false b borrow).toNat 0 (OAI.EditApproximation.bitWordValue bs)
        (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitSubtractNilLeftWithWork bs (OAI.EditApproximation.bitBorrow false b borrow)).1)
        (2 ^ bs.length * (OAI.EditApproximation.bitSubtractNilLeftWithWork bs (OAI.EditApproximation.bitBorrow false b borrow)).2.1.toNat)
        h hb
      simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_assoc,
        Nat.mul_left_comm] using hs
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (OAI.EditApproximation.bitBorrow a false borrow)
      have hb := OAI.EditApproximation.Lemmas.bitSubtractor_value a false borrow
      (simp only [OAI.EditApproximation.bitSubtractWithWork, OAI.EditApproximation.bitWordValue, List.length_nil, List.length_cons,
        Nat.max_zero, pow_succ, Bool.toNat_false] at h hb ⊢)
      have hs := OAI.EditApproximation.Lemmas.bitSubtractionRippleEquation a.toNat 0 borrow.toNat (OAI.EditApproximation.bitBorrow a false borrow).toNat
        (OAI.EditApproximation.bitDifference a false borrow).toNat (OAI.EditApproximation.bitWordValue as) 0
        (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitSubtractWithWork as [] (OAI.EditApproximation.bitBorrow a false borrow)).1)
        (2 ^ as.length * (OAI.EditApproximation.bitSubtractWithWork as [] (OAI.EditApproximation.bitBorrow a false borrow)).2.1.toNat)
        h hb
      simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_assoc,
        Nat.mul_left_comm] using hs
    | cons b bs =>
      have h := ih bs (OAI.EditApproximation.bitBorrow a b borrow)
      have hb := OAI.EditApproximation.Lemmas.bitSubtractor_value a b borrow
      (simp only [OAI.EditApproximation.bitSubtractWithWork, OAI.EditApproximation.bitWordValue, List.length_cons, Nat.succ_max_succ,
        pow_succ] at h hb ⊢)
      have hs := OAI.EditApproximation.Lemmas.bitSubtractionRippleEquation a.toNat b.toNat borrow.toNat (OAI.EditApproximation.bitBorrow a b borrow).toNat
        (OAI.EditApproximation.bitDifference a b borrow).toNat (OAI.EditApproximation.bitWordValue as) (OAI.EditApproximation.bitWordValue bs)
        (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitSubtractWithWork as bs (OAI.EditApproximation.bitBorrow a b borrow)).1)
        (2 ^ max as.length bs.length * (OAI.EditApproximation.bitSubtractWithWork as bs (OAI.EditApproximation.bitBorrow a b borrow)).2.1.toNat)
        h hb
      simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hs

theorem _root_.OAI.EditApproximation.Lemmas.bitWordValue_lt_pow_length (bits : List.{0} Bool) : OAI.EditApproximation.bitWordValue bits < 2 ^ bits.length := by
  induction bits with
  | nil => (simp [OAI.EditApproximation.bitWordValue])
  | cons bit bits ih =>
    cases bit <;> (simp only [OAI.EditApproximation.bitWordValue, List.length_cons, pow_succ, Bool.toNat_false, Bool.toNat_true]) <;> omega

theorem _root_.OAI.EditApproximation.Lemmas.bitSubtractWithWork_length (left : List.{0} Bool) (right : List.{0} Bool) (borrow : Bool) :
    (OAI.EditApproximation.bitSubtractWithWork left right borrow).1.length = max left.length right.length := by
  induction left generalizing right borrow with
  | nil =>
    simp only [OAI.EditApproximation.bitSubtractWithWork]
    induction right generalizing borrow with
    | nil => simp [OAI.EditApproximation.bitSubtractNilLeftWithWork]
    | cons b bs ih => simp [OAI.EditApproximation.bitSubtractNilLeftWithWork, ih]
  | cons a as ih =>
    cases right with
    | nil => simp [OAI.EditApproximation.bitSubtractWithWork, ih]
    | cons b bs => simp [OAI.EditApproximation.bitSubtractWithWork, ih, Nat.succ_max_succ]

theorem _root_.OAI.EditApproximation.Lemmas.bitSubtractWithWork_sub (left : List.{0} Bool) (right : List.{0} Bool) (h : LE.le.{0} (OAI.EditApproximation.bitWordValue right) (OAI.EditApproximation.bitWordValue left)) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitSubtractWithWork left right false).1 = OAI.EditApproximation.bitWordValue left - OAI.EditApproximation.bitWordValue right := by
  have hvalue := OAI.EditApproximation.Lemmas.bitSubtractWithWork_value left right false
  have hlt := OAI.EditApproximation.Lemmas.bitWordValue_lt_pow_length (OAI.EditApproximation.bitSubtractWithWork left right false).1
  rw [OAI.EditApproximation.Lemmas.bitSubtractWithWork_length] at hlt
  cases hb : (OAI.EditApproximation.bitSubtractWithWork left right false).2.1
  · simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hvalue
    omega
  · simp only [hb, Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.add_zero] at hvalue
    omega

theorem _root_.OAI.EditApproximation.Lemmas.bitDivModWithWork_value (divisor : List.{0} Bool) (bits : List.{0} Bool) (hd : LT.lt.{0} 0 (OAI.EditApproximation.bitWordValue divisor)) :
    OAI.EditApproximation.bitWordValue bits = OAI.EditApproximation.bitWordValue divisor * OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitDivModWithWork divisor bits).1 +
      OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitDivModWithWork divisor bits).2.1 ∧
      OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitDivModWithWork divisor bits).2.1 < OAI.EditApproximation.bitWordValue divisor := by
  induction bits with
  | nil => (simp [OAI.EditApproximation.bitDivModWithWork, OAI.EditApproximation.bitWordValue, hd])
  | cons bit bits ih =>
    let previous := OAI.EditApproximation.bitDivModWithWork divisor bits
    let candidate := bit :: previous.2.1
    have hp : OAI.EditApproximation.bitWordValue bits = OAI.EditApproximation.bitWordValue divisor * OAI.EditApproximation.bitWordValue previous.1 +
        OAI.EditApproximation.bitWordValue previous.2.1 := ih.1
    have hr : OAI.EditApproximation.bitWordValue previous.2.1 < OAI.EditApproximation.bitWordValue divisor := ih.2
    have hc : OAI.EditApproximation.bitWordValue candidate < 2 * OAI.EditApproximation.bitWordValue divisor := by
      dsimp only [candidate, OAI.EditApproximation.bitWordValue]
      cases bit <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    by_cases hlt : (OAI.EditApproximation.bitCompareWithWork candidate divisor).1 = .lt
    · have hv := (OAI.EditApproximation.Lemmas.bitCompareWithWork_lt candidate divisor).1 hlt
      simp only [OAI.EditApproximation.bitDivModWithWork, show (OAI.EditApproximation.bitCompareWithWork (bit :: (OAI.EditApproximation.bitDivModWithWork divisor bits).2.1)
        divisor).1 = .lt from hlt, ↓reduceIte]
      change OAI.EditApproximation.bitWordValue (bit :: bits) = OAI.EditApproximation.bitWordValue divisor *
        OAI.EditApproximation.bitWordValue (false :: previous.1) + OAI.EditApproximation.bitWordValue candidate ∧ OAI.EditApproximation.bitWordValue candidate < _
      constructor
      · (simp only [OAI.EditApproximation.bitWordValue, Bool.toNat_false])
        dsimp only [candidate, OAI.EditApproximation.bitWordValue]
        nlinarith only [hp]
      · exact hv
    · have hv : OAI.EditApproximation.bitWordValue divisor ≤ OAI.EditApproximation.bitWordValue candidate := by
        exact Nat.le_of_not_gt (fun h => hlt ((OAI.EditApproximation.Lemmas.bitCompareWithWork_lt candidate divisor).2 h))
      have hs := OAI.EditApproximation.Lemmas.bitSubtractWithWork_sub candidate divisor hv
      simp only [OAI.EditApproximation.bitDivModWithWork, show (OAI.EditApproximation.bitCompareWithWork (bit :: (OAI.EditApproximation.bitDivModWithWork divisor bits).2.1)
        divisor).1 ≠ .lt from hlt, ↓reduceIte]
      change OAI.EditApproximation.bitWordValue (bit :: bits) = OAI.EditApproximation.bitWordValue divisor * OAI.EditApproximation.bitWordValue (true :: previous.1) +
        OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitSubtractWithWork candidate divisor false).1 ∧
        OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitSubtractWithWork candidate divisor false).1 < _
      rw [hs]
      constructor
      · (simp only [OAI.EditApproximation.bitWordValue, Bool.toNat_true])
        have he := Nat.sub_add_cancel hv
        dsimp only [candidate, OAI.EditApproximation.bitWordValue] at he ⊢
        nlinarith only [hp, he]
      · omega

theorem _root_.OAI.EditApproximation.Lemmas.bitWordValue_bits (n : ℕ) : OAI.EditApproximation.bitWordValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [OAI.EditApproximation.bitWordValue]
  | bit bit n h ih =>
    rw [Nat.bits_append_bit n bit h]
    cases bit <;> simp [OAI.EditApproximation.bitWordValue, ih, Nat.bit, Nat.add_comm]

theorem _root_.OAI.EditApproximation.Lemmas.binaryNaturalDivModWithWork_spec (n : ℕ) (d : ℕ) (hd : LT.lt.{0} 0 d) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalDivModWithWork n d).1 = n / d ∧
      OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalDivModWithWork n d).2.1 = n % d := by
  have h := OAI.EditApproximation.Lemmas.bitDivModWithWork_value d.bits n.bits (by simpa only [OAI.EditApproximation.Lemmas.bitWordValue_bits] using hd)
  simp only [OAI.EditApproximation.Lemmas.bitWordValue_bits] at h
  have hmod : n % d = OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitDivModWithWork d.bits n.bits).2.1 := by
    conv_lhs => rw [h.1]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt h.2]
  have hdiv : n / d = OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitDivModWithWork d.bits n.bits).1 := by
    conv_lhs => rw [h.1]
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt h.2, Nat.add_zero]
  exact ⟨hdiv.symm, hmod.symm⟩

def queryFinOfNatWithWork (bound value : ℕ) (hb : 0 < bound) : Fin bound × ℕ := by
  exact
    let result := OAI.EditApproximation.binaryNaturalDivModWithWork value bound
    (⟨OAI.EditApproximation.bitWordValue result.2.1, by
      rw [(OAI.EditApproximation.Lemmas.binaryNaturalDivModWithWork_spec value bound hb).2]
      exact Nat.mod_lt value hb⟩, result.2.2 + 1)

def coarseDenominatorWithWork (allowanceDen q L branching : List Bool) (D : ℕ) :
    List Bool × ℕ :=
  let first := OAI.EditApproximation.bitMulWithWork L branching
  let base := OAI.EditApproximation.bitMulWithWork first.1 q
  let trimmedBase := OAI.EditApproximation.trimBitWordWithWork base.1
  let power := OAI.EditApproximation.bitPowerWithWork trimmedBase.1 D
  let initial := OAI.EditApproximation.bitMulWithWork allowanceDen q
  let product := OAI.EditApproximation.bitMulWithWork initial.1 power.1
  let result := OAI.EditApproximation.trimBitWordWithWork product.1
  (result.1, first.2 + base.2 + trimmedBase.2 + power.2 + initial.2 + product.2 + result.2 + 7)

def coarseFramedReadWithWork {α : Type u_1} (k n : ℕ) (word : List α) (i : ℕ) :
    Option (Option α) × ℕ :=
  let lower := OAI.EditApproximation.binaryNaturalCompareWithWork i k
  if lower.1 = .lt then (none, lower.2 + Nat.size k + Nat.size n + Nat.size i + 2) else
  let finish := OAI.EditApproximation.binaryNaturalAddWithWork k n
  let upper := OAI.EditApproximation.binaryNaturalCompareWithWork i (OAI.EditApproximation.bitWordValue finish.1)
  if upper.1 = .lt then
    let offset := OAI.EditApproximation.saturatingSubtractWithWork i k
    (some word[OAI.EditApproximation.bitWordValue offset.1]?, lower.2 + finish.2 + upper.2 + offset.2 +
      Nat.size k + Nat.size n + Nat.size i + 4)
  else (none, lower.2 + finish.2 + upper.2 + Nat.size k + Nat.size n + Nat.size i + 3)

def coarseDescriptorWithWork (B d n start : ℕ) : List Bool × ℕ :=
  let capacity := OAI.EditApproximation.bitPowerWithWork B.bits d
  let remaining := OAI.EditApproximation.saturatingSubtractWithWork n start
  let clipped := OAI.EditApproximation.wordMinWithWork capacity.1 remaining.1
  (clipped.1, capacity.2 + remaining.2 + clipped.2 +
    Nat.size B + Nat.size d + Nat.size n + Nat.size start + 4)

def coarseChildOffsetWithWork (offset capacity index : ℕ) : List Bool × ℕ :=
  let displacement := OAI.EditApproximation.binaryNaturalMulWithWork index capacity
  let result := OAI.EditApproximation.binaryNaturalAddWithWork offset (OAI.EditApproximation.bitWordValue displacement.1)
  (result.1, displacement.2 + result.2 + Nat.size index + Nat.size capacity + Nat.size offset + 3)

def coarseInputGuardWithWork (sourceLo sourceHi targetLo targetHi : ℕ) : Bool × ℕ :=
  let sourceWidth := OAI.EditApproximation.saturatingSubtractWithWork sourceHi sourceLo
  let targetWidth := OAI.EditApproximation.saturatingSubtractWithWork targetHi targetLo
  let twice := OAI.EditApproximation.binaryNaturalMulWithWork 2 (OAI.EditApproximation.bitWordValue sourceWidth.1)
  let compared := OAI.EditApproximation.binaryNaturalCompareWithWork (OAI.EditApproximation.bitWordValue twice.1) (OAI.EditApproximation.bitWordValue targetWidth.1)
  (decide (compared.1 = .lt), sourceWidth.2 + targetWidth.2 + twice.2 + compared.2 + 6)

def bitPowerAllocation (base : List Bool) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let previous := (OAI.EditApproximation.bitPowerWithWork base n).1
    bitPowerAllocation base n + OAI.EditApproximation.bitMulAllocation previous base +
      OAI.EditApproximation.trimBitWordAllocation (OAI.EditApproximation.bitMulWithWork previous base).1

def bitCeilDivAllocation (divisor bits : List Bool) : ℕ :=
  let divided := OAI.EditApproximation.bitDivModWithWork divisor bits
  OAI.EditApproximation.bitDivModAllocation divisor bits +
    if (OAI.EditApproximation.bitCompareWithWork divided.2.1 []).1 = .eq then 0
    else 1 + OAI.EditApproximation.bitAddAllocation divided.1 [true] false

def binaryNaturalMulAllocation (a b : ℕ) : ℕ := OAI.EditApproximation.bitMulAllocation a.bits b.bits

def binaryNaturalDivAllocation (a b : ℕ) : ℕ := OAI.EditApproximation.bitDivModAllocation b.bits a.bits

def triangularMassAllocation (K : ℕ) : ℕ :=
  let next := (OAI.EditApproximation.binaryNaturalAddWithWork K 1).1
  let product := (OAI.EditApproximation.binaryNaturalMulWithWork K (OAI.EditApproximation.bitWordValue next)).1
  OAI.EditApproximation.bitAddAllocation K.bits (1 : ℕ).bits false +
    OAI.EditApproximation.bitMulAllocation K.bits (OAI.EditApproximation.bitWordValue next).bits +
    OAI.EditApproximation.bitDivModAllocation (2 : ℕ).bits (OAI.EditApproximation.bitWordValue product).bits

def binaryIntervalRoundWithWork (spacing lo hi : ℕ) : (List Bool × List Bool) × ℕ :=
  let left := OAI.EditApproximation.binaryGridRoundWithWork spacing lo
  let right := OAI.EditApproximation.binaryGridRoundWithWork spacing hi
  ((left.1, right.1), left.2 + right.2 + 1)

def computedQueryBase (N : ℕ) : List Bool :=
  (OAI.EditApproximation.refinementBaseWithWork (OAI.EditApproximation.inputSmallLog N).bits).1

def coarsePreparedSlicesWithWork (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi : ℕ) : Option (List ℕ × List ℕ) × ℕ :=
  let guard := OAI.EditApproximation.coarseInputGuardWithWork sourceLo sourceHi targetLo targetHi
  if guard.1 then (none, guard.2) else
  let copiedSource := OAI.EditApproximation.coarseRangeCopyWithWork (fun i => source[i]?.getD 0) sourceLo (sourceHi - sourceLo)
  let copiedTarget := OAI.EditApproximation.coarseRangeCopyWithWork (fun i => target[i]?.getD 0) targetLo (targetHi - targetLo)
  (some (copiedSource.1, copiedTarget.1), guard.2 + copiedSource.2 + copiedTarget.2)

def gridPointsAllocation (g lo hi : ℕ) : ℕ :=
  let lower := (OAI.EditApproximation.bitCeilDivWithWork g.bits lo.bits).1
  let upper := (OAI.EditApproximation.binaryNaturalDivModWithWork hi g).1
  let stop := (OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue upper) 1).1
  let count := (OAI.EditApproximation.saturatingSubtractWithWork (OAI.EditApproximation.bitWordValue stop) (OAI.EditApproximation.bitWordValue lower)).1
  let indices := List.range' (OAI.EditApproximation.bitWordValue lower) (OAI.EditApproximation.bitWordValue count)
  OAI.EditApproximation.bitCeilDivAllocation g.bits lo.bits + OAI.EditApproximation.binaryNaturalDivAllocation hi g +
    OAI.EditApproximation.binaryNaturalAddAllocation (OAI.EditApproximation.bitWordValue upper) 1 +
    OAI.EditApproximation.saturatingSubtractAllocation (OAI.EditApproximation.bitWordValue stop) (OAI.EditApproximation.bitWordValue lower) +
    indices.length + OAI.EditApproximation.arithmeticMapAllocation (fun i => OAI.EditApproximation.binaryNaturalMulAllocation g i) indices

def balancedCutAllocation (lo width M i : ℕ) : ℕ :=
  let product := (OAI.EditApproximation.binaryNaturalMulWithWork i width).1
  let quotient := (OAI.EditApproximation.binaryNaturalDivModWithWork (OAI.EditApproximation.bitWordValue product) M).1
  OAI.EditApproximation.binaryNaturalMulAllocation i width + OAI.EditApproximation.binaryNaturalDivAllocation (OAI.EditApproximation.bitWordValue product) M +
    OAI.EditApproximation.binaryNaturalAddAllocation lo (OAI.EditApproximation.bitWordValue quotient)

def seedGridSpacingAllocation (b P : ℕ) : ℕ :=
  OAI.EditApproximation.binaryNaturalDivAllocation b P + OAI.EditApproximation.naturalWordLEAllocation (OAI.EditApproximation.binaryNaturalDivModWithWork b P).1 [true] + 1

def queryCellValidAllocation (n exponent : ℕ) (cell : ℕ × ℕ) : ℕ :=
  let cap := (OAI.EditApproximation.binaryNaturalMulWithWork n (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.powerTwoWord exponent))).1
  OAI.EditApproximation.binaryNaturalMulAllocation n (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.powerTwoWord exponent)) +
    OAI.EditApproximation.naturalWordLEAllocation cell.1.bits cap + OAI.EditApproximation.naturalWordLEAllocation cell.2.bits cap + exponent + 1

def queryPairAllocation (a b : ℕ) : ℕ :=
  a.bits.length + b.bits.length +
    if (OAI.EditApproximation.binaryNaturalCompareWithWork a b).1 = .lt then
      OAI.EditApproximation.binaryNaturalMulAllocation b b + OAI.EditApproximation.binaryNaturalAddAllocation (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalMulWithWork b b).1) a
    else
      OAI.EditApproximation.binaryNaturalMulAllocation a a + OAI.EditApproximation.binaryNaturalAddAllocation (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalMulWithWork a a).1) a +
        OAI.EditApproximation.binaryNaturalAddAllocation
          (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalMulWithWork a a).1) a).1) b

def binaryGridRoundAllocation (spacing position : ℕ) : ℕ :=
  OAI.EditApproximation.binaryNaturalDivAllocation position spacing +
    OAI.EditApproximation.bitMulAllocation spacing.bits (OAI.EditApproximation.binaryNaturalDivModWithWork position spacing).1

def wordSortAllocation : List (List Bool) → ℕ
  | [] => 0
  | a :: rest => wordSortAllocation rest +
    OAI.EditApproximation.wordInsertAllocation a (OAI.EditApproximation.wordSortWithWork rest).1 + 0

def reduceOnlineIntegerAllocation (K integer : ℕ) : ℕ :=
  OAI.EditApproximation.triangularMassAllocation K +
    OAI.EditApproximation.bitDivModAllocation (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.triangularMassWithWork K).1).bits integer.bits + Nat.size integer

def coarsePreparedInputStorage (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi : ℕ) : ℕ :=
  match (OAI.EditApproximation.coarsePreparedSlicesWithWork source target sourceLo sourceHi targetLo targetHi).1 with
  | none => 1
  | some (x, y) => 1 + OAI.EditApproximation.storedNaturalBits x + OAI.EditApproximation.storedNaturalBits y

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset

def optimizerTriangularMass (K : ℕ) : ℕ := ∑ j ∈ range K, (j + 1)

def rationalLogApproximation (r : ℚ) (K : ℕ) : ℚ :=
  2 * ∑ k ∈ range K, (((r - 1) / (r + 1)) ^ (2 * k + 1) / (2 * k + 1))

def rationalLinearizationMaximizer {ι : Type u_1} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (gradient : ι → ℚ) : ι → ℚ :=
  (vertices.argmax fun p => ∑ i ∈ coordinates, gradient i * p i).getD (fun _ => 0)

def bandCoordinates {β : Type u_1} {σ : Type u_2} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) : Finset (β × σ) :=
  band.biUnion fun action => univ.image fun child => (child, action child)

def actionVector {β : Type u_1} {σ : Type u_2} [Fintype β] [DecidableEq σ]
    (mass : β → ℚ) (action : β → σ) (coordinate : β × σ) : ℚ :=
  if coordinate.2 = action coordinate.1 then mass coordinate.1 / (∑ child, mass child) else 0

def rationalOptimisticHistory {ι : Type u_1} (κ : ℚ)
    (gain decrement : ℕ → ι → ℚ) (t : ℕ) (i : ι) : ℚ :=
  ∑ j ∈ range t, (gain j i + (1 - 2 * κ) * decrement j i)

def rejectionBitCount (N : ℕ) : ℕ := Nat.clog 2 N

def vectorMapWithWork {α : Type u_1} (d : ℕ) (f : Fin d → α × ℕ) : Vector α d × ℕ :=
  let cells := Vector.ofFn f
  (cells.map Prod.fst, (cells.map Prod.snd).toList.sum + 6 * d)

def TreeLayer (M : ℕ) : ℕ → Type
  | 0 => PUnit
  | d + 1 => TreeLayer M d × Fin M

def intervalTreeDepth (M nx : ℕ) : ℕ := Nat.clog M (max 1 nx)

def rationalMaximum (fallback : ℚ) : List ℚ → ℚ
  | [] => fallback
  | value :: rest => max value (rationalMaximum fallback rest)

def rationalDyadicCeiling (value : ℚ) : ℚ := (2 : ℚ) ^ Int.clog 2 value

def listedBandCoordinates {M : ℕ} {σ : Type u_1} [DecidableEq σ]
    (band : List (Fin M → σ)) : List (Fin M × σ) :=
  (band.flatMap fun action => List.ofFn fun child => (child, action child)).dedup

def childGain {β : Type u_1} {σ : Type u_2} (mass : β → ℚ) (table : ℕ → β × σ → ℚ)
    (t : ℕ) (i : β × σ) : ℚ := -table t i / mass i.1

def childDecrement {β : Type u_1} {σ : Type u_2} (mass : β → ℚ) (table : ℕ → β × σ → ℚ)
    (t : ℕ) (i : β × σ) : ℚ := (table t i - table (t + 1) i) / mass i.1

def naturalEqualWithWork (a b : ℕ) : Bool × ℕ :=
  let result := OAI.EditApproximation.binaryNaturalCompareWithWork a b
  (decide (result.1 = .eq), result.2 + 1)

def translatedEndpointWithWork (reference root endpoint : ℕ) : ℕ × ℕ :=
  let difference := OAI.EditApproximation.binaryNaturalSubtractWithWork endpoint root
  let result := OAI.EditApproximation.binaryNaturalAddWithWork reference (OAI.EditApproximation.bitWordValue difference.1)
  (OAI.EditApproximation.bitWordValue result.1, difference.2 + result.2 + 2)

def rationalOnlineMinimum : List ℚ → Option ℚ
  | [] => none
  | first :: rest => some (OAI.EditApproximation.rationalMinimum first rest)

def dyadicQueryWindow (N : ℕ) (w a F : ℚ) : List ℕ :=
  (OAI.EditApproximation.dyadicScales N).filter fun (b : ℕ) => decide (w / (16 * F) ≤ b ∧ (b : ℚ) ≤ 8 * a * w)

def actionCurrentInputCover {Parent : Type u_1} {Child : Type u_2} [DecidableEq Child] {M : ℕ}
    (actions : List (OAI.EditApproximation.RationalBellmanAction Parent Child M)) : Finset Child :=
  (List.finRange actions.length).toFinset.biUnion fun index =>
    Finset.univ.image (actions.get index).childState

def boundedOnlineInteger (n : ℕ) (hn : 0 < n) (integer : ℕ) : Fin n :=
  ⟨integer % n, Nat.mod_lt _ hn⟩

def orderedInputs {ι : Type u_1} [DecidableEq ι] (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (inputs : Finset ι) : List ι :=
  let _ : LinearOrder ι := LinearOrder.lift' encode hinjective
  inputs.sort (· ≤ ·)

def CoarseThresholdDraws (B : ℕ) : ℕ → Type
  | 0 => PUnit
  | D + 1 => (Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)

def coarseThresholdContribution (threshold scale value : ℚ) : ℚ :=
  if threshold ≤ value then max value scale else 0

def coarseChildThreshold (B : ℕ) (Q allowance : ℚ) (draw : Fin B) : ℚ :=
  allowance * (draw.val + 1 : ℕ) / ((B : ℚ) * Q)

def coarseCommonDenominator (allowanceDen q L B D : ℕ) : ℕ :=
  allowanceDen * q * (L * B * q) ^ D

def rationalSmoothedGradient {ι : Type u_1} (G : ℕ) (linear p : ι → ℚ) (i : ι) : ℚ :=
  -OAI.EditApproximation.rationalLogApproximation (p i + 1 / (G : ℚ) ^ 50) (G ^ 60) - 1 + linear i

def rationalOnlineLinear {ι : Type u_1} (η κ : ℚ)
    (gain decrement : ℕ → ι → ℚ) (t : ℕ) (i : ι) : ℚ :=
  η * (OAI.EditApproximation.rationalOptimisticHistory κ gain decrement t i + gain t i)

def triangularChoice : (K : ℕ) → Fin (OAI.EditApproximation.optimizerTriangularMass K) → Fin K
  | 0, integer => Fin.elim0 integer
  | K + 1, integer =>
    if h : integer.val < OAI.EditApproximation.optimizerTriangularMass K then
      (triangularChoice K ⟨integer.val, h⟩).castSucc
    else ⟨K, by omega⟩

instance treeLayerFintype (M : ℕ) : (d : ℕ) → Fintype (OAI.EditApproximation.TreeLayer M d)
  | 0 => inferInstanceAs (Fintype PUnit)
  | d + 1 =>
    letI := treeLayerFintype M d
    inferInstanceAs (Fintype (OAI.EditApproximation.TreeLayer M d × Fin M))

abbrev PhysicalNode (M J : ℕ) := Σ d : Fin (J + 1), OAI.EditApproximation.TreeLayer M d.val

def finiteRationalOptimizer {ι : Type u_1} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G : ℕ) : ℕ → ι → ℚ
  | 0 => vertices.headD (fun _ => 0)
  | j + 1 =>
    let p := finiteRationalOptimizer coordinates vertices linear G j
    let selected := OAI.EditApproximation.rationalLinearizationMaximizer coordinates vertices
      (OAI.EditApproximation.rationalSmoothedGradient G linear p)
    fun i => (1 - 2 / ((j : ℚ) + 2)) * p i + (2 / ((j : ℚ) + 2)) * selected i

instance physicalNodeFintype (M J : ℕ) : Fintype (OAI.EditApproximation.PhysicalNode M J) := inferInstance

abbrev PhysicalInternalNode (M J : ℕ) := {node : OAI.EditApproximation.PhysicalNode M J // node.1.val < J}

def finiteOptimizerAction {β : Type u_1} {σ : Type u_2} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (linear : β × σ → ℚ) (G j : ℕ) : β → σ :=
  let coordinates := OAI.EditApproximation.bandCoordinates band.toFinset
  let vertices := band.map (OAI.EditApproximation.actionVector mass)
  let gradient := OAI.EditApproximation.rationalSmoothedGradient G linear (OAI.EditApproximation.finiteRationalOptimizer coordinates vertices linear G j)
  (band.argmax fun action => ∑ coordinate ∈ coordinates,
    gradient coordinate * OAI.EditApproximation.actionVector mass action coordinate).getD (band.head hband)

def finiteOptimizerActionDraw {β : Type u_1} {σ : Type u_2} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (linear : β × σ → ℚ) (G K : ℕ) (integer : Fin (OAI.EditApproximation.optimizerTriangularMass K)) : β → σ :=
  OAI.EditApproximation.finiteOptimizerAction band hband mass linear G (OAI.EditApproximation.triangularChoice K integer).val

end OAI.EditApproximation

end



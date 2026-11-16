-- Prove2me | Definitions.Def_EditApproxScheme_03
-- name    : EditApproxScheme_03
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:31:30.111348+00:00
-- url     : https://prove2.me/theorems/93243c11-81d7-450c-bae6-24b90ddff43d
-- title:
--   Edit-distance approximation scheme, part 3 of 20: normalization of binary fractions
-- statement:
--   This is **part 3 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains canonicalization of binary fractions, inverse powers of two, natural floors, conversion to a fixed denominator, refinement decrements, tree-layer codes, scheduled seed words and factors, and the dispatch of physical scales to indices. It also proves 7 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L1374-L1807 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 3 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_02

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

def width (a : OAI.EditApproximation.BinaryFraction) : ℕ := max a.numerator.bits.length a.denominator.length

def denominatorInteger (a : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.SignedBinary := ⟨false, a.denominator⟩

def zero : OAI.EditApproximation.BinaryFraction := ⟨⟨false, []⟩, [true], by decide⟩

theorem _root_.OAI.EditApproximation.Lemmas.trimBitWordWithWork_value (bits : List.{0} Bool) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.trimBitWordWithWork bits).1 = OAI.EditApproximation.bitWordValue bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [OAI.EditApproximation.trimBitWordWithWork]
    split_ifs with h
    · have ht : OAI.EditApproximation.bitWordValue bits = 0 := by rw [← ih, h.1]; rfl
      simp [h.2, OAI.EditApproximation.bitWordValue, ht]
    · (simp only [OAI.EditApproximation.bitWordValue, ih])

def canonicalizeWithWork (a : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ := by
  exact
    let numerator := OAI.EditApproximation.trimBitWordWithWork a.numerator.bits
    let denominator := OAI.EditApproximation.trimBitWordWithWork a.denominator
    (⟨⟨a.numerator.negative, numerator.1⟩, denominator.1, by
        rw [OAI.EditApproximation.Lemmas.trimBitWordWithWork_value]
        exact a.denominator_pos⟩, numerator.2 + denominator.2 + 2)

theorem _root_.OAI.EditApproximation.Lemmas.powerTwoWord_value (n : ℕ) : OAI.EditApproximation.bitWordValue (OAI.EditApproximation.powerTwoWord n) = 2 ^ n := by
  induction n with
  | zero => (simp [OAI.EditApproximation.powerTwoWord, OAI.EditApproximation.bitWordValue])
  | succ n ih =>
    (simp only [OAI.EditApproximation.powerTwoWord, List.replicate_succ, List.cons_append, OAI.EditApproximation.bitWordValue,
      Bool.toNat_false, zero_add] at *)
    rw [ih, pow_succ]
    omega

def inversePowerTwo (n : ℕ) : OAI.EditApproximation.BinaryFraction := by
  exact
    ⟨⟨false, [true]⟩, OAI.EditApproximation.powerTwoWord n, by rw [OAI.EditApproximation.Lemmas.powerTwoWord_value]; positivity⟩

def doubleFraction (a : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction :=
  ⟨⟨a.numerator.negative, false :: a.numerator.bits⟩, a.denominator, a.denominator_pos⟩

def absolute (a : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction :=
  ⟨⟨false, a.numerator.bits⟩, a.denominator, a.denominator_pos⟩

def naturalCeilingWithWork (a : OAI.EditApproximation.BinaryFraction) : List Bool × ℕ :=
  if a.numerator.negative then ([], 1)
  else
    let result := OAI.EditApproximation.bitCeilDivWithWork a.denominator a.numerator.bits
    (result.1, result.2 + 1)

def ofNaturalWord (bits : List Bool) : OAI.EditApproximation.BinaryFraction :=
  ⟨⟨false, bits⟩, [true], by decide⟩

def naturalFloorWithWork (a : OAI.EditApproximation.BinaryFraction) : List Bool × ℕ :=
  if a.numerator.negative then ([], 1) else
    let quotient := OAI.EditApproximation.bitDivModWithWork a.denominator a.numerator.bits
    (quotient.1, quotient.2.2 + 1)

def queryDataReadBudget (M n : ℕ) {κ : Type u_1} (keys : List κ) : ℕ :=
  1 + keys.length * (24 * max (Nat.size M) (Nat.size n) + 9)

theorem _root_.OAI.EditApproximation.Lemmas.bitAdder_value (a : Bool) (b : Bool) (carry : Bool) :
    (OAI.EditApproximation.bitSum a b carry).toNat + 2 * (OAI.EditApproximation.bitCarry a b carry).toNat =
      a.toNat + b.toNat + carry.toNat := by
  cases a <;> cases b <;> cases carry <;> decide

theorem _root_.OAI.EditApproximation.Lemmas.bitAddWithWork_value (left : List.{0} Bool) (right : List.{0} Bool) (carry : Bool) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitAddWithWork left right carry).1 =
      OAI.EditApproximation.bitWordValue left + OAI.EditApproximation.bitWordValue right + carry.toNat := by
  induction left generalizing right carry with
  | nil =>
    simp only [OAI.EditApproximation.bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [OAI.EditApproximation.bitAddNilLeftWithWork, OAI.EditApproximation.bitWordValue]
    | cons b bs ih =>
      simp only [OAI.EditApproximation.bitAddNilLeftWithWork, OAI.EditApproximation.bitWordValue, ih]
      have h := OAI.EditApproximation.Lemmas.bitAdder_value false b carry
      simp only [Bool.toNat_false] at h
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      simp only [OAI.EditApproximation.bitAddWithWork, OAI.EditApproximation.bitWordValue, ih]
      have h := OAI.EditApproximation.Lemmas.bitAdder_value a false carry
      simp only [Bool.toNat_false] at h
      omega
    | cons b bs =>
      simp only [OAI.EditApproximation.bitAddWithWork, OAI.EditApproximation.bitWordValue, ih]
      have h := OAI.EditApproximation.Lemmas.bitAdder_value a b carry
      omega

theorem _root_.OAI.EditApproximation.Lemmas.bitMulWithWork_value (left : List.{0} Bool) (right : List.{0} Bool) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitMulWithWork left right).1 = OAI.EditApproximation.bitWordValue left * OAI.EditApproximation.bitWordValue right := by
  induction left with
  | nil => simp [OAI.EditApproximation.bitMulWithWork, OAI.EditApproximation.bitWordValue]
  | cons bit bits ih =>
    cases bit <;> simp [OAI.EditApproximation.bitMulWithWork, OAI.EditApproximation.bitWordValue, OAI.EditApproximation.Lemmas.bitAddWithWork_value, ih] <;> ring

theorem _root_.OAI.EditApproximation.Lemmas.bitPowerWithWork_value (base : List.{0} Bool) (n : ℕ) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitPowerWithWork base n).1 = OAI.EditApproximation.bitWordValue base ^ n := by
  induction n with
  | zero => (simp [OAI.EditApproximation.bitPowerWithWork, OAI.EditApproximation.bitWordValue])
  | succ n ih =>
    simp only [OAI.EditApproximation.bitPowerWithWork, OAI.EditApproximation.Lemmas.trimBitWordWithWork_value, OAI.EditApproximation.Lemmas.bitMulWithWork_value, ih, pow_succ]

def onlineParametersWithWork (ell : List Bool) (hell : 0 < OAI.EditApproximation.bitWordValue ell) :
    (OAI.EditApproximation.BinaryFraction × OAI.EditApproximation.BinaryFraction) × ℕ := by
  exact
    let etaPower := OAI.EditApproximation.bitPowerWithWork ell 5
    let kappaPower := OAI.EditApproximation.bitPowerWithWork ell 4
    let eta : OAI.EditApproximation.BinaryFraction := ⟨⟨false, etaPower.1⟩, [true], by decide⟩
    let kappa : OAI.EditApproximation.BinaryFraction := ⟨⟨false, [true]⟩, kappaPower.1, by
      rw [OAI.EditApproximation.Lemmas.bitPowerWithWork_value]
      exact Nat.pow_pos hell⟩
    ((eta, kappa), etaPower.2 + kappaPower.2 + 2)

def refinementDecrementWithWork (ell : List Bool) (hell : 0 < OAI.EditApproximation.bitWordValue ell) : OAI.EditApproximation.BinaryFraction × ℕ := by
  exact
    let denominator := OAI.EditApproximation.bitPowerWithWork ell 10
    (⟨⟨false, [true]⟩, denominator.1, by
      rw [OAI.EditApproximation.Lemmas.bitPowerWithWork_value]
      exact Nat.pow_pos hell⟩, denominator.2 + 1)

abbrev CoarseBinaryArray := Option (List OAI.EditApproximation.BinaryFraction)

def coarseRootDenominator (B q L d : ℕ) : List Bool × ℕ :=
  OAI.EditApproximation.coarseDenominatorWithWork (1 : ℕ).bits q.bits L.bits B.bits d

def naturalListEqualWithWork : List ℕ → List ℕ → Bool × ℕ
  | [], [] => (true, 1)
  | a :: left, b :: right =>
    let test := OAI.EditApproximation.naturalEqualWithWork a b
    if test.1 then
      let tail := naturalListEqualWithWork left right
      (tail.1, test.2 + tail.2 + 2)
    else (false, test.2 + 2)
  | _, _ => (false, 1)

def canonicalizeAllocation (a : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.trimBitWordAllocation a.numerator.bits + OAI.EditApproximation.trimBitWordAllocation a.denominator

def invAllocation (a : OAI.EditApproximation.BinaryFraction) : ℕ :=
  if (OAI.EditApproximation.bitCompareWithWork a.numerator.bits []).1 = .eq then 1 else 0

def naturalCeilingAllocation (a : OAI.EditApproximation.BinaryFraction) : ℕ :=
  if a.numerator.negative then 0 else OAI.EditApproximation.bitCeilDivAllocation a.denominator a.numerator.bits

def gatheredLookupAllocation {κ : Type u_1} (equal : κ → κ → Bool × ℕ)
    (allocation : κ → κ → ℕ) : List κ → List OAI.EditApproximation.BinaryFraction → κ → ℕ
  | key :: keys, _value :: values, query =>
    allocation query key + if (equal query key).1 then 0
      else gatheredLookupAllocation equal allocation keys values query
  | _, _, _ => 0

def naturalFloorAllocation (a : OAI.EditApproximation.BinaryFraction) : ℕ :=
  if a.numerator.negative then 0 else OAI.EditApproximation.bitDivModAllocation a.denominator a.numerator.bits

def signedPowerTwoAllocation (e : ℤ) : ℕ :=
  if 0 ≤ e then e.toNat + 2 else (-e).toNat + 2

theorem _root_.OAI.EditApproximation.Lemmas.bitCompareWithWork_eq (left : List.{0} Bool) (right : List.{0} Bool) :
    (OAI.EditApproximation.bitCompareWithWork left right).1 = .eq ↔ OAI.EditApproximation.bitWordValue left = OAI.EditApproximation.bitWordValue right := by
  have h := OAI.EditApproximation.Lemmas.bitCompareWithWork_matches left right
  rcases h with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ <;> rw [h] <;> simp_all
  all_goals omega

def invWithWork (a : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ := by
  exact
    let comparison := OAI.EditApproximation.bitCompareWithWork a.numerator.bits []
    if h : comparison.1 = .eq then (OAI.EditApproximation.BinaryFraction.zero, comparison.2 + 2) else
      (⟨⟨a.numerator.negative, a.denominator⟩, a.numerator.bits, by
        have hnonzero : OAI.EditApproximation.bitWordValue a.numerator.bits ≠ 0 := by
          intro hzero
          exact h ((OAI.EditApproximation.Lemmas.bitCompareWithWork_eq a.numerator.bits []).2 hzero)
        omega⟩, comparison.2 + 2)

def signedPowerTwoWithWork (e : ℤ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  if 0 ≤ e then
    (⟨⟨false, OAI.EditApproximation.powerTwoWord e.toNat⟩, [true], by decide⟩, e.toNat + 3)
  else (OAI.EditApproximation.BinaryFraction.inversePowerTwo (-e).toNat, (-e).toNat + 3)

def fixedDenominatorWithWork (a : OAI.EditApproximation.BinaryFraction) (denominator : List Bool)
    (hden : 0 < OAI.EditApproximation.bitWordValue denominator) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let product := OAI.EditApproximation.bitMulWithWork a.numerator.bits denominator
  let quotient := OAI.EditApproximation.bitDivModWithWork a.denominator product.1
  let raw : OAI.EditApproximation.BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  let answer := OAI.EditApproximation.BinaryFraction.canonicalizeWithWork raw
  (answer.1, product.2 + quotient.2.2 + answer.2 + 4)

def finalAnswerWithWork (N : ℕ) (a : OAI.EditApproximation.BinaryFraction) : List Bool × ℕ :=
  let floor := OAI.EditApproximation.BinaryFraction.naturalFloorWithWork a
  let clamped := OAI.EditApproximation.wordMinWithWork N.bits floor.1
  (clamped.1, floor.2 + clamped.2 + Nat.size N + 2)

def coarseGridNatWithWork (denominator : List Bool)
    (hden : 0 < OAI.EditApproximation.bitWordValue denominator) (n : ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let product := OAI.EditApproximation.bitMulWithWork n.bits denominator
  let raw : OAI.EditApproximation.BinaryFraction := ⟨⟨false, product.1⟩, denominator, hden⟩
  let answer := OAI.EditApproximation.BinaryFraction.canonicalizeWithWork raw
  (answer.1, product.2 + answer.2 + 3)

def coarseBinaryMapWithWork (f : OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BinaryFraction × ℕ) :
    OAI.EditApproximation.BinaryFraction.CoarseBinaryArray → OAI.EditApproximation.BinaryFraction.CoarseBinaryArray × ℕ
  | none => (none, 0)
  | some values =>
    let result := OAI.EditApproximation.arithmeticMapWithWork f values
    (some result.1, result.2)

def fixedDenominatorAllocation (a : OAI.EditApproximation.BinaryFraction) (denominator : List Bool)
    (hden : 0 < OAI.EditApproximation.bitWordValue denominator) : ℕ :=
  let product := OAI.EditApproximation.bitMulWithWork a.numerator.bits denominator
  let quotient := OAI.EditApproximation.bitDivModWithWork a.denominator product.1
  let raw : OAI.EditApproximation.BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  OAI.EditApproximation.bitMulAllocation a.numerator.bits denominator + OAI.EditApproximation.bitDivModAllocation a.denominator product.1 +
    OAI.EditApproximation.BinaryFraction.canonicalizeAllocation raw

def finalAnswerAllocation (N : ℕ) (a : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.naturalFloorAllocation a + OAI.EditApproximation.naturalWordLEAllocation N.bits (OAI.EditApproximation.BinaryFraction.naturalFloorWithWork a).1 + Nat.size N + 1

def powerDenominatorWithWork (a : OAI.EditApproximation.BinaryFraction) (base : List Bool)
    (hbase : 0 < OAI.EditApproximation.bitWordValue base) (n : ℕ) : OAI.EditApproximation.BinaryFraction × ℕ := by
  exact
    let denominator := OAI.EditApproximation.bitPowerWithWork base n
    let answer := OAI.EditApproximation.BinaryFraction.fixedDenominatorWithWork a denominator.1 (by
      rw [OAI.EditApproximation.Lemmas.bitPowerWithWork_value]
      exact Nat.pow_pos hbase)
    (answer.1, denominator.2 + answer.2 + 1)

def powerDenominatorAllocation (a : OAI.EditApproximation.BinaryFraction) (base : List Bool)
    (hbase : 0 < OAI.EditApproximation.bitWordValue base) (n : ℕ) : ℕ := by
  exact
    OAI.EditApproximation.bitPowerAllocation base n + OAI.EditApproximation.BinaryFraction.fixedDenominatorAllocation a (OAI.EditApproximation.bitPowerWithWork base n).1
      (by rw [OAI.EditApproximation.Lemmas.bitPowerWithWork_value]; exact Nat.pow_pos hbase)

def finishCachedWithWork (raw : OAI.EditApproximation.BinaryFraction × ℕ) (base : List Bool)
    (hbase : 0 < OAI.EditApproximation.bitWordValue base) (remaining : ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let result := OAI.EditApproximation.BinaryFraction.powerDenominatorWithWork raw.1 base hbase remaining
  (result.1, raw.2 + result.2 + 1)

def finishCachedAllocation (raw : OAI.EditApproximation.BinaryFraction × ℕ) (allocation : ℕ)
    (base : List Bool) (hbase : 0 < OAI.EditApproximation.bitWordValue base) (remaining : ℕ) : ℕ :=
  allocation + OAI.EditApproximation.BinaryFraction.powerDenominatorAllocation raw.1 base hbase remaining

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def physicalChild {M J : ℕ} (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : node.1.val < J)
    (i : Fin M) : OAI.EditApproximation.PhysicalNode M J :=
  ⟨⟨node.1.val + 1, by omega⟩, (node.2, i)⟩

instance treeLayerDecidableEq (M : ℕ) : (d : ℕ) → DecidableEq (OAI.EditApproximation.TreeLayer M d)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | d + 1 =>
    letI := treeLayerDecidableEq M d
    inferInstanceAs (DecidableEq (OAI.EditApproximation.TreeLayer M d × Fin M))

def treeLayerCode (M : ℕ) : (d : ℕ) → OAI.EditApproximation.TreeLayer M d → ℕ
  | 0, _ => 0
  | d + 1, path => path.2.val + M * treeLayerCode M d path.1

def localOnlineMassBound (M P H : ℕ) : ℕ :=
  OAI.EditApproximation.optimizerTriangularMass ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80)

def treeLayerCodeWithWork (M : ℕ) : (d : ℕ) → OAI.EditApproximation.TreeLayer M d → ℕ × ℕ
  | 0, _ => (0, 1)
  | d + 1, path => let previous := treeLayerCodeWithWork M d path.1
      (path.2.val + M * previous.1, previous.2 + 3)

def queryNaturalIndexWithWork (a : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 1)
  | b :: rest =>
    let test := OAI.EditApproximation.naturalEqualWithWork a b
    if test.1 then (0, test.2 + 1)
    else
      let tail := queryNaturalIndexWithWork a rest
      (tail.1 + 1, test.2 + tail.2 + 2)

def scheduledSeedWordWithWork (N pass : ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork
    ((OAI.EditApproximation.dyadicSeedExponent (OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.computedSeedInitialExponent N) pass : ℕ) : ℤ)

def coarseLetterMatchWithWork : Option (Option ℕ) → Option ℕ → Bool × ℕ
  | none, _ => (false, 1)
  | some none, none => (true, 1)
  | some (some a), some b => OAI.EditApproximation.naturalEqualWithWork a b
  | _, _ => (false, 1)

def queryNaturalIndexAllocation (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: rest => OAI.EditApproximation.naturalEqualAllocation a b +
      if (OAI.EditApproximation.naturalEqualWithWork a b).1 then 1 else queryNaturalIndexAllocation a rest + 1

def physicalNodeCode {M J : ℕ} (node : OAI.EditApproximation.PhysicalNode M J) : ℕ :=
  OAI.EditApproximation.treeLayerCode M node.1.val node.2 + M ^ J * node.1.val

def queryScaleDispatchWithWork (N b : ℕ) : ℕ × ℕ :=
  let scales := OAI.EditApproximation.dyadicScalesWithWork N
  let index := OAI.EditApproximation.queryNaturalIndexWithWork b scales.1
  (index.1, scales.2 + index.2 + scales.1.length + 2)

def queryScaleDispatchAllocation (N b : ℕ) : ℕ :=
  OAI.EditApproximation.dyadicScalesAllocation N + OAI.EditApproximation.queryNaturalIndexAllocation b (OAI.EditApproximation.dyadicScalesWithWork N).1 +
    (OAI.EditApproximation.dyadicScalesWithWork N).1.length

def queryScalePresentWithWork (N b : ℕ) : Bool × ℕ :=
  let found := OAI.EditApproximation.queryScaleDispatchWithWork N b
  let test := OAI.EditApproximation.binaryNaturalCompareWithWork found.1 (max 1 N.bits.length)
  (decide (test.1 = .lt), found.2 + test.2 + 2)

def queryScalePresentAllocation (N b : ℕ) : ℕ :=
  OAI.EditApproximation.queryScaleDispatchAllocation N b + (OAI.EditApproximation.queryScaleDispatchWithWork N b).1.bits.length + (max 1 N.bits.length).bits.length

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

def physicalScaleIndex (N b : ℕ) (hb : b ∈ OAI.EditApproximation.dyadicScales N) :
    Fin (OAI.EditApproximation.dyadicScales N).length :=
  ⟨(OAI.EditApproximation.dyadicScales N).idxOf b, List.idxOf_lt_length_of_mem hb⟩

abbrev PositiveDrawRange (B : ℕ) := {n : Fin (B + 1) // 0 < n.val}

abbrev PhysicalLocalGroupKey (M J N n exponent : ℕ) :=
  OAI.EditApproximation.PhysicalInternalNode M J × Fin (OAI.EditApproximation.dyadicScales N).length ×
    Fin (n * 2 ^ exponent + 1) × Fin (n * 2 ^ exponent + 1)

noncomputable def rejectionSuccessParameter (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) : unitInterval :=
  ⟨(N : ℝ) / R, div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one₀ (by exact_mod_cast hN.trans_le hNR : (0 : ℝ) < R)).mpr (by exact_mod_cast hNR)⟩

def scheduledSeedFactor (N pass : ℕ) : ℚ :=
  (2 : ℚ) ^ OAI.EditApproximation.dyadicSeedExponent (OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.computedSeedInitialExponent N) pass

def scheduledSeedMultiplier (N pass : ℕ) : ℕ :=
  2 ^ (OAI.EditApproximation.dyadicSeedExponent (OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.computedSeedInitialExponent N) pass - OAI.EditApproximation.smallLogExponent N)

instance computedBranching_neZero (N : ℕ) : NeZero (OAI.EditApproximation.integerParameters N).M :=
  ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩

instance computedCoarseBranching_neZero (N : ℕ) : NeZero (OAI.EditApproximation.integerParameters N).B :=
  ⟨pow_ne_zero _ (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))⟩

instance computedSourceTime_neZero (N : ℕ) : NeZero (OAI.EditApproximation.inputHeight N ^ 2) :=
  ⟨pow_ne_zero _ (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))⟩

abbrev CommonRangeKey (ι : Type u_1) (B : ℕ) := ι × OAI.EditApproximation.PositiveDrawRange B

def positiveDrawRangeOfLE (B n : ℕ) (hn : 0 < n) (hB : n ≤ B) : OAI.EditApproximation.PositiveDrawRange B :=
  ⟨⟨n, Nat.lt_succ_of_le hB⟩, hn⟩

instance positiveDrawRange_nezero {B : ℕ} (n : OAI.EditApproximation.PositiveDrawRange B) : NeZero n.val.val :=
  ⟨Nat.ne_of_gt n.property⟩

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.SignedBinary

def value (a : OAI.EditApproximation.SignedBinary) : ℤ := OAI.EditApproximation.signedMagnitude a.negative (OAI.EditApproximation.bitWordValue a.bits)

def ofInt (a : ℤ) : OAI.EditApproximation.SignedBinary := ⟨decide (a < 0), a.natAbs.bits⟩

def neg (a : OAI.EditApproximation.SignedBinary) : OAI.EditApproximation.SignedBinary := ⟨!a.negative, a.bits⟩

def addWithWork (a b : OAI.EditApproximation.SignedBinary) : OAI.EditApproximation.SignedBinary × ℕ :=
  if a.negative = b.negative then
    let total := OAI.EditApproximation.bitAddWithWork a.bits b.bits false
    (⟨a.negative, total.1⟩, total.2 + 4)
  else
    let comparison := OAI.EditApproximation.bitCompareWithWork a.bits b.bits
    match comparison.1 with
    | .eq => (⟨false, []⟩, comparison.2 + 4)
    | .lt =>
      let difference := OAI.EditApproximation.bitSubtractWithWork b.bits a.bits false
      (⟨b.negative, difference.1⟩, comparison.2 + difference.2.2 + 4)
    | .gt =>
      let difference := OAI.EditApproximation.bitSubtractWithWork a.bits b.bits false
      (⟨a.negative, difference.1⟩, comparison.2 + difference.2.2 + 4)

def mulWithWork (a b : OAI.EditApproximation.SignedBinary) : OAI.EditApproximation.SignedBinary × ℕ :=
  let product := OAI.EditApproximation.bitMulWithWork a.bits b.bits
  (⟨xor a.negative b.negative, product.1⟩, product.2 + 4)

def nonzeroWithWork (bits : List Bool) : Bool × ℕ :=
  let comparison := OAI.EditApproximation.bitCompareWithWork bits []
  (if comparison.1 = .eq then false else true, comparison.2 + 1)

def addAllocation (a b : OAI.EditApproximation.SignedBinary) : ℕ :=
  if a.negative = b.negative then OAI.EditApproximation.bitAddAllocation a.bits b.bits false
  else match (OAI.EditApproximation.bitCompareWithWork a.bits b.bits).1 with
    | .eq => 0
    | .lt => OAI.EditApproximation.bitSubtractAllocation b.bits a.bits false
    | .gt => OAI.EditApproximation.bitSubtractAllocation a.bits b.bits false

def mulAllocation (a b : OAI.EditApproximation.SignedBinary) : ℕ := OAI.EditApproximation.bitMulAllocation a.bits b.bits

def ltWithWork (a b : OAI.EditApproximation.SignedBinary) : Bool × ℕ :=
  if a.negative then
    if b.negative then
      let comparison := OAI.EditApproximation.bitCompareWithWork b.bits a.bits
      (comparison.1 == .lt, comparison.2 + 2)
    else
      let left := OAI.EditApproximation.SignedBinary.nonzeroWithWork a.bits
      let right := OAI.EditApproximation.SignedBinary.nonzeroWithWork b.bits
      (left.1 || right.1, left.2 + right.2 + 4)
  else
    if b.negative then (false, 2)
    else
      let comparison := OAI.EditApproximation.bitCompareWithWork a.bits b.bits
      (comparison.1 == .lt, comparison.2 + 2)

end OAI.EditApproximation.SignedBinary

end



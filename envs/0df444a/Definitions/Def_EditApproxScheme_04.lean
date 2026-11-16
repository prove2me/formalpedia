-- Prove2me | Definitions.Def_EditApproxScheme_04
-- name    : EditApproxScheme_04
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:32:53.554166+00:00
-- url     : https://prove2.me/theorems/9ebc7ca8-2ca6-43df-be48-85b414c33898
-- title:
--   Edit-distance approximation scheme, part 4 of 20: arithmetic on binary fractions and coarse grids
-- statement:
--   This is **part 4 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains maxima, products and powers of binary fractions, shifted reads and pointwise minima of coarse grids, group terms, gain and decrement reads, refinement scale guards, interval distances, partial sums of the logarithm series, and gradient cells.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L1809-L2565 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 4 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_03

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

def value (a : OAI.EditApproximation.BinaryFraction) : ℚ := (a.numerator.value : ℚ) / OAI.EditApproximation.bitWordValue a.denominator

def representation (a : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.UnreducedRational :=
  ⟨a.numerator.value, OAI.EditApproximation.bitWordValue a.denominator, a.denominator_pos⟩

def addWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ := by
  exact
    let first := a.numerator.mulWithWork b.denominatorInteger
    let second := b.numerator.mulWithWork a.denominatorInteger
    let numerator := first.1.addWithWork second.1
    let denominator := OAI.EditApproximation.bitMulWithWork a.denominator b.denominator
    (⟨numerator.1, denominator.1, by
        change 0 < OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitMulWithWork a.denominator b.denominator).1
        rw [OAI.EditApproximation.Lemmas.bitMulWithWork_value]
        exact Nat.mul_pos a.denominator_pos b.denominator_pos⟩,
      first.2 + second.2 + numerator.2 + denominator.2 + 8)

def mulWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ := by
  exact
    let numerator := a.numerator.mulWithWork b.numerator
    let denominator := OAI.EditApproximation.bitMulWithWork a.denominator b.denominator
    (⟨numerator.1, denominator.1, by
        change 0 < OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitMulWithWork a.denominator b.denominator).1
        rw [OAI.EditApproximation.Lemmas.bitMulWithWork_value]
        exact Nat.mul_pos a.denominator_pos b.denominator_pos⟩,
      numerator.2 + denominator.2 + 4)

def neg (a : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction :=
  ⟨a.numerator.neg, a.denominator, a.denominator_pos⟩

def ltWithWork (a b : OAI.EditApproximation.BinaryFraction) : Bool × ℕ :=
  let left := a.numerator.mulWithWork b.denominatorInteger
  let right := b.numerator.mulWithWork a.denominatorInteger
  let compared := left.1.ltWithWork right.1
  (compared.1, left.2 + right.2 + compared.2 + 4)

def nat (n : ℕ) : OAI.EditApproximation.BinaryFraction :=
  ⟨OAI.EditApproximation.SignedBinary.ofInt n, [true], by decide⟩

def coarseGridAddWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let total := a.numerator.addWithWork b.numerator
  let raw : OAI.EditApproximation.BinaryFraction := ⟨total.1, a.denominator, a.denominator_pos⟩
  let answer := OAI.EditApproximation.BinaryFraction.canonicalizeWithWork raw
  (answer.1, total.2 + answer.2 + 3)

def coarseReadShiftWithWork (k n : ℕ) (target : List ℕ) (letter : Option (Option ℕ))
    (start : ℕ) (shift : Fin (2 * k + 1)) : ℕ × ℕ :=
  match letter with
  | none => (0, 1)
  | some letter =>
    let position := OAI.EditApproximation.binaryNaturalAddWithWork start shift.val
    let actual := OAI.EditApproximation.coarseFramedReadWithWork k n target (OAI.EditApproximation.bitWordValue position.1)
    let matched := OAI.EditApproximation.coarseLetterMatchWithWork actual.1 letter
    (if matched.1 then 0 else 1, position.2 + actual.2 + matched.2 + 3)

def addAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ :=
  a.numerator.mulAllocation b.denominatorInteger +
  b.numerator.mulAllocation a.denominatorInteger +
  ((a.numerator.mulWithWork b.denominatorInteger).1.addAllocation
    (b.numerator.mulWithWork a.denominatorInteger).1) +
  OAI.EditApproximation.bitMulAllocation a.denominator b.denominator

def mulAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ :=
  a.numerator.mulAllocation b.numerator + OAI.EditApproximation.bitMulAllocation a.denominator b.denominator

def ltAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ :=
  a.numerator.mulAllocation b.denominatorInteger +
  b.numerator.mulAllocation a.denominatorInteger

def canonicalAddWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let raw := a.addWithWork b
  let result := OAI.EditApproximation.BinaryFraction.canonicalizeWithWork raw.1
  (result.1, raw.2 + result.2)

def canonicalMulWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let raw := a.mulWithWork b
  let result := OAI.EditApproximation.BinaryFraction.canonicalizeWithWork raw.1
  (result.1, raw.2 + result.2)

def one : OAI.EditApproximation.BinaryFraction := OAI.EditApproximation.BinaryFraction.nat 1

def dyadicScanWithWork (a candidate : OAI.EditApproximation.BinaryFraction) : ℕ → OAI.EditApproximation.BinaryFraction × ℕ
  | 0 => (candidate, 1)
  | n + 1 =>
    let comparison := candidate.ltWithWork a
    if comparison.1 then
      let next := dyadicScanWithWork a (OAI.EditApproximation.BinaryFraction.doubleFraction candidate) n
      (next.1, comparison.2 + next.2 + 2)
    else (candidate, comparison.2 + 1)

def maxWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let comparison := a.ltWithWork b
  (if comparison.1 then b else a, comparison.2 + 1)

def leWithWork (a b : OAI.EditApproximation.BinaryFraction) : Bool × ℕ :=
  let result := b.ltWithWork a
  (!result.1, result.2 + 1)

def minWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let comparison := a.ltWithWork b
  (if comparison.1 then a else b, comparison.2 + 1)

def queryScaleAt (words : List OAI.EditApproximation.BinaryFraction) (scales : List ℚ)
    (h : words.map OAI.EditApproximation.BinaryFraction.value = scales) (i : Fin scales.length) : OAI.EditApproximation.BinaryFraction :=
  words[i.val]'(by have hl := congrArg List.length h; simp only [List.length_map] at hl; omega)

def gatheredWordLookupWithWork {κ : Type u_1} (equal : κ → κ → Bool × ℕ) :
    List κ → List OAI.EditApproximation.BinaryFraction → κ → OAI.EditApproximation.BinaryFraction × ℕ
  | key :: keys, value :: values, query =>
      let test := equal query key
      if test.1 then (value, test.2 + 1)
      else
        let rest := gatheredWordLookupWithWork equal keys values query
        (rest.1, test.2 + rest.2 + 1)
  | _, _, _ => (OAI.EditApproximation.BinaryFraction.nat 0, 1)

def coarseGridZipAddWithWork : List OAI.EditApproximation.BinaryFraction → List OAI.EditApproximation.BinaryFraction → List OAI.EditApproximation.BinaryFraction × ℕ
  | a :: left, b :: right =>
    let here := OAI.EditApproximation.BinaryFraction.coarseGridAddWithWork a b
    let tail := coarseGridZipAddWithWork left right
    (here.1 :: tail.1, here.2 + tail.2 + 3)
  | _, _ => ([], 0)

def coarseBinaryRead (array : OAI.EditApproximation.BinaryFraction.CoarseBinaryArray) (i : ℕ) : OAI.EditApproximation.BinaryFraction :=
  match array with
  | none => OAI.EditApproximation.BinaryFraction.nat 0
  | some cells => cells[i]?.getD (OAI.EditApproximation.BinaryFraction.nat 0)

def canonicalAddAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ :=
  a.addAllocation b + OAI.EditApproximation.BinaryFraction.canonicalizeAllocation (a.addWithWork b).1

def canonicalMulAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ :=
  a.mulAllocation b + OAI.EditApproximation.BinaryFraction.canonicalizeAllocation (a.mulWithWork b).1

def minAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ := OAI.EditApproximation.BinaryFraction.ltAllocation a b

def maxAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ := OAI.EditApproximation.BinaryFraction.ltAllocation a b

def leAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ := OAI.EditApproximation.BinaryFraction.ltAllocation b a

def dyadicScanAllocation (a candidate : OAI.EditApproximation.BinaryFraction) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    OAI.EditApproximation.BinaryFraction.ltAllocation candidate a + if (candidate.ltWithWork a).1 then
      dyadicScanAllocation a (OAI.EditApproximation.BinaryFraction.doubleFraction candidate) n + 1 else 0

def equalAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.ltAllocation b a + OAI.EditApproximation.BinaryFraction.ltAllocation a b + 0

def subWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork a b.neg
  (result.1, result.2 + 1)

def divWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let inverse := b.invWithWork
  let result := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork a inverse.1
  (result.1, inverse.2 + result.2 + 1)

def powWithWork (a : OAI.EditApproximation.BinaryFraction) : ℕ → OAI.EditApproximation.BinaryFraction × ℕ
  | 0 => (OAI.EditApproximation.BinaryFraction.one, 1)
  | k + 1 =>
    let previous := powWithWork a k
    let result := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork previous.1 a
    (result.1, previous.2 + result.2 + 1)

def dotListWithWork {d : ℕ} (left right : Vector OAI.EditApproximation.BinaryFraction d) : List (Fin d) → OAI.EditApproximation.BinaryFraction × ℕ
  | [] => (OAI.EditApproximation.BinaryFraction.zero, 1)
  | i :: rest =>
    let tail := dotListWithWork left right rest
    let product := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (left.get i) (right.get i)
    let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork product.1 tail.1
    (result.1, tail.2 + product.2 + result.2 + 5)

def dyadicCeilingWithWork (a : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let result := OAI.EditApproximation.BinaryFraction.dyadicScanWithWork a (OAI.EditApproximation.BinaryFraction.inversePowerTwo a.width) (2 * a.width)
  (result.1, result.2 + 3 * a.width + 5)

def maximumWithWork (fallback : OAI.EditApproximation.BinaryFraction) : List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BinaryFraction × ℕ
  | [] => (fallback, 1)
  | head :: rest =>
    let tail := maximumWithWork fallback rest
    let result := OAI.EditApproximation.BinaryFraction.maxWithWork head tail.1
    (result.1, tail.2 + result.2 + 1)

def minimumWithWork (fallback : OAI.EditApproximation.BinaryFraction) : List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BinaryFraction × ℕ
  | [] => (fallback, 1)
  | head :: rest =>
    let tail := minimumWithWork fallback rest
    let result := OAI.EditApproximation.BinaryFraction.minWithWork head tail.1
    (result.1, tail.2 + result.2 + 1)

def scaledCeilingWithWork (multiplier : ℕ) (a : OAI.EditApproximation.BinaryFraction) : List Bool × ℕ :=
  let product := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat multiplier) a
  let result := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork product.1
  (result.1, product.2 + result.2 + Nat.size multiplier + 3)

def coarseContributionWithWork (threshold scale a : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let test := OAI.EditApproximation.BinaryFraction.leWithWork threshold a
  if test.1 then
    let result := OAI.EditApproximation.BinaryFraction.maxWithWork a scale
    (result.1, test.2 + result.2 + 2)
  else
    let result := OAI.EditApproximation.BinaryFraction.coarseGridNatWithWork a.denominator a.denominator_pos 0
    (result.1, test.2 + result.2 + 2)

def coarseGridScanWithWork (two previous : OAI.EditApproximation.BinaryFraction) :
    List OAI.EditApproximation.BinaryFraction → List OAI.EditApproximation.BinaryFraction × ℕ
  | [] => ([previous], 0)
  | head :: rest =>
    let added := OAI.EditApproximation.BinaryFraction.coarseGridAddWithWork previous two
    let next := OAI.EditApproximation.BinaryFraction.minWithWork head added.1
    let tail := coarseGridScanWithWork two next.1 rest
    (previous :: tail.1, added.2 + next.2 + tail.2 + 3)

def coarseGridZipMinimumWithWork : List OAI.EditApproximation.BinaryFraction → List OAI.EditApproximation.BinaryFraction → List OAI.EditApproximation.BinaryFraction × ℕ
  | a :: left, b :: right =>
    let here := OAI.EditApproximation.BinaryFraction.minWithWork a b
    let tail := coarseGridZipMinimumWithWork left right
    (here.1 :: tail.1, here.2 + tail.2 + 3)
  | _, _ => ([], 0)

def coarseBinaryAddWithWork : OAI.EditApproximation.BinaryFraction.CoarseBinaryArray → OAI.EditApproximation.BinaryFraction.CoarseBinaryArray → OAI.EditApproximation.BinaryFraction.CoarseBinaryArray × ℕ
  | none, right => (right, 0)
  | left, none => (left, 0)
  | some left, some right =>
    let result := OAI.EditApproximation.BinaryFraction.coarseGridZipAddWithWork left right
    (some result.1, result.2)

def divAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.invAllocation b + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation a b.invWithWork.1

def subAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ := OAI.EditApproximation.BinaryFraction.canonicalAddAllocation a b.neg

def optimizerUpdateCellAllocation {d : ℕ} (step complement : OAI.EditApproximation.BinaryFraction)
    (previous selected : Vector OAI.EditApproximation.BinaryFraction d) (i : Fin d) : ℕ :=
  OAI.EditApproximation.BinaryFraction.canonicalMulAllocation complement (previous.get i) + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation step (selected.get i) +
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork complement (previous.get i)).1
      (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork step (selected.get i)).1

def dyadicCeilingAllocation (a : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.dyadicScanAllocation a (OAI.EditApproximation.BinaryFraction.inversePowerTwo a.width) (2 * a.width) + a.width + 2

def roundedSpacingAllocation (theta envelope : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let product := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork theta envelope).1
  OAI.EditApproximation.BinaryFraction.canonicalMulAllocation theta envelope + OAI.EditApproximation.BinaryFraction.maxAllocation OAI.EditApproximation.BinaryFraction.one product +
    OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation (OAI.EditApproximation.BinaryFraction.maxWithWork OAI.EditApproximation.BinaryFraction.one product).1

def scaledCeilingAllocation (multiplier : ℕ) (a : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat multiplier) a +
    OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat multiplier) a).1 + Nat.size multiplier + 1

def groupTermsAllocation {M : ℕ} (h : OAI.EditApproximation.BinaryFraction) (envelope : Vector OAI.EditApproximation.BinaryFraction M)
    (indices : List (Fin M)) : ℕ :=
  OAI.EditApproximation.arithmeticMapAllocation (fun i => OAI.EditApproximation.BinaryFraction.equalAllocation (envelope.get i) h + 2) indices

def logarithmPartialWithWork (b : OAI.EditApproximation.BinaryFraction) : ℕ → OAI.EditApproximation.BinaryFraction × ℕ
  | 0 => (OAI.EditApproximation.BinaryFraction.zero, 1)
  | k + 1 =>
    let previous := logarithmPartialWithWork b k
    let power := OAI.EditApproximation.BinaryFraction.powWithWork b (2 * k + 1)
    let term := OAI.EditApproximation.BinaryFraction.divWithWork power.1 (OAI.EditApproximation.BinaryFraction.nat (2 * k + 1))
    let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork previous.1 term.1
    (result.1, previous.2 + power.2 + term.2 + result.2 + Nat.size (2 * k + 1) + 5)

def dotWithWork {d : ℕ} (left right : Vector OAI.EditApproximation.BinaryFraction d) : OAI.EditApproximation.BinaryFraction × ℕ :=
  OAI.EditApproximation.BinaryFraction.dotListWithWork left right (List.finRange d)

def distanceWithWork (a b : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let difference := a.subWithWork b
  (difference.1.absolute, difference.2 + 1)

def affineErrorWithWork (position offset velocity prediction tolerance : OAI.EditApproximation.BinaryFraction) :
    Bool × ℕ :=
  let displacement := position.subWithWork offset
  let product := velocity.canonicalMulWithWork prediction
  let error := displacement.1.subWithWork product.1
  let comparison := error.1.absolute.leWithWork tolerance
  (comparison.1, displacement.2 + product.2 + error.2 + comparison.2 + 4)

def bandToleranceWithWork (tau theta : OAI.EditApproximation.BinaryFraction) (b M : ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let product := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork tau theta
  let scale := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork product.1 (OAI.EditApproximation.BinaryFraction.nat b)
  let result := OAI.EditApproximation.BinaryFraction.divWithWork scale.1 (OAI.EditApproximation.BinaryFraction.nat M)
  (result.1, product.2 + scale.2 + result.2 + Nat.size b + Nat.size M + 3)

def medianSeedWithWork (N multiplier : ℕ) (values : List OAI.EditApproximation.BinaryFraction) : List Bool × ℕ :=
  let rounded := OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork multiplier) values
  let sorted := OAI.EditApproximation.wordSortWithWork rounded.1
  let middle := sorted.1.getD (values.length / 2) []
  let clamped := OAI.EditApproximation.wordMinWithWork N.bits middle
  (clamped.1, rounded.2 + sorted.2 + values.length + clamped.2 + Nat.size N + 3)

def groupSampleCountWithWork (M Q b : ℕ) (h : OAI.EditApproximation.BinaryFraction) : List Bool × ℕ :=
  let qm := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat Q) (OAI.EditApproximation.BinaryFraction.nat M)
  let numerator := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork qm.1 h
  let ratio := OAI.EditApproximation.BinaryFraction.divWithWork numerator.1 (OAI.EditApproximation.BinaryFraction.nat b)
  let ceiling := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork ratio.1
  let result := OAI.EditApproximation.wordMinWithWork M.bits ceiling.1
  (result.1, qm.2 + numerator.2 + ratio.2 + ceiling.2 + result.2 +
    Nat.size M + Nat.size Q + Nat.size b + 5)

def gainReadWithWork {β : Type u_1} {σ : Type u_2} (mass : β → OAI.EditApproximation.BinaryFraction)
    (read : ℕ → β × σ → OAI.EditApproximation.BinaryFraction × ℕ) (s : ℕ) (i : β × σ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let word := read s i
  let result := OAI.EditApproximation.BinaryFraction.divWithWork word.1.neg (mass i.1)
  (result.1, word.2 + result.2 + 1)

def decrementReadWithWork {β : Type u_1} {σ : Type u_2} (mass : β → OAI.EditApproximation.BinaryFraction)
    (read : ℕ → β × σ → OAI.EditApproximation.BinaryFraction × ℕ) (s : ℕ) (i : β × σ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let first := read s i
  let second := read (s + 1) i
  let difference := OAI.EditApproximation.BinaryFraction.subWithWork first.1 second.1
  let result := OAI.EditApproximation.BinaryFraction.divWithWork difference.1 (mass i.1)
  (result.1, first.2 + second.2 + difference.2 + result.2 + 1)

def scaledSeedWithWork (U : ℕ) (a gap : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let ratio := OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat U) a
  let rounded := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork ratio.1
  let result := OAI.EditApproximation.BinaryFraction.maxWithWork (OAI.EditApproximation.BinaryFraction.ofNaturalWord rounded.1) gap.absolute
  (result.1, ratio.2 + rounded.2 + result.2 + Nat.size U + 3)

def initialScaleGuardWithWork (U b : ℕ) (A : OAI.EditApproximation.BinaryFraction) : Bool × ℕ :=
  let square := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork A A
  let denominator := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 16) square.1
  let lower := OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat U) denominator.1
  let factor := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 4) A
  let upper := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork factor.1 (OAI.EditApproximation.BinaryFraction.nat U)
  let low := OAI.EditApproximation.BinaryFraction.leWithWork lower.1 (OAI.EditApproximation.BinaryFraction.nat b)
  let high := OAI.EditApproximation.BinaryFraction.leWithWork (OAI.EditApproximation.BinaryFraction.nat b) upper.1
  (low.1 && high.1, square.2 + denominator.2 + lower.2 + factor.2 + upper.2 + low.2 + high.2 +
    Nat.size U + Nat.size b + 7)

def initialCenterGuardWithWork (b U : ℕ) (A : OAI.EditApproximation.BinaryFraction) : Bool × ℕ :=
  let lower := OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat b) (OAI.EditApproximation.BinaryFraction.nat 2)
  let factor := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 4) A
  let upper := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork factor.1 (OAI.EditApproximation.BinaryFraction.nat b)
  let low := OAI.EditApproximation.BinaryFraction.leWithWork lower.1 (OAI.EditApproximation.BinaryFraction.nat U)
  let high := OAI.EditApproximation.BinaryFraction.leWithWork (OAI.EditApproximation.BinaryFraction.nat U) upper.1
  (low.1 && high.1, lower.2 + factor.2 + upper.2 + low.2 + high.2 + Nat.size b + Nat.size U + 5)

def cellCoordinatesWithWork (side : OAI.EditApproximation.BinaryFraction) (p radius : ℕ) : List ℕ × ℕ :=
  let lower := OAI.EditApproximation.saturatingSubtractWithWork p radius
  let upper := OAI.EditApproximation.binaryNaturalAddWithWork p radius
  let firstQ := OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.bitWordValue lower.1)) side
  let lastQ := OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.bitWordValue upper.1)) side
  let first := OAI.EditApproximation.BinaryFraction.naturalFloorWithWork firstQ.1
  let last := OAI.EditApproximation.BinaryFraction.naturalFloorWithWork lastQ.1
  let stop := OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue last.1) 1
  let count := OAI.EditApproximation.saturatingSubtractWithWork (OAI.EditApproximation.bitWordValue stop.1) (OAI.EditApproximation.bitWordValue first.1)
  let values := List.range' (OAI.EditApproximation.bitWordValue first.1) (OAI.EditApproximation.bitWordValue count.1)
  (values, lower.2 + upper.2 + firstQ.2 + lastQ.2 + first.2 + last.2 + stop.2 + count.2 +
    values.length + Nat.size p + Nat.size radius + 9)

def cellGridPointsWithWork (side : OAI.EditApproximation.BinaryFraction) (g cell : ℕ) : List ℕ × ℕ :=
  let next := OAI.EditApproximation.binaryNaturalAddWithWork cell 1
  let lower := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat cell) side
  let upper := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.bitWordValue next.1)) side
  let firstQ := OAI.EditApproximation.BinaryFraction.divWithWork lower.1 (OAI.EditApproximation.BinaryFraction.nat g)
  let lastQ := OAI.EditApproximation.BinaryFraction.divWithWork upper.1 (OAI.EditApproximation.BinaryFraction.nat g)
  let first := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork firstQ.1
  let last := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork lastQ.1
  let count := OAI.EditApproximation.saturatingSubtractWithWork (OAI.EditApproximation.bitWordValue last.1) (OAI.EditApproximation.bitWordValue first.1)
  let indices := List.range' (OAI.EditApproximation.bitWordValue first.1) (OAI.EditApproximation.bitWordValue count.1)
  let points := OAI.EditApproximation.arithmeticMapWithWork (fun i =>
    let product := OAI.EditApproximation.binaryNaturalMulWithWork g i
    (OAI.EditApproximation.bitWordValue product.1, product.2 + Nat.size i + 2)) indices
  (points.1, next.2 + lower.2 + upper.2 + firstQ.2 + lastQ.2 + first.2 + last.2 + count.2 +
    points.2 + indices.length + Nat.size cell + Nat.size g + 10)

def centerEligibilityWithWork (b F : ℕ) (a initial : OAI.EditApproximation.BinaryFraction) : Bool × ℕ :=
  let denominator := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 4) a
  let lower := OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat b) denominator.1
  let factor := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 8) (OAI.EditApproximation.BinaryFraction.nat F)
  let upper := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork factor.1 (OAI.EditApproximation.BinaryFraction.nat b)
  let low := OAI.EditApproximation.BinaryFraction.leWithWork lower.1 initial
  let high := OAI.EditApproximation.BinaryFraction.leWithWork initial upper.1
  (low.1 && high.1, denominator.2 + lower.2 + factor.2 + upper.2 + low.2 + high.2 +
    Nat.size b + Nat.size F + 8)

def refinementScaleGuardWithWork (F b : ℕ) (a w : OAI.EditApproximation.BinaryFraction) : Bool × ℕ :=
  let denominator := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 16) (OAI.EditApproximation.BinaryFraction.nat F)
  let lower := OAI.EditApproximation.BinaryFraction.divWithWork w denominator.1
  let factor := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 8) a
  let upper := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork factor.1 w
  let low := OAI.EditApproximation.BinaryFraction.leWithWork lower.1 (OAI.EditApproximation.BinaryFraction.nat b)
  let high := OAI.EditApproximation.BinaryFraction.leWithWork (OAI.EditApproximation.BinaryFraction.nat b) upper.1
  (low.1 && high.1, denominator.2 + lower.2 + factor.2 + upper.2 + low.2 + high.2 +
    Nat.size b + Nat.size F + 8)

def coarseDivideWithWork (a divisor : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let quotient := OAI.EditApproximation.BinaryFraction.divWithWork a divisor
  let result := OAI.EditApproximation.BinaryFraction.fixedDenominatorWithWork quotient.1 a.denominator a.denominator_pos
  (result.1, quotient.2 + result.2 + 2)

def coarseGridLeftWithWork (two : OAI.EditApproximation.BinaryFraction) : List OAI.EditApproximation.BinaryFraction → List OAI.EditApproximation.BinaryFraction × ℕ
  | [] => ([], 0)
  | head :: rest => OAI.EditApproximation.BinaryFraction.coarseGridScanWithWork two head rest

def coarseMinimumWithWork : List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BinaryFraction × ℕ
  | [] => (OAI.EditApproximation.BinaryFraction.nat 0, 1)
  | a :: rest => OAI.EditApproximation.BinaryFraction.minimumWithWork a rest

def powAllocation (a : OAI.EditApproximation.BinaryFraction) : ℕ → ℕ
  | 0 => 0
  | n + 1 => powAllocation a n + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.powWithWork a n).1 a

def dotListAllocation {d : ℕ} (left right : Vector OAI.EditApproximation.BinaryFraction d) : List (Fin d) → ℕ
  | [] => 0
  | i :: rest => dotListAllocation left right rest +
      OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (left.get i) (right.get i) +
      OAI.EditApproximation.BinaryFraction.canonicalAddAllocation (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (left.get i) (right.get i)).1 (OAI.EditApproximation.BinaryFraction.dotListWithWork left right rest).1

def minimumAllocation (fallback : OAI.EditApproximation.BinaryFraction) : List OAI.EditApproximation.BinaryFraction → ℕ
  | [] => 0
  | head :: rest => minimumAllocation fallback rest +
      OAI.EditApproximation.BinaryFraction.minAllocation head (OAI.EditApproximation.BinaryFraction.minimumWithWork fallback rest).1

def maximumAllocation (fallback : OAI.EditApproximation.BinaryFraction) : List OAI.EditApproximation.BinaryFraction → ℕ
  | [] => 0
  | head :: rest => maximumAllocation fallback rest +
      OAI.EditApproximation.BinaryFraction.maxAllocation head (OAI.EditApproximation.BinaryFraction.maximumWithWork fallback rest).1

def distanceAllocation (a b : OAI.EditApproximation.BinaryFraction) : ℕ := OAI.EditApproximation.BinaryFraction.subAllocation a b + 0

def optimizerUpdateAllocation {d : ℕ} (j : ℕ) (previous selected : Vector OAI.EditApproximation.BinaryFraction d) : ℕ :=
  let step := (OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat 2) (OAI.EditApproximation.BinaryFraction.nat (j + 2))).1
  let complement := (OAI.EditApproximation.BinaryFraction.subWithWork OAI.EditApproximation.BinaryFraction.one step).1
  OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.nat 2) (OAI.EditApproximation.BinaryFraction.nat (j + 2)) + OAI.EditApproximation.BinaryFraction.subAllocation OAI.EditApproximation.BinaryFraction.one step +
    OAI.EditApproximation.vectorMapAllocation d (OAI.EditApproximation.BinaryFraction.optimizerUpdateCellAllocation step complement previous selected) +
    Nat.size (j + 2) + 1

def affineErrorAllocation (position offset velocity prediction tolerance : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let displacement := (OAI.EditApproximation.BinaryFraction.subWithWork position offset).1
  let product := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork velocity prediction).1
  OAI.EditApproximation.BinaryFraction.subAllocation position offset + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation velocity prediction +
    OAI.EditApproximation.BinaryFraction.subAllocation displacement product + OAI.EditApproximation.BinaryFraction.leAllocation (OAI.EditApproximation.BinaryFraction.subWithWork displacement product).1.absolute tolerance

def bandToleranceAllocation (tau theta : OAI.EditApproximation.BinaryFraction) (b M : ℕ) : ℕ :=
  let product := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork tau theta).1
  let scale := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork product (OAI.EditApproximation.BinaryFraction.nat b)).1
  OAI.EditApproximation.BinaryFraction.canonicalMulAllocation tau theta + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation product (OAI.EditApproximation.BinaryFraction.nat b) +
    OAI.EditApproximation.BinaryFraction.divAllocation scale (OAI.EditApproximation.BinaryFraction.nat M) + Nat.size b + Nat.size M

def initialScaleGuardAllocation (U b : ℕ) (A : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let square := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork A A).1
  let denominator := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 16) square).1
  let lower := (OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat U) denominator).1
  let factor := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 4) A).1
  let upper := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork factor (OAI.EditApproximation.BinaryFraction.nat U)).1
  OAI.EditApproximation.BinaryFraction.canonicalMulAllocation A A + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 16) square + OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.nat U) denominator +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 4) A + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation factor (OAI.EditApproximation.BinaryFraction.nat U) +
    OAI.EditApproximation.BinaryFraction.leAllocation lower (OAI.EditApproximation.BinaryFraction.nat b) + OAI.EditApproximation.BinaryFraction.leAllocation (OAI.EditApproximation.BinaryFraction.nat b) upper + Nat.size U + Nat.size b

def initialCenterGuardAllocation (b U : ℕ) (A : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let lower := (OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat b) (OAI.EditApproximation.BinaryFraction.nat 2)).1
  let factor := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 4) A).1
  let upper := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork factor (OAI.EditApproximation.BinaryFraction.nat b)).1
  OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.nat b) (OAI.EditApproximation.BinaryFraction.nat 2) + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 4) A + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation factor (OAI.EditApproximation.BinaryFraction.nat b) +
    OAI.EditApproximation.BinaryFraction.leAllocation lower (OAI.EditApproximation.BinaryFraction.nat U) + OAI.EditApproximation.BinaryFraction.leAllocation (OAI.EditApproximation.BinaryFraction.nat U) upper + Nat.size b + Nat.size U

def scaledSeedAllocation (U : ℕ) (a gap : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let ratio := (OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat U) a).1
  let rounded := (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork ratio).1
  OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.nat U) a + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation ratio +
    OAI.EditApproximation.BinaryFraction.maxAllocation (OAI.EditApproximation.BinaryFraction.ofNaturalWord rounded) gap.absolute + Nat.size U + 2

def centerEligibilityAllocation (b F : ℕ) (a initial : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 4) a +
    OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.nat b) (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 4) a).1 +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 8) (OAI.EditApproximation.BinaryFraction.nat F) +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 8) (OAI.EditApproximation.BinaryFraction.nat F)).1 (OAI.EditApproximation.BinaryFraction.nat b) +
    OAI.EditApproximation.BinaryFraction.leAllocation (OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat b) (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 4) a).1).1 initial +
    OAI.EditApproximation.BinaryFraction.leAllocation initial (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 8) (OAI.EditApproximation.BinaryFraction.nat F)).1 (OAI.EditApproximation.BinaryFraction.nat b)).1 + Nat.size b + Nat.size F

def refinementScaleGuardAllocation (F b : ℕ) (a w : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 16) (OAI.EditApproximation.BinaryFraction.nat F) +
    OAI.EditApproximation.BinaryFraction.divAllocation w (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 16) (OAI.EditApproximation.BinaryFraction.nat F)).1 +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 8) a +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 8) a).1 w +
    OAI.EditApproximation.BinaryFraction.leAllocation (OAI.EditApproximation.BinaryFraction.divWithWork w (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 16) (OAI.EditApproximation.BinaryFraction.nat F)).1).1 (OAI.EditApproximation.BinaryFraction.nat b) +
    OAI.EditApproximation.BinaryFraction.leAllocation (OAI.EditApproximation.BinaryFraction.nat b) (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 8) a).1 w).1 + Nat.size b + Nat.size F

def cellCoordinatesAllocation (side : OAI.EditApproximation.BinaryFraction) (p radius : ℕ) : ℕ :=
  let lower := (OAI.EditApproximation.saturatingSubtractWithWork p radius).1
  let upper := (OAI.EditApproximation.binaryNaturalAddWithWork p radius).1
  let firstQ := (OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.bitWordValue lower)) side).1
  let lastQ := (OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.bitWordValue upper)) side).1
  let first := (OAI.EditApproximation.BinaryFraction.naturalFloorWithWork firstQ).1
  let last := (OAI.EditApproximation.BinaryFraction.naturalFloorWithWork lastQ).1
  let stop := (OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue last) 1).1
  let count := (OAI.EditApproximation.saturatingSubtractWithWork (OAI.EditApproximation.bitWordValue stop) (OAI.EditApproximation.bitWordValue first)).1
  OAI.EditApproximation.saturatingSubtractAllocation p radius + OAI.EditApproximation.binaryNaturalAddAllocation p radius +
    OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.bitWordValue lower)) side + OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.bitWordValue upper)) side +
    OAI.EditApproximation.BinaryFraction.naturalFloorAllocation firstQ + OAI.EditApproximation.BinaryFraction.naturalFloorAllocation lastQ +
    OAI.EditApproximation.binaryNaturalAddAllocation (OAI.EditApproximation.bitWordValue last) 1 +
    OAI.EditApproximation.saturatingSubtractAllocation (OAI.EditApproximation.bitWordValue stop) (OAI.EditApproximation.bitWordValue first) + OAI.EditApproximation.bitWordValue count +
    Nat.size p + Nat.size radius

def cellGridPointsAllocation (side : OAI.EditApproximation.BinaryFraction) (g cell : ℕ) : ℕ :=
  let next := (OAI.EditApproximation.binaryNaturalAddWithWork cell 1).1
  let lower := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat cell) side).1
  let upper := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.bitWordValue next)) side).1
  let firstQ := (OAI.EditApproximation.BinaryFraction.divWithWork lower (OAI.EditApproximation.BinaryFraction.nat g)).1
  let lastQ := (OAI.EditApproximation.BinaryFraction.divWithWork upper (OAI.EditApproximation.BinaryFraction.nat g)).1
  let first := (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork firstQ).1
  let last := (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork lastQ).1
  let count := (OAI.EditApproximation.saturatingSubtractWithWork (OAI.EditApproximation.bitWordValue last) (OAI.EditApproximation.bitWordValue first)).1
  let indices := List.range' (OAI.EditApproximation.bitWordValue first) (OAI.EditApproximation.bitWordValue count)
  OAI.EditApproximation.binaryNaturalAddAllocation cell 1 + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat cell) side +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.bitWordValue next)) side + OAI.EditApproximation.BinaryFraction.divAllocation lower (OAI.EditApproximation.BinaryFraction.nat g) + OAI.EditApproximation.BinaryFraction.divAllocation upper (OAI.EditApproximation.BinaryFraction.nat g) +
    OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation firstQ + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation lastQ +
    OAI.EditApproximation.saturatingSubtractAllocation (OAI.EditApproximation.bitWordValue last) (OAI.EditApproximation.bitWordValue first) +
    OAI.EditApproximation.arithmeticMapAllocation (fun i => OAI.EditApproximation.binaryNaturalMulAllocation g i + Nat.size i) indices +
    indices.length + Nat.size cell + Nat.size g

def medianSeedAllocation (N multiplier : ℕ) (values : List OAI.EditApproximation.BinaryFraction) : ℕ :=
  let rounded := (OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork multiplier) values).1
  let sorted := (OAI.EditApproximation.wordSortWithWork rounded).1
  OAI.EditApproximation.arithmeticMapAllocation (OAI.EditApproximation.BinaryFraction.scaledCeilingAllocation multiplier) values + OAI.EditApproximation.wordSortAllocation rounded +
    OAI.EditApproximation.wordLEAllocation N.bits (sorted.getD (values.length / 2) []) +
    Nat.size N

def groupSampleCountAllocation (M Q b : ℕ) (h : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let qm := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat Q) (OAI.EditApproximation.BinaryFraction.nat M)).1
  let numerator := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork qm h).1
  let ratio := (OAI.EditApproximation.BinaryFraction.divWithWork numerator (OAI.EditApproximation.BinaryFraction.nat b)).1
  OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat Q) (OAI.EditApproximation.BinaryFraction.nat M) + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation qm h +
    OAI.EditApproximation.BinaryFraction.divAllocation numerator (OAI.EditApproximation.BinaryFraction.nat b) + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation ratio +
    OAI.EditApproximation.wordLEAllocation M.bits (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork ratio).1 +
    Nat.size M + Nat.size Q + Nat.size b

def refinementUpdateAllocation (delta cone : OAI.EditApproximation.BinaryFraction) : Option OAI.EditApproximation.BinaryFraction → ℕ
  | none => 0
  | some online =>
    let denominator := (OAI.EditApproximation.BinaryFraction.canonicalAddWithWork OAI.EditApproximation.BinaryFraction.one delta).1
    let lower := (OAI.EditApproximation.BinaryFraction.divWithWork cone denominator).1
    let clipped := (OAI.EditApproximation.BinaryFraction.maxWithWork lower online).1
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation OAI.EditApproximation.BinaryFraction.one delta + OAI.EditApproximation.BinaryFraction.divAllocation cone denominator +
      OAI.EditApproximation.BinaryFraction.maxAllocation lower online + OAI.EditApproximation.BinaryFraction.minAllocation cone clipped

def coefficientAllocation (kappa : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 2) kappa + OAI.EditApproximation.BinaryFraction.subAllocation OAI.EditApproximation.BinaryFraction.one (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 2) kappa).1 + 0

def gainReadAllocation {β : Type u_1} {σ : Type u_2} (mass : β → OAI.EditApproximation.BinaryFraction)
    (read : ℕ → β × σ → OAI.EditApproximation.BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) : ℕ :=
  footprint s i + OAI.EditApproximation.BinaryFraction.divAllocation (read s i).1.neg (mass i.1) + 0

def decrementReadAllocation {β : Type u_1} {σ : Type u_2} (mass : β → OAI.EditApproximation.BinaryFraction)
    (read : ℕ → β × σ → OAI.EditApproximation.BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) : ℕ :=
  footprint s i + footprint (s + 1) i + OAI.EditApproximation.BinaryFraction.subAllocation (read s i).1 (read (s + 1) i).1 +
    OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.subWithWork (read s i).1 (read (s + 1) i).1).1 (mass i.1) + 0

def logarithmWithWork (r : OAI.EditApproximation.BinaryFraction) (k : ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let numerator := OAI.EditApproximation.BinaryFraction.subWithWork r OAI.EditApproximation.BinaryFraction.one
  let denominator := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork r OAI.EditApproximation.BinaryFraction.one
  let ratio := OAI.EditApproximation.BinaryFraction.divWithWork numerator.1 denominator.1
  let subtotal :=  OAI.EditApproximation.BinaryFraction.logarithmPartialWithWork ratio.1 k
  let result := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 2) subtotal.1
  (result.1, numerator.2 + denominator.2 + ratio.2 + subtotal.2 + result.2 + 5)

def optimisticTermReadWithWork {β : Type u_1} {σ : Type u_2} (mass : β → OAI.EditApproximation.BinaryFraction)
    (read : ℕ → β × σ → OAI.EditApproximation.BinaryFraction × ℕ) (coefficient : OAI.EditApproximation.BinaryFraction)
    (s : ℕ) (i : β × σ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let gain := OAI.EditApproximation.BinaryFraction.gainReadWithWork mass read s i
  let decrement := OAI.EditApproximation.BinaryFraction.decrementReadWithWork mass read s i
  let scaled := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork coefficient decrement.1
  let total := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork gain.1 scaled.1
  (total.1, gain.2 + decrement.2 + scaled.2 + total.2 + 2)

def queryExponentsWithWork (N F : ℕ) (a w : OAI.EditApproximation.BinaryFraction) : List ℕ × ℕ :=
  let count := max 1 N.bits.length
  let selected := OAI.EditApproximation.filterWithWork (fun e =>
    let guard := OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork F (2 ^ e) a w
    (guard.1, guard.2 + e + 2)) (List.range count)
  (selected.1, selected.2 + count + N.bits.length + 2)

def seedMedianWithWork (N multiplier : ℕ) (values : List OAI.EditApproximation.BinaryFraction) : List Bool × ℕ :=
  let median := OAI.EditApproximation.BinaryFraction.medianSeedWithWork N multiplier values
  let trimmed := OAI.EditApproximation.trimBitWordWithWork median.1
  (trimmed.1, median.2 + trimmed.2 + 1)

def coarseGridPenaltyWithWork (two : OAI.EditApproximation.BinaryFraction) (source : List OAI.EditApproximation.BinaryFraction) :
    List OAI.EditApproximation.BinaryFraction × ℕ :=
  let left := OAI.EditApproximation.BinaryFraction.coarseGridLeftWithWork two source
  let right := OAI.EditApproximation.BinaryFraction.coarseGridLeftWithWork two source.reverse
  let result := OAI.EditApproximation.BinaryFraction.coarseGridZipMinimumWithWork left.1 right.1.reverse
  (result.1, left.2 + right.2 + result.2 + 3 * source.length)

def coarseChildThresholdWithWork (B q : ℕ) (allowance : OAI.EditApproximation.BinaryFraction) (draw : Fin B) :
    OAI.EditApproximation.BinaryFraction × ℕ :=
  let numerator := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork allowance (OAI.EditApproximation.BinaryFraction.nat (draw.val + 1))
  let divisor := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat B) (OAI.EditApproximation.BinaryFraction.nat q)
  let result := OAI.EditApproximation.BinaryFraction.coarseDivideWithWork numerator.1 divisor.1
  (result.1, numerator.2 + divisor.2 + result.2 + Nat.size (draw.val + 1) + Nat.size B + Nat.size q + 4)

def coarseChildAllowanceWithWork (L : ℕ) (threshold : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let result := OAI.EditApproximation.BinaryFraction.coarseDivideWithWork threshold (OAI.EditApproximation.BinaryFraction.nat L)
  (result.1, result.2 + Nat.size L + 1)

def logarithmPartialAllocation (b : OAI.EditApproximation.BinaryFraction) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    let previous := (OAI.EditApproximation.BinaryFraction.logarithmPartialWithWork b n).1
    let power := (OAI.EditApproximation.BinaryFraction.powWithWork b (2 * n + 1)).1
    let term := (OAI.EditApproximation.BinaryFraction.divWithWork power (OAI.EditApproximation.BinaryFraction.nat (2 * n + 1))).1
    logarithmPartialAllocation b n + OAI.EditApproximation.BinaryFraction.powAllocation b (2 * n + 1) +
      OAI.EditApproximation.BinaryFraction.divAllocation power (OAI.EditApproximation.BinaryFraction.nat (2 * n + 1)) + OAI.EditApproximation.BinaryFraction.canonicalAddAllocation previous term + Nat.size (2 * n + 1) + 1

def bandMassAllocation {M : ℕ} (mass : Vector OAI.EditApproximation.BinaryFraction M) : ℕ :=
  OAI.EditApproximation.BinaryFraction.dotListAllocation mass (Vector.replicate M OAI.EditApproximation.BinaryFraction.one) (List.finRange M) + 2 * M

def sumListAllocation (values : List OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.dotListAllocation (Vector.ofFn values.get) (Vector.replicate values.length OAI.EditApproximation.BinaryFraction.one)
    (List.finRange values.length) + 3 * values.length

def naturalDistanceLeAllocation (a b radius : ℕ) : ℕ :=
  OAI.EditApproximation.BinaryFraction.distanceAllocation (OAI.EditApproximation.BinaryFraction.nat a) (OAI.EditApproximation.BinaryFraction.nat b) + OAI.EditApproximation.BinaryFraction.leAllocation (OAI.EditApproximation.BinaryFraction.distanceWithWork (OAI.EditApproximation.BinaryFraction.nat a) (OAI.EditApproximation.BinaryFraction.nat b)).1 (OAI.EditApproximation.BinaryFraction.nat radius) +
    Nat.size a + Nat.size b + Nat.size radius

def queryExponentsAllocation (N F : ℕ) (a w : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let count := max 1 N.bits.length
  OAI.EditApproximation.filterAllocation (fun e => ((OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork F (2 ^ e) a w).1,
      (OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork F (2 ^ e) a w).2 + e + 2))
    (fun e => OAI.EditApproximation.BinaryFraction.refinementScaleGuardAllocation F (2 ^ e) a w + e + 1) (List.range count) +
    count + N.bits.length

def seedMedianAllocation (N multiplier : ℕ) (values : List OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.medianSeedAllocation N multiplier values +
    OAI.EditApproximation.trimBitWordAllocation (OAI.EditApproximation.BinaryFraction.medianSeedWithWork N multiplier values).1 + 0

def onlineMinimumAllocation : List OAI.EditApproximation.BinaryFraction → ℕ
  | [] => 0
  | first :: rest => OAI.EditApproximation.BinaryFraction.minimumAllocation first rest

def optimisticTermReadAllocation {β : Type u_1} {σ : Type u_2} (mass : β → OAI.EditApproximation.BinaryFraction)
    (read : ℕ → β × σ → OAI.EditApproximation.BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (coefficient : OAI.EditApproximation.BinaryFraction) (s : ℕ) (i : β × σ) : ℕ :=
  let gain := (OAI.EditApproximation.BinaryFraction.gainReadWithWork mass read s i).1
  let decrement := (OAI.EditApproximation.BinaryFraction.decrementReadWithWork mass read s i).1
  OAI.EditApproximation.BinaryFraction.gainReadAllocation mass read footprint s i + OAI.EditApproximation.BinaryFraction.decrementReadAllocation mass read footprint s i +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation coefficient decrement +
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation gain (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork coefficient decrement).1 + 0

def gradientCellWithWork {d : ℕ} (G : ℕ) (linear point : Vector OAI.EditApproximation.BinaryFraction d)
    (i : Fin d) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let smoothing := OAI.EditApproximation.BinaryFraction.powWithWork (OAI.EditApproximation.BinaryFraction.nat G) 50
  let inverse := smoothing.1.invWithWork
  let shifted := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork (point.get i) inverse.1
  let logarithm := OAI.EditApproximation.BinaryFraction.logarithmWithWork shifted.1 (G ^ 60)
  let deficit := OAI.EditApproximation.BinaryFraction.subWithWork logarithm.1.neg OAI.EditApproximation.BinaryFraction.one
  let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork deficit.1 (linear.get i)
  (result.1, smoothing.2 + inverse.2 + shifted.2 + logarithm.2 + deficit.2 + result.2 +
    Nat.size G + 70)

def queryScalesWithWork (N F : ℕ) (a value : OAI.EditApproximation.BinaryFraction) : List ℕ × ℕ :=
  let exponents := OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a value
  let scales := OAI.EditApproximation.arithmeticMapWithWork (fun e => (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.powerTwoWord e), e + 3)) exponents.1
  (scales.1, exponents.2 + scales.2 + 1)

def querySeedMedianWithWork (N multiplier : ℕ) (words : List OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let result := OAI.EditApproximation.BinaryFraction.seedMedianWithWork N multiplier words
  (OAI.EditApproximation.BinaryFraction.ofNaturalWord result.1, result.2 + result.1.length + 1)

def coarseBinaryPenaltyWithWork (two : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction.CoarseBinaryArray → OAI.EditApproximation.BinaryFraction.CoarseBinaryArray × ℕ
  | none => (none, 0)
  | some values =>
    let result := OAI.EditApproximation.BinaryFraction.coarseGridPenaltyWithWork two values
    (some result.1, result.2)

def logarithmAllocation (r : OAI.EditApproximation.BinaryFraction) (n : ℕ) : ℕ :=
  let numerator := (OAI.EditApproximation.BinaryFraction.subWithWork r OAI.EditApproximation.BinaryFraction.one).1
  let denominator := (OAI.EditApproximation.BinaryFraction.canonicalAddWithWork r OAI.EditApproximation.BinaryFraction.one).1
  let ratio := (OAI.EditApproximation.BinaryFraction.divWithWork numerator denominator).1
  OAI.EditApproximation.BinaryFraction.subAllocation r OAI.EditApproximation.BinaryFraction.one + OAI.EditApproximation.BinaryFraction.canonicalAddAllocation r OAI.EditApproximation.BinaryFraction.one + OAI.EditApproximation.BinaryFraction.divAllocation numerator denominator +
    OAI.EditApproximation.BinaryFraction.logarithmPartialAllocation ratio n + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 2) (OAI.EditApproximation.BinaryFraction.logarithmPartialWithWork ratio n).1

def queryScalesAllocation (N F : ℕ) (a value : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.BinaryFraction.queryExponentsAllocation N F a value +
    OAI.EditApproximation.arithmeticMapAllocation (fun e => e + 1) (OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a value).1

def coarseIndexChildren {B : ℕ} (k q L : ℕ) (two : OAI.EditApproximation.BinaryFraction)
    (width : Fin B → ℕ)
    (evaluate : Fin B → OAI.EditApproximation.BinaryFraction → ℕ → OAI.EditApproximation.BinaryFraction.CoarseBinaryArray × ℕ)
    (draw : Fin B → Fin B) (allowance : OAI.EditApproximation.BinaryFraction) :
    List (Fin B) → ℕ → OAI.EditApproximation.BinaryFraction.CoarseBinaryArray × ℕ
  | [], _ => (none, 0)
  | i :: rest, start =>
    let threshold := OAI.EditApproximation.BinaryFraction.coarseChildThresholdWithWork B q allowance (draw i)
    let childAllowance := OAI.EditApproximation.BinaryFraction.coarseChildAllowanceWithWork L threshold.1
    let evaluated := evaluate i childAllowance.1 start
    let penalty := OAI.EditApproximation.BinaryFraction.coarseBinaryPenaltyWithWork two evaluated.1
    let scale := OAI.EditApproximation.BinaryFraction.coarseChildAllowanceWithWork q allowance
    let contribution := OAI.EditApproximation.BinaryFraction.coarseBinaryMapWithWork (OAI.EditApproximation.BinaryFraction.coarseContributionWithWork threshold.1 scale.1) penalty.1
    let remainder := coarseIndexChildren k q L two width evaluate draw allowance rest (start + width i)
    let total := OAI.EditApproximation.BinaryFraction.coarseBinaryAddWithWork contribution.1 remainder.1
    (total.1, threshold.2 + childAllowance.2 + evaluated.2 + penalty.2 + scale.2 + contribution.2 +
      remainder.2 + total.2 + Nat.size start + Nat.size (width i) + 9)

def gradientCellAllocation {d : ℕ} (G : ℕ) (linear point : Vector OAI.EditApproximation.BinaryFraction d)
    (i : Fin d) : ℕ :=
  let smoothing := (OAI.EditApproximation.BinaryFraction.powWithWork (OAI.EditApproximation.BinaryFraction.nat G) 50).1
  let inverse := smoothing.invWithWork.1
  let shifted := (OAI.EditApproximation.BinaryFraction.canonicalAddWithWork (point.get i) inverse).1
  let logarithm := (OAI.EditApproximation.BinaryFraction.logarithmWithWork shifted (G ^ 60)).1
  let deficit := (OAI.EditApproximation.BinaryFraction.subWithWork logarithm.neg OAI.EditApproximation.BinaryFraction.one).1
  OAI.EditApproximation.BinaryFraction.powAllocation (OAI.EditApproximation.BinaryFraction.nat G) 50 + OAI.EditApproximation.BinaryFraction.invAllocation smoothing +
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation (point.get i) inverse + OAI.EditApproximation.BinaryFraction.logarithmAllocation shifted (G ^ 60) +
    OAI.EditApproximation.BinaryFraction.subAllocation logarithm.neg OAI.EditApproximation.BinaryFraction.one + OAI.EditApproximation.BinaryFraction.canonicalAddAllocation deficit (linear.get i) + Nat.size G + 1

def coarseIndexedWithWork {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : OAI.EditApproximation.BinaryFraction) : (d offset : ℕ) → OAI.EditApproximation.CoarseThresholdDraws B d →
    OAI.EditApproximation.BinaryFraction → ℕ → OAI.EditApproximation.BinaryFraction.CoarseBinaryArray × ℕ
  | 0, offset, _, allowance, start =>
    let descriptor := OAI.EditApproximation.coarseDescriptorWithWork B 0 n offset
    let size := OAI.EditApproximation.bitWordValue descriptor.1
    let prune := OAI.EditApproximation.BinaryFraction.leWithWork (OAI.EditApproximation.BinaryFraction.nat size) allowance
    if prune.1 then (none, descriptor.2 + prune.2 + Nat.size size + 1) else
    let letter := OAI.EditApproximation.coarsePaddedReadWithWork n source offset
    let cells := OAI.EditApproximation.arithmeticMapWithWork (fun shift : Fin (2 * k + 1) =>
      let mismatch := OAI.EditApproximation.BinaryFraction.coarseReadShiftWithWork k n target letter.1 start shift
      let value := OAI.EditApproximation.BinaryFraction.coarseGridNatWithWork allowance.denominator allowance.denominator_pos mismatch.1
      (value.1, value.2 + mismatch.2)) (List.finRange (2 * k + 1))
    (some cells.1, descriptor.2 + letter.2 + prune.2 + cells.2 +
      Nat.size size + 3 * (2 * k + 1) + 1)
  | d + 1, offset, (draws, below), allowance, start =>
    let descriptor := OAI.EditApproximation.coarseDescriptorWithWork B (d + 1) n offset
    let size := OAI.EditApproximation.bitWordValue descriptor.1
    let prune := OAI.EditApproximation.BinaryFraction.leWithWork (OAI.EditApproximation.BinaryFraction.nat size) allowance
    if prune.1 then (none, descriptor.2 + prune.2 + Nat.size size + 1) else
    let capacity := OAI.EditApproximation.bitPowerWithWork B.bits d
    let childOffset := fun i : Fin B =>
      OAI.EditApproximation.coarseChildOffsetWithWork offset (OAI.EditApproximation.bitWordValue capacity.1) i.val
    let childSize := fun i : Fin B =>
      OAI.EditApproximation.coarseDescriptorWithWork B d n (OAI.EditApproximation.bitWordValue (childOffset i).1)
    let result := OAI.EditApproximation.BinaryFraction.coarseIndexChildren k q L two
      (fun i => OAI.EditApproximation.bitWordValue (childSize i).1)
      (fun i a s =>
        let evaluated := coarseIndexedWithWork k q L n source target two d
          (OAI.EditApproximation.bitWordValue (childOffset i).1) (below i) a s
        let next := OAI.EditApproximation.binaryNaturalAddWithWork s (OAI.EditApproximation.bitWordValue (childSize i).1)
        (evaluated.1, evaluated.2 + 3 * ((childOffset i).2 + (childSize i).2 + next.2 + 3)))
      draws allowance (List.finRange B) start
    (result.1, descriptor.2 + capacity.2 + result.2 + prune.2 + Nat.size size + B + 1)

def gradientAllocation {d : ℕ} (G : ℕ) (linear point : Vector OAI.EditApproximation.BinaryFraction d) : ℕ :=
  OAI.EditApproximation.vectorMapAllocation d (OAI.EditApproximation.BinaryFraction.gradientCellAllocation G linear point)

end OAI.EditApproximation.BinaryFraction

end



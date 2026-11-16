-- Prove2me | Definitions.Def_EditApproxScheme_12
-- name    : EditApproxScheme_12
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:45:52.335489+00:00
-- url     : https://prove2.me/theorems/fd9ab884-452c-42ef-a98c-2a47651402e5
-- title:
--   Edit-distance approximation scheme, part 12 of 20: group-member and unskipped sources; edit scripts
-- statement:
--   This is **part 12 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains group labels and inputs and their transport, prepared reads of unskipped bands, unskipped estimate sources and their choice, sampled group-action sources, prepared online reads, and the edit scripts (single insertion, deletion and substitution steps) defining the edit distance. It also proves 36 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L6613-L7311 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 12 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_11

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

open Finset

theorem _root_.OAI.EditApproximation.Lemmas.vectorMapWithWork_value {α : Type 0} (d : ℕ) (f : Fin d → Prod.{0, 0} α ℕ) (i : Fin d) :
    (OAI.EditApproximation.vectorMapWithWork d f).1.get i = (f i).1 := by
  change (Vector.ofFn f |>.map Prod.fst)[i.val] = _
  simp only [Vector.getElem_map, Vector.getElem_ofFn]

theorem _root_.OAI.EditApproximation.Lemmas.wordMinWithWork_value (a : List.{0} Bool) (b : List.{0} Bool) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.wordMinWithWork a b).1 = min (OAI.EditApproximation.bitWordValue a) (OAI.EditApproximation.bitWordValue b) := by
  unfold OAI.EditApproximation.wordMinWithWork
  dsimp only
  split_ifs with h
  · exact (min_eq_left ((OAI.EditApproximation.Lemmas.wordLEWithWork_value a b).mp h)).symm
  · exact (min_eq_right (le_of_not_ge (fun hle => h ((OAI.EditApproximation.Lemmas.wordLEWithWork_value a b).mpr hle)))).symm

theorem _root_.OAI.EditApproximation.Lemmas.bitCeilDivWithWork_value (divisor : List.{0} Bool) (bits : List.{0} Bool) (hd : LT.lt.{0} 0 (OAI.EditApproximation.bitWordValue divisor)) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitCeilDivWithWork divisor bits).1 =
      ⌈((OAI.EditApproximation.bitWordValue bits : ℚ) / OAI.EditApproximation.bitWordValue divisor)⌉₊ := by
  let q := OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitDivModWithWork divisor bits).1
  let r := OAI.EditApproximation.bitWordValue (OAI.EditApproximation.bitDivModWithWork divisor bits).2.1
  have h := OAI.EditApproximation.Lemmas.bitDivModWithWork_value divisor bits hd
  have heq : OAI.EditApproximation.bitWordValue bits = OAI.EditApproximation.bitWordValue divisor * q + r := h.1
  have hr : r < OAI.EditApproximation.bitWordValue divisor := h.2
  have hdQ : (0 : ℚ) < OAI.EditApproximation.bitWordValue divisor := by exact_mod_cast hd
  unfold OAI.EditApproximation.bitCeilDivWithWork
  dsimp only
  split_ifs with hz
  · have hr0 : r = 0 := by
      exact (OAI.EditApproximation.Lemmas.bitCompareWithWork_eq (OAI.EditApproximation.bitDivModWithWork divisor bits).2.1 []).1 hz
    have hratio : (OAI.EditApproximation.bitWordValue bits : ℚ) / OAI.EditApproximation.bitWordValue divisor = (q : ℚ) := by
      apply (div_eq_iff hdQ.ne').mpr
      exact_mod_cast (show OAI.EditApproximation.bitWordValue bits = q * OAI.EditApproximation.bitWordValue divisor by nlinarith only [heq, hr0])
    rw [hratio]
    exact (Nat.ceil_natCast q).symm
  · have hr0 : r ≠ 0 := by
      intro hzero
      exact hz ((OAI.EditApproximation.Lemmas.bitCompareWithWork_eq (OAI.EditApproximation.bitDivModWithWork divisor bits).2.1 []).2 hzero)
    rw [OAI.EditApproximation.Lemmas.bitAddWithWork_value]
    change q + 1 + 0 = _
    simp only [Nat.add_zero]
    symm
    apply (Nat.ceil_eq_iff (by omega : q + 1 ≠ 0)).mpr
    constructor
    · simp only [Nat.add_sub_cancel]
      rw [lt_div_iff₀ hdQ]
      exact_mod_cast (show q * OAI.EditApproximation.bitWordValue divisor < OAI.EditApproximation.bitWordValue bits by
        nlinarith only [heq, Nat.pos_of_ne_zero hr0])
    · rw [div_le_iff₀ hdQ]
      push_cast
      exact_mod_cast (show OAI.EditApproximation.bitWordValue bits ≤ (q + 1) * OAI.EditApproximation.bitWordValue divisor by nlinarith only [heq, hr])

theorem _root_.OAI.EditApproximation.Lemmas.naturalCeilingWithWork_value (a : OAI.EditApproximation.BinaryFraction) :
    OAI.EditApproximation.bitWordValue (a.naturalCeilingWithWork).1 = ⌈a.value⌉₊ := by
  cases hs : a.numerator.negative
  · simpa only [OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork, hs, Bool.false_eq_true, ↓reduceIte,
      OAI.EditApproximation.BinaryFraction.value, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude, Int.cast_natCast] using
      OAI.EditApproximation.Lemmas.bitCeilDivWithWork_value a.denominator a.numerator.bits a.denominator_pos
  · have hn : a.value ≤ 0 := by
      (simp only [OAI.EditApproximation.BinaryFraction.value, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude, hs, ↓reduceIte, Int.cast_neg, Int.cast_natCast])
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    (simp only [OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork, hs, ↓reduceIte, OAI.EditApproximation.bitWordValue])
    exact (Nat.ceil_eq_zero.mpr hn).symm

theorem _root_.OAI.EditApproximation.Lemmas.representation_value (a : OAI.EditApproximation.BinaryFraction) : a.representation.value = a.value := rfl

theorem _root_.OAI.EditApproximation.Lemmas.eq_of_num_den {a : OAI.EditApproximation.UnreducedRational} {b : OAI.EditApproximation.UnreducedRational} (hnum : Eq.{1} a.num b.num) (hden : Eq.{1} a.den b.den) : a = b := by
  cases a
  cases b
  cases hnum
  cases hden
  rfl

theorem _root_.OAI.EditApproximation.Lemmas.canonicalizeWithWork_representation (a : OAI.EditApproximation.BinaryFraction) :
    (OAI.EditApproximation.BinaryFraction.canonicalizeWithWork a).1.representation = a.representation := by
  apply OAI.EditApproximation.Lemmas.eq_of_num_den
  · (simp only [OAI.EditApproximation.BinaryFraction.canonicalizeWithWork, OAI.EditApproximation.BinaryFraction.representation, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.Lemmas.trimBitWordWithWork_value])
  · exact OAI.EditApproximation.Lemmas.trimBitWordWithWork_value a.denominator

theorem _root_.OAI.EditApproximation.Lemmas.mulWithWork_value (a : OAI.EditApproximation.SignedBinary) (b : OAI.EditApproximation.SignedBinary) :
    (a.mulWithWork b).1.value = a.value * b.value := by
  simp only [OAI.EditApproximation.SignedBinary.mulWithWork, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.Lemmas.bitMulWithWork_value]
  cases a.negative <;> cases b.negative <;> simp [OAI.EditApproximation.signedMagnitude]

theorem _root_.OAI.EditApproximation.Lemmas.mulWithWork_representation (a : OAI.EditApproximation.BinaryFraction) (b : OAI.EditApproximation.BinaryFraction) :
    (a.mulWithWork b).1.representation = a.representation.mul b.representation := by
  apply OAI.EditApproximation.Lemmas.eq_of_num_den
  · exact OAI.EditApproximation.Lemmas.mulWithWork_value a.numerator b.numerator
  · exact OAI.EditApproximation.Lemmas.bitMulWithWork_value a.denominator b.denominator

theorem _root_.OAI.EditApproximation.Lemmas.canonicalMulWithWork_representation (a : OAI.EditApproximation.BinaryFraction) (b : OAI.EditApproximation.BinaryFraction) :
    (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork a b).1.representation = a.representation.mul b.representation := by
  rw [OAI.EditApproximation.BinaryFraction.canonicalMulWithWork, OAI.EditApproximation.Lemmas.canonicalizeWithWork_representation, OAI.EditApproximation.Lemmas.mulWithWork_representation]

theorem _root_.OAI.EditApproximation.Lemmas.zero_representation : OAI.EditApproximation.BinaryFraction.zero.representation = OAI.EditApproximation.UnreducedRational.zero := by
  apply OAI.EditApproximation.Lemmas.eq_of_num_den <;> rfl

theorem _root_.OAI.EditApproximation.Lemmas.invWithWork_representation (a : OAI.EditApproximation.BinaryFraction) :
    (a.invWithWork).1.representation = a.representation.inv := by
  unfold OAI.EditApproximation.BinaryFraction.invWithWork
  dsimp only
  split_ifs with h
  · have hz : OAI.EditApproximation.bitWordValue a.numerator.bits = 0 := by
      simpa only [OAI.EditApproximation.bitWordValue] using (OAI.EditApproximation.Lemmas.bitCompareWithWork_eq a.numerator.bits []).1 h
    have hv : a.numerator.value = 0 := by (simp [OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude, hz])
    (simp only [OAI.EditApproximation.UnreducedRational.inv, OAI.EditApproximation.BinaryFraction.representation, hv, ↓reduceDIte])
    exact OAI.EditApproximation.Lemmas.zero_representation
  · have hn : OAI.EditApproximation.bitWordValue a.numerator.bits ≠ 0 := by
      intro hz
      exact h ((OAI.EditApproximation.Lemmas.bitCompareWithWork_eq a.numerator.bits []).2 (by simpa [OAI.EditApproximation.bitWordValue] using hz))
    have hv : a.numerator.value ≠ 0 := by
      cases hs : a.numerator.negative <;> (simp [OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude, hs, hn])
    (simp only [OAI.EditApproximation.UnreducedRational.inv, OAI.EditApproximation.BinaryFraction.representation, hv, ↓reduceDIte])
    apply OAI.EditApproximation.Lemmas.eq_of_num_den
    · cases hs : a.numerator.negative <;>
        simp [OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude, hs, Int.sign_natCast_of_ne_zero hn]
    · cases hs : a.numerator.negative <;> (simp [OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude, hs])

theorem _root_.OAI.EditApproximation.Lemmas.divWithWork_representation (a : OAI.EditApproximation.BinaryFraction) (b : OAI.EditApproximation.BinaryFraction) :
    (a.divWithWork b).1.representation = a.representation.div b.representation := by
  (simp only [OAI.EditApproximation.BinaryFraction.divWithWork, OAI.EditApproximation.Lemmas.canonicalMulWithWork_representation, OAI.EditApproximation.Lemmas.invWithWork_representation,
    OAI.EditApproximation.UnreducedRational.div])

theorem _root_.OAI.EditApproximation.Lemmas.value_mul (a : OAI.EditApproximation.UnreducedRational) (b : OAI.EditApproximation.UnreducedRational) : (a.mul b).value = a.value * b.value := by
  simp [OAI.EditApproximation.UnreducedRational.mul, OAI.EditApproximation.UnreducedRational.value, mul_div_mul_comm]

theorem _root_.OAI.EditApproximation.Lemmas.value_inv (a : OAI.EditApproximation.UnreducedRational) : a.inv.value = a.value⁻¹ := by
  by_cases h : a.num = 0
  · simp [OAI.EditApproximation.UnreducedRational.inv, h, OAI.EditApproximation.UnreducedRational.value, OAI.EditApproximation.UnreducedRational.zero]
  · have hn : (a.num.natAbs : ℚ) ≠ 0 := by exact_mod_cast (Int.natAbs_pos.mpr h).ne'
    have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
    have hsign : ((a.num.sign : ℤ) : ℚ) * a.num = (a.num.natAbs : ℚ) := by
      simpa only [Int.cast_mul, Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ℚ)) (Int.sign_mul_self_eq_natAbs a.num)
    simp only [OAI.EditApproximation.UnreducedRational.inv, h, ↓reduceDIte, OAI.EditApproximation.UnreducedRational.value]
    push_cast
    apply eq_inv_of_mul_eq_one_left
    field_simp [hn, hd]
    exact hsign

theorem _root_.OAI.EditApproximation.Lemmas.value_div (a : OAI.EditApproximation.UnreducedRational) (b : OAI.EditApproximation.UnreducedRational) : (a.div b).value = a.value / b.value := by
  simp [OAI.EditApproximation.Lemmas.value_mul, OAI.EditApproximation.Lemmas.value_inv, OAI.EditApproximation.UnreducedRational.div, div_eq_mul_inv]

theorem _root_.OAI.EditApproximation.Lemmas.divWithWork_value (a : OAI.EditApproximation.BinaryFraction) (b : OAI.EditApproximation.BinaryFraction) :
    (OAI.EditApproximation.BinaryFraction.divWithWork a b).1.value = a.value / b.value := by
  rw [← OAI.EditApproximation.Lemmas.representation_value, OAI.EditApproximation.Lemmas.divWithWork_representation,
    OAI.EditApproximation.Lemmas.value_div, OAI.EditApproximation.Lemmas.representation_value, OAI.EditApproximation.Lemmas.representation_value]

theorem _root_.OAI.EditApproximation.Lemmas.canonicalMulWithWork_value (a : OAI.EditApproximation.BinaryFraction) (b : OAI.EditApproximation.BinaryFraction) :
    (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork a b).1.value = a.value * b.value := by
  rw [← OAI.EditApproximation.Lemmas.representation_value, OAI.EditApproximation.Lemmas.canonicalMulWithWork_representation,
    OAI.EditApproximation.Lemmas.value_mul, OAI.EditApproximation.Lemmas.representation_value, OAI.EditApproximation.Lemmas.representation_value]

theorem _root_.OAI.EditApproximation.Lemmas.value_ofInt (a : ℤ) : (OAI.EditApproximation.SignedBinary.ofInt a).value = a := by
  by_cases h : a < 0
  · simpa only [OAI.EditApproximation.SignedBinary.ofInt, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.Lemmas.bitWordValue_bits, OAI.EditApproximation.signedMagnitude, h, decide_true,
      ↓reduceIte] using (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · simpa only [OAI.EditApproximation.SignedBinary.ofInt, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.Lemmas.bitWordValue_bits, OAI.EditApproximation.signedMagnitude, h, decide_false,
      Bool.false_eq_true, ↓reduceIte] using (Int.eq_natAbs_of_nonneg (le_of_not_gt h)).symm

theorem _root_.OAI.EditApproximation.Lemmas.nat_representation (n : ℕ) : (OAI.EditApproximation.BinaryFraction.nat n).representation = OAI.EditApproximation.UnreducedRational.nat n := by
  apply OAI.EditApproximation.Lemmas.eq_of_num_den
  · change (OAI.EditApproximation.SignedBinary.ofInt (n : ℤ)).value = (n : ℤ)
    exact OAI.EditApproximation.Lemmas.value_ofInt _
  · rfl

theorem _root_.OAI.EditApproximation.Lemmas.value_nat (n : ℕ) : (OAI.EditApproximation.UnreducedRational.nat n).value = n := by (simp [OAI.EditApproximation.UnreducedRational.nat, OAI.EditApproximation.UnreducedRational.value])

theorem _root_.OAI.EditApproximation.Lemmas.nat_value (n : ℕ) : (OAI.EditApproximation.BinaryFraction.nat n).value = (n : ℚ) := by
  rw [← OAI.EditApproximation.Lemmas.representation_value, OAI.EditApproximation.Lemmas.nat_representation, OAI.EditApproximation.Lemmas.value_nat]

theorem _root_.OAI.EditApproximation.Lemmas.groupSampleCountWithWork_value (M : ℕ) (Q : ℕ) (b : ℕ) (h : OAI.EditApproximation.BinaryFraction) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork M Q b h).1 = OAI.EditApproximation.groupSampleCount M Q b h.value := by
  simp only [OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork, OAI.EditApproximation.Lemmas.wordMinWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits,
    OAI.EditApproximation.Lemmas.naturalCeilingWithWork_value, OAI.EditApproximation.Lemmas.divWithWork_value, OAI.EditApproximation.Lemmas.canonicalMulWithWork_value,
    OAI.EditApproximation.Lemmas.nat_value, OAI.EditApproximation.groupSampleCount]

def countedGroupMemberSourceWithWork {M T : ℕ} (Q b : ℕ) (scales : Fin T → OAI.EditApproximation.BinaryFraction)
    (connection : OAI.EditApproximation.BinaryFraction) (envelope values : Vector OAI.EditApproximation.BinaryFraction M)
    (draw : ∀ t, Fin (OAI.EditApproximation.groupSampleCount M Q b (scales t).value) → Fin M × ℕ) : OAI.EditApproximation.BinaryFraction × ℕ := by
  exact
    let counts := OAI.EditApproximation.vectorMapWithWork T fun t => OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork M Q b (scales t)
    let count := fun t => OAI.EditApproximation.bitWordValue (counts.1.get t)
    let heq : ∀ t, count t = OAI.EditApproximation.groupSampleCount M Q b (scales t).value := by
      intro t
      simp only [count, counts, OAI.EditApproximation.Lemmas.vectorMapWithWork_value, OAI.EditApproximation.Lemmas.groupSampleCountWithWork_value]
    let result := OAI.EditApproximation.BinaryFraction.groupMemberSourceWithWork scales count connection envelope values
      (fun t j => draw t (Fin.cast (heq t) j))
    (result.1, counts.2 + result.2 + 1)

theorem _root_.OAI.EditApproximation.Lemmas.lt_eq_true (a : OAI.EditApproximation.UnreducedRational) (b : OAI.EditApproximation.UnreducedRational) : a.lt b = true ↔ a.value < b.value := by
  simp only [OAI.EditApproximation.UnreducedRational.lt, decide_eq_true_eq, OAI.EditApproximation.UnreducedRational.value]
  rw [div_lt_div_iff₀ (by exact_mod_cast a.den_pos : (0 : ℚ) < a.den)
    (by exact_mod_cast b.den_pos : (0 : ℚ) < b.den)]
  exact_mod_cast (Iff.rfl : a.num * (b.den : ℤ) < b.num * (a.den : ℤ) ↔ _)

theorem _root_.OAI.EditApproximation.Lemmas.nonzeroWithWork_value (bits : List.{0} Bool) :
    (OAI.EditApproximation.SignedBinary.nonzeroWithWork bits).1 = true ↔ OAI.EditApproximation.bitWordValue bits ≠ 0 := by
  (simp [OAI.EditApproximation.SignedBinary.nonzeroWithWork, OAI.EditApproximation.Lemmas.bitCompareWithWork_eq, OAI.EditApproximation.bitWordValue])

theorem _root_.OAI.EditApproximation.Lemmas.SignedBinary.ltWithWork_value (a : OAI.EditApproximation.SignedBinary) (b : OAI.EditApproximation.SignedBinary) :
    (a.ltWithWork b).1 = true ↔ a.value < b.value := by
  cases ha : a.negative <;> cases hb : b.negative
  · (simp [OAI.EditApproximation.SignedBinary.ltWithWork, ha, hb, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude, OAI.EditApproximation.Lemmas.bitCompareWithWork_lt])
  · (simp [OAI.EditApproximation.SignedBinary.ltWithWork, ha, hb, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude])
  · (simp only [OAI.EditApproximation.SignedBinary.ltWithWork, ha, hb, ↓reduceIte, Bool.false_eq_true,
      Bool.or_eq_true, OAI.EditApproximation.Lemmas.nonzeroWithWork_value, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude])
    omega
  · (simp [OAI.EditApproximation.SignedBinary.ltWithWork, ha, hb, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude, OAI.EditApproximation.Lemmas.bitCompareWithWork_lt])

theorem _root_.OAI.EditApproximation.Lemmas.denominatorInteger_value (a : OAI.EditApproximation.BinaryFraction) :
    a.denominatorInteger.value = (OAI.EditApproximation.bitWordValue a.denominator : ℤ) := rfl

theorem _root_.OAI.EditApproximation.Lemmas.ltWithWork_representation (a : OAI.EditApproximation.BinaryFraction) (b : OAI.EditApproximation.BinaryFraction) :
    (a.ltWithWork b).1 = a.representation.lt b.representation := by
  apply Bool.eq_iff_iff.mpr
  rw [OAI.EditApproximation.Lemmas.lt_eq_true]
  simp only [OAI.EditApproximation.BinaryFraction.ltWithWork, OAI.EditApproximation.Lemmas.SignedBinary.ltWithWork_value, OAI.EditApproximation.Lemmas.mulWithWork_value,
    OAI.EditApproximation.Lemmas.denominatorInteger_value, OAI.EditApproximation.Lemmas.representation_value]
  unfold OAI.EditApproximation.BinaryFraction.value
  rw [div_lt_div_iff₀ (by exact_mod_cast a.denominator_pos : (0 : ℚ) < bitWordValue a.denominator)
    (by exact_mod_cast b.denominator_pos : (0 : ℚ) < bitWordValue b.denominator)]
  exact_mod_cast (Iff.rfl :
    a.numerator.value * (OAI.EditApproximation.bitWordValue b.denominator : ℤ) <
      b.numerator.value * (OAI.EditApproximation.bitWordValue a.denominator : ℤ) ↔ _)

theorem _root_.OAI.EditApproximation.Lemmas.BinaryFraction.ltWithWork_value (a : OAI.EditApproximation.BinaryFraction) (b : OAI.EditApproximation.BinaryFraction) :
    (a.ltWithWork b).1 = true ↔ a.value < b.value := by
  rw [OAI.EditApproximation.Lemmas.ltWithWork_representation, OAI.EditApproximation.Lemmas.lt_eq_true]
  rfl

theorem _root_.OAI.EditApproximation.Lemmas.maxWithWork_value (a : OAI.EditApproximation.BinaryFraction) (b : OAI.EditApproximation.BinaryFraction) :
    (OAI.EditApproximation.BinaryFraction.maxWithWork a b).1.value = max a.value b.value := by
  by_cases h : a.value < b.value
  · simp only [OAI.EditApproximation.BinaryFraction.maxWithWork, (OAI.EditApproximation.Lemmas.BinaryFraction.ltWithWork_value a b).mpr h, ↓reduceIte, max_eq_right h.le]
  · have hb : (a.ltWithWork b).1 = false := Bool.eq_false_iff.mpr (fun hh => h ((OAI.EditApproximation.Lemmas.BinaryFraction.ltWithWork_value a b).mp hh))
    simp only [OAI.EditApproximation.BinaryFraction.maxWithWork, hb, Bool.false_eq_true, ↓reduceIte, max_eq_left (le_of_not_gt h)]

theorem _root_.OAI.EditApproximation.Lemmas.roundedSpacingWithWork_value (theta : OAI.EditApproximation.BinaryFraction) (envelope : OAI.EditApproximation.BinaryFraction) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork theta envelope).1 = ⌈max 1 (theta.value * envelope.value)⌉₊ := by
  simp only [OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork, OAI.EditApproximation.Lemmas.naturalCeilingWithWork_value, OAI.EditApproximation.Lemmas.maxWithWork_value,
    OAI.EditApproximation.Lemmas.canonicalMulWithWork_value, OAI.EditApproximation.BinaryFraction.one, OAI.EditApproximation.Lemmas.nat_value, Nat.cast_one]

theorem _root_.OAI.EditApproximation.Lemmas.roundedSpacingWithWork_pos (theta : OAI.EditApproximation.BinaryFraction) (envelope : OAI.EditApproximation.BinaryFraction) :
    0 < OAI.EditApproximation.bitWordValue (OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork theta envelope).1 := by
  rw [OAI.EditApproximation.Lemmas.roundedSpacingWithWork_value, Nat.ceil_pos]
  exact lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (le_max_left _ _)

def roundedBandReadWithWork {n M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) (hne : band ≠ [])
    (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) : Vector (OAI.EditApproximation.TargetInterval n) M × ℕ := by
  exact
    OAI.EditApproximation.vectorMapWithWork M fun i =>
      let envelope := OAI.EditApproximation.BinaryFraction.bandEnvelopeReadWithWork b band read i
      let spacing := OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) envelope.1
      let rounded := OAI.EditApproximation.roundStateWithWork (OAI.EditApproximation.bitWordValue spacing.1)
        (OAI.EditApproximation.Lemmas.roundedSpacingWithWork_pos _ _) (band.head hne i)
      (rounded.1, envelope.2 + spacing.2 + rounded.2 + exponent + 3)

def queryGroupLabelsWithWork (M Q b : ℕ) (h : OAI.EditApproximation.BinaryFraction)
    (draw : Fin (OAI.EditApproximation.groupSampleCount M Q b h.value) → Fin M × ℕ) : List (Fin M) × ℕ := by
  exact
    let count := OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork M Q b h
    let test := OAI.EditApproximation.naturalEqualWithWork (OAI.EditApproximation.bitWordValue count.1) M
    if test.1 then (List.finRange M, count.2 + test.2 + M + 2)
    else
      let indices := OAI.EditApproximation.queryFinRange (OAI.EditApproximation.bitWordValue count.1) (OAI.EditApproximation.groupSampleCount M Q b h.value)
        (OAI.EditApproximation.Lemmas.groupSampleCountWithWork_value M Q b h)
      let labels := OAI.EditApproximation.arithmeticMapWithWork draw indices
      (labels.1, count.2 + test.2 + labels.2 + indices.length + 2)

def queryGroupLabelsAllocation (M Q b : ℕ) (h : OAI.EditApproximation.BinaryFraction)
    (_draw : Fin (OAI.EditApproximation.groupSampleCount M Q b h.value) → Fin M × ℕ)
    (allocation : Fin (OAI.EditApproximation.groupSampleCount M Q b h.value) → ℕ) : ℕ := by
  exact
    let count := (OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork M Q b h).1
    let test := (OAI.EditApproximation.naturalEqualWithWork (OAI.EditApproximation.bitWordValue count) M).1
    OAI.EditApproximation.BinaryFraction.groupSampleCountAllocation M Q b h + OAI.EditApproximation.naturalEqualAllocation (OAI.EditApproximation.bitWordValue count) M +
      if test then M else
        let indices := OAI.EditApproximation.queryFinRange (OAI.EditApproximation.bitWordValue count) (OAI.EditApproximation.groupSampleCount M Q b h.value)
          (OAI.EditApproximation.Lemmas.groupSampleCountWithWork_value M Q b h)
        OAI.EditApproximation.arithmeticMapAllocation allocation indices + 2 * indices.length

def countedGroupMemberSourceAllocation {M T : ℕ} (Q b : ℕ) (scales : Fin T → OAI.EditApproximation.BinaryFraction)
    (connection : OAI.EditApproximation.BinaryFraction) (envelope values : Vector OAI.EditApproximation.BinaryFraction M)
    (draw : ∀ t, Fin (OAI.EditApproximation.groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
    (allocation : ∀ t, Fin (OAI.EditApproximation.groupSampleCount M Q b (scales t).value) → ℕ) : ℕ := by
  exact
    let counts := OAI.EditApproximation.vectorMapWithWork T fun t => OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork M Q b (scales t)
    let count := fun t => OAI.EditApproximation.bitWordValue (counts.1.get t)
    let heq : ∀ t, count t = OAI.EditApproximation.groupSampleCount M Q b (scales t).value := by
      intro t
      simp only [count, counts, OAI.EditApproximation.Lemmas.vectorMapWithWork_value, OAI.EditApproximation.Lemmas.groupSampleCountWithWork_value]
    OAI.EditApproximation.vectorMapAllocation T (fun t => OAI.EditApproximation.BinaryFraction.groupSampleCountAllocation M Q b (scales t)) +
      OAI.EditApproximation.BinaryFraction.groupMemberSourceAllocation scales count connection envelope values (fun t j => draw t (Fin.cast (heq t) j))
        (fun t j => allocation t (Fin.cast (heq t) j))

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

def unskippedGuardReadWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (_center : OAI.EditApproximation.TargetInterval ny)
    (b exponent : ℕ) (F : OAI.EditApproximation.BinaryFraction) (band wide : List (Fin M → OAI.EditApproximation.TargetInterval ny))
    (hne : band ≠ []) (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) : Bool × ℕ :=
  let envelope := OAI.EditApproximation.BinaryFraction.envelopeVectorReadWithWork b band read
  let total := OAI.EditApproximation.BinaryFraction.bandMassTotalWithWork envelope.1
  let fb := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork F (OAI.EditApproximation.BinaryFraction.nat b)
  let limit := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 64) fb.1
  let sumGuard := OAI.EditApproximation.BinaryFraction.leWithWork total.1 limit.1
  let rounded := OAI.EditApproximation.BinaryFraction.roundedBandReadWithWork exponent b band hne read
  let wideGuard := OAI.EditApproximation.actionMemberWithWork rounded.1.get wide
  let gapGuard := OAI.EditApproximation.allWithWork (fun i =>
    let sourceLength := OAI.EditApproximation.binaryNaturalSubtractWithWork (OAI.EditApproximation.sourceChild parent i).hi (OAI.EditApproximation.sourceChild parent i).lo
    let gap := OAI.EditApproximation.BinaryFraction.stateGapWithWork (OAI.EditApproximation.bitWordValue sourceLength.1) (rounded.1.get i)
    let bound := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 2) (envelope.1.get i)
    let test := OAI.EditApproximation.BinaryFraction.leWithWork gap.1.absolute bound.1
    (test.1, sourceLength.2 + gap.2 + bound.2 + test.2 + 3)) (List.finRange M)
  (sumGuard.1 && wideGuard.1 && gapGuard.1,
    envelope.2 + total.2 + fb.2 + limit.2 + sumGuard.2 + rounded.2 + wideGuard.2 + gapGuard.2 + 5)

def queryGroupInputsWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (b exponent Q : ℕ) (cell : ℕ × ℕ) (h : OAI.EditApproximation.BinaryFraction)
    (draw : Fin (OAI.EditApproximation.groupSampleCount M Q b h.value) → Fin M × ℕ) :
    List (Fin M × OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let labels := OAI.EditApproximation.BinaryFraction.queryGroupLabelsWithWork M Q b h draw
  let inputs := OAI.EditApproximation.arithmeticFlatMapWithWork (fun i =>
    let states := OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h
    let tagged := OAI.EditApproximation.arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
    (tagged.1, states.2 + tagged.2 + 1)) labels.1
  (inputs.1, labels.2 + inputs.2 + 1)

theorem _root_.OAI.EditApproximation.Lemmas.coarseDenominatorWithWork_value (allowanceDen : List.{0} Bool) (q : List.{0} Bool) (L : List.{0} Bool) (branching : List.{0} Bool) (D : ℕ) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.coarseDenominatorWithWork allowanceDen q L branching D).1 =
      OAI.EditApproximation.coarseCommonDenominator (OAI.EditApproximation.bitWordValue allowanceDen) (OAI.EditApproximation.bitWordValue q)
        (OAI.EditApproximation.bitWordValue L) (OAI.EditApproximation.bitWordValue branching) D := by
  simp only [OAI.EditApproximation.coarseDenominatorWithWork, OAI.EditApproximation.Lemmas.trimBitWordWithWork_value,
    OAI.EditApproximation.Lemmas.bitMulWithWork_value, OAI.EditApproximation.Lemmas.bitPowerWithWork_value, OAI.EditApproximation.coarseCommonDenominator]

theorem _root_.OAI.EditApproximation.Lemmas.coarseRootDenominator_value (B : ℕ) (q : ℕ) (L : ℕ) (d : ℕ) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.BinaryFraction.coarseRootDenominator B q L d).1 = OAI.EditApproximation.coarseCommonDenominator 1 q L B d := by
  simp only [OAI.EditApproximation.BinaryFraction.coarseRootDenominator, OAI.EditApproximation.Lemmas.coarseDenominatorWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits]

theorem _root_.OAI.EditApproximation.Lemmas.coarseRootDenominator_pos (B : ℕ) (q : ℕ) (L : ℕ) (d : ℕ) (hB : LT.lt.{0} 0 B) (hq : LT.lt.{0} 0 q) (hL : LT.lt.{0} 0 L) :
    0 < OAI.EditApproximation.bitWordValue (OAI.EditApproximation.BinaryFraction.coarseRootDenominator B q L d).1 := by
  rw [OAI.EditApproximation.Lemmas.coarseRootDenominator_value]
  unfold OAI.EditApproximation.coarseCommonDenominator
  positivity

def coarseIndexedRootWithWork {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : OAI.EditApproximation.CoarseThresholdDraws B d) : OAI.EditApproximation.BinaryFraction × ℕ := by
  exact
    let den := OAI.EditApproximation.BinaryFraction.coarseRootDenominator B q L d
    let denPos := OAI.EditApproximation.Lemmas.coarseRootDenominator_pos B q L d hB hq hL
    let two := OAI.EditApproximation.BinaryFraction.coarseGridNatWithWork den.1 denPos 2
    let allowance := OAI.EditApproximation.BinaryFraction.coarseGridNatWithWork den.1 denPos k
    let evaluated := OAI.EditApproximation.BinaryFraction.coarseIndexedWithWork k q L (OAI.EditApproximation.coarseEntryWidth x y) x y two.1 d 0 draws allowance.1 0
    (OAI.EditApproximation.BinaryFraction.coarseBinaryRead evaluated.1 (OAI.EditApproximation.coarseRootShift k).val,
      den.2 + two.2 + allowance.2 + evaluated.2 + 1)

def queryGroupInputsAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (b exponent Q : ℕ) (cell : ℕ × ℕ) (h : OAI.EditApproximation.BinaryFraction)
    (draw : Fin (OAI.EditApproximation.groupSampleCount M Q b h.value) → Fin M × ℕ)
    (allocation : Fin (OAI.EditApproximation.groupSampleCount M Q b h.value) → ℕ) : ℕ :=
  let build := fun i : Fin M =>
    let states := OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h
    let tagged := OAI.EditApproximation.arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
    (tagged.1, states.2 + tagged.2 + 1)
  OAI.EditApproximation.BinaryFraction.queryGroupLabelsAllocation M Q b h draw allocation + OAI.EditApproximation.arithmeticFlatMapAllocation build
    (fun i => OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesAllocation (ny := ny) parent b exponent cell i h +
      OAI.EditApproximation.arithmeticMapAllocation (fun _ => 1) (OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1)
    (OAI.EditApproximation.BinaryFraction.queryGroupLabelsWithWork M Q b h draw).1

def unskippedGuardReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (_center : OAI.EditApproximation.TargetInterval ny) (b exponent : ℕ) (F : OAI.EditApproximation.BinaryFraction)
    (band wide : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hne : band ≠ [])
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ) : ℕ :=
  let envelope := (OAI.EditApproximation.BinaryFraction.envelopeVectorReadWithWork b band read).1
  let total := (OAI.EditApproximation.BinaryFraction.bandMassTotalWithWork envelope).1
  let fb := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork F (OAI.EditApproximation.BinaryFraction.nat b)).1
  let limit := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 64) fb).1
  let rounded := (OAI.EditApproximation.BinaryFraction.roundedBandReadWithWork exponent b band hne read).1
  OAI.EditApproximation.BinaryFraction.envelopeVectorReadAllocation b band read allocation + OAI.EditApproximation.BinaryFraction.bandMassAllocation envelope +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation F (OAI.EditApproximation.BinaryFraction.nat b) + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 64) fb + OAI.EditApproximation.BinaryFraction.leAllocation total limit +
    OAI.EditApproximation.BinaryFraction.roundedBandReadAllocation exponent b band hne read allocation + OAI.EditApproximation.actionMemberAllocation rounded.get wide +
    OAI.EditApproximation.allAllocation (OAI.EditApproximation.BinaryFraction.gapGuardAllocation parent envelope rounded) (List.finRange M)

def queryGroupInputsTransportWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (b exponent Q : ℕ) (cell : ℕ × ℕ) (word : OAI.EditApproximation.BinaryFraction) (scale : ℚ)
    (hv : word.value = scale) (draw : Fin (OAI.EditApproximation.groupSampleCount M Q b scale) → Fin M × ℕ) :
    List (Fin M × OAI.EditApproximation.TargetInterval ny) × ℕ :=
  OAI.EditApproximation.BinaryFraction.queryGroupInputsWithWork parent b exponent Q cell word
    (fun sample => draw (Fin.cast (congrArg (OAI.EditApproximation.groupSampleCount M Q b) hv) sample))

def coarseIndexedCandidateWithWork {B d : ℕ} (q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (i : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth x y)) (draws : OAI.EditApproximation.CoarseThresholdDraws B d) :
    OAI.EditApproximation.BinaryFraction × ℕ :=
  let k := OAI.EditApproximation.coarseGuess (OAI.EditApproximation.coarseEntryWidth x y) i
  let root := OAI.EditApproximation.BinaryFraction.coarseIndexedRootWithWork k q L hB hq hL x y draws
  let shifted := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork root.1 (OAI.EditApproximation.BinaryFraction.nat k)
  let doubled := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 2) shifted.1
  (doubled.1, root.2 + shifted.2 + doubled.2 + Nat.size k + 3)

def preparedUnskippedReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (center : OAI.EditApproximation.TargetInterval ny) (b P exponent : ℕ) (tau F : OAI.EditApproximation.BinaryFraction)
    (read initial : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (readAllocation initialAllocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ) : ℕ :=
  let band := (OAI.EditApproximation.BinaryFraction.preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) read).1
  OAI.EditApproximation.BinaryFraction.preparedRepresentativeReadAllocation parent center (parent.hi - parent.lo) b P
    tau (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) read readAllocation +
    if hband : band = [] then 0 else
      let wide := (OAI.EditApproximation.wideActionGridWithWork M parent center b P).1
      OAI.EditApproximation.wideActionGridAllocation M parent center b P + wide.length +
        OAI.EditApproximation.BinaryFraction.unskippedGuardReadAllocation parent center b exponent F band (wide.map Vector.get) hband initial initialAllocation +
        if (OAI.EditApproximation.BinaryFraction.unskippedGuardReadWithWork parent center b exponent F band (wide.map Vector.get) hband initial).1 then 3 else 0

def queryGroupInputsTransportAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (b exponent Q : ℕ) (cell : ℕ × ℕ) (word : OAI.EditApproximation.BinaryFraction) (scale : ℚ)
    (hv : word.value = scale) (draw : Fin (OAI.EditApproximation.groupSampleCount M Q b scale) → Fin M × ℕ)
    (allocation : Fin (OAI.EditApproximation.groupSampleCount M Q b scale) → ℕ) : ℕ :=
  OAI.EditApproximation.BinaryFraction.queryGroupInputsAllocation (ny := ny) parent b exponent Q cell word
    (fun sample => draw (Fin.cast (congrArg (OAI.EditApproximation.groupSampleCount M Q b) hv) sample))
    (fun sample => allocation (Fin.cast (congrArg (OAI.EditApproximation.groupSampleCount M Q b) hv) sample))

def preparedUnskippedReadWithWorkRaw {nx ny M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval nx) (b P exponent : ℕ) (tau F : OAI.EditApproximation.BinaryFraction)
    (read initial : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (center : OAI.EditApproximation.TargetInterval ny) : Option (OAI.EditApproximation.RawUnskippedBand M ny) × ℕ :=
  let band := OAI.EditApproximation.BinaryFraction.preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) read
  if hband : band.1 = [] then (none, band.2 + 1) else
    let wide := OAI.EditApproximation.wideActionGridWithWork M parent center b P
    let guard := OAI.EditApproximation.BinaryFraction.unskippedGuardReadWithWork parent center b exponent F band.1
      (wide.1.map Vector.get) hband initial
    if guard.1 = true then
      (some ⟨center, band.1, hband⟩, band.2 + wide.2 + guard.2 + wide.1.length + 3)
    else (none, band.2 + wide.2 + guard.2 + wide.1.length + 2)

def coarseIndexedInitialWithWork {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth x y) → OAI.EditApproximation.CoarseThresholdDraws B d) : ℕ × ℕ :=
  let long := OAI.EditApproximation.binaryNaturalCompareWithWork (2 * x.length) y.length
  if long.1 = .lt then (min N y.length, long.2 + Nat.size N + Nat.size y.length + 4) else
  let equal := OAI.EditApproximation.BinaryFraction.naturalListEqualWithWork x y
  if equal.1 then (0, long.2 + equal.2 + 3) else
  let roots := OAI.EditApproximation.arithmeticMapWithWork (fun i => OAI.EditApproximation.BinaryFraction.coarseIndexedCandidateWithWork q L hB hq hL x y i (draws i))
    (List.finRange (Nat.clog 2 (OAI.EditApproximation.coarseEntryWidth x y) + 1))
  let smallest := OAI.EditApproximation.BinaryFraction.coarseMinimumWithWork roots.1
  let rounded := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork smallest.1
  let result := OAI.EditApproximation.wordMinWithWork N.bits rounded.1
  (OAI.EditApproximation.bitWordValue result.1, long.2 + equal.2 + roots.2 + smallest.2 + rounded.2 + result.2 + Nat.size N + 6)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {ny M T : ℕ} (b exponent Q : ℕ)
  (initial current : Fin M → TargetInterval ny → BinaryFraction × ℕ)
  (initialAllocation currentAllocation : Fin M → TargetInterval ny → ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
  (drawSource : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
  (drawAllocation : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → ℕ)

def unskippedEstimateSourceWithWorkRaw (member : (OAI.EditApproximation.RawUnskippedBand M ny)) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let mass := OAI.EditApproximation.BinaryFraction.envelopeVectorReadWithWork b member.actions initial
  let rounded := OAI.EditApproximation.BinaryFraction.roundedBandReadWithWork exponent b member.actions member.nonempty initial
  let values := OAI.EditApproximation.vectorMapWithWork M fun i => current i (rounded.1.get i)
  let connection := OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork member.center rounded.1.get
  let result := OAI.EditApproximation.BinaryFraction.countedGroupMemberSourceWithWork Q b scales connection.1 mass.1 values.1 drawSource
  (result.1, mass.2 + rounded.2 + values.2 + connection.2 + result.2 + 5)

def unskippedEstimateSourceAllocationRaw (member : (OAI.EditApproximation.RawUnskippedBand M ny)) : ℕ :=
  let mass := (OAI.EditApproximation.BinaryFraction.envelopeVectorReadWithWork b member.actions initial).1
  let rounded := (OAI.EditApproximation.BinaryFraction.roundedBandReadWithWork exponent b member.actions member.nonempty initial).1
  let values := (OAI.EditApproximation.vectorMapWithWork M (fun i => current i (rounded.get i))).1
  let connection := (OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork member.center rounded.get).1
  OAI.EditApproximation.BinaryFraction.envelopeVectorReadAllocation b member.actions initial initialAllocation +
    OAI.EditApproximation.BinaryFraction.roundedBandReadAllocation exponent b member.actions member.nonempty initial initialAllocation +
    OAI.EditApproximation.vectorMapAllocation M (fun i => currentAllocation i (rounded.get i)) +
    OAI.EditApproximation.BinaryFraction.endpointConnectionAllocation member.center rounded.get + OAI.EditApproximation.BinaryFraction.countedGroupMemberSourceAllocation Q b scales connection mass values drawSource drawAllocation

def chooseUnskippedSourceWithWorkRaw (members : List (OAI.EditApproximation.RawUnskippedBand M ny)) (hne : members ≠ []) : (OAI.EditApproximation.RawUnskippedBand M ny) × ℕ :=
  OAI.EditApproximation.BinaryFraction.selectGroupWithWork members hne
    (OAI.EditApproximation.BinaryFraction.unskippedEstimateSourceWithWorkRaw b exponent Q initial current scales drawSource)

def chooseUnskippedSourceAllocationRaw (members : List (OAI.EditApproximation.RawUnskippedBand M ny)) : ℕ :=
  OAI.EditApproximation.BinaryFraction.selectGroupAllocation members
    (OAI.EditApproximation.BinaryFraction.unskippedEstimateSourceWithWorkRaw b exponent Q initial current scales drawSource)
    (OAI.EditApproximation.BinaryFraction.unskippedEstimateSourceAllocationRaw b exponent Q initial current
      initialAllocation currentAllocation scales drawSource drawAllocation)

def sampledGroupActionSourceWithWorkRaw (members : List (OAI.EditApproximation.RawUnskippedBand M ny)) (hne : members ≠ []) :
    OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval ny) (Fin M × OAI.EditApproximation.TargetInterval ny) M × ℕ :=
  let selected := OAI.EditApproximation.BinaryFraction.chooseUnskippedSourceWithWorkRaw b exponent Q initial current scales drawSource members hne
  let rounded := OAI.EditApproximation.BinaryFraction.roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
  let result := OAI.EditApproximation.BinaryFraction.endpointActionWithWork selected.1.center rounded.1.get
  (result.1, selected.2 + rounded.2 + result.2 + 3)

def sampledGroupActionSourceAllocationRaw (members : List (OAI.EditApproximation.RawUnskippedBand M ny)) (hne : members ≠ []) : ℕ :=
  let selected := (OAI.EditApproximation.BinaryFraction.chooseUnskippedSourceWithWorkRaw b exponent Q initial current
    scales drawSource members hne).1
  let rounded := (OAI.EditApproximation.BinaryFraction.roundedBandReadWithWork exponent b selected.actions selected.nonempty initial).1
  OAI.EditApproximation.BinaryFraction.chooseUnskippedSourceAllocationRaw b exponent Q initial current
    initialAllocation currentAllocation scales drawSource drawAllocation members +
    OAI.EditApproximation.BinaryFraction.roundedBandReadAllocation exponent b selected.actions selected.nonempty initial initialAllocation +
    OAI.EditApproximation.BinaryFraction.endpointActionAllocation selected.center rounded.get

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

open Finset

theorem _root_.OAI.EditApproximation.Lemmas.onlineIndexSetupWithWork_value {M : ℕ} {n : ℕ} (H : ℕ) (band : List.{0} (Fin M → OAI.EditApproximation.TargetInterval n)) :
    (OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork H band).1 = H + (OAI.EditApproximation.listedBandCoordinates band).length + 2 := by
  simp only [OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork, OAI.EditApproximation.Lemmas.binaryNaturalAddWithWork_value, OAI.EditApproximation.Lemmas.bandCoordinatesWithWork_value]

def preparedOnlineReadWithWorkRaw {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (P F exponent H b : ℕ) (_hb : 0 < b) (_hP : 0 < P)
    (tau eta kappa : OAI.EditApproximation.BinaryFraction)
    (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (table : ℕ → Fin M × OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (R : ℕ) (_hc : ∀ i q, (child i q).2 ≤ R) (_hi : ∀ i q, (initial i q).2 ≤ R)
    (t : ℕ) (center : OAI.EditApproximation.TargetInterval target.length) (integer : ℕ) :
    Option (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
      (Fin M × OAI.EditApproximation.TargetInterval target.length) M) × ℕ := by
  exact
    let band := OAI.EditApproximation.BinaryFraction.preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
      tau (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) child
    let setup := OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork H band.1
    let G := setup.1
    let accepted := OAI.EditApproximation.BinaryFraction.reduceOnlineIntegerWithWork (G ^ 80) (by
      dsimp only [G, setup]
      rw [OAI.EditApproximation.Lemmas.onlineIndexSetupWithWork_value]
      positivity) integer
    if hband : band.1 = [] then (none, band.2 + setup.2 + accepted.2 + 1) else
      let guard := OAI.EditApproximation.BinaryFraction.preparedUnskippedReadWithWorkRaw parent b P exponent tau (OAI.EditApproximation.BinaryFraction.nat F) child initial center
      if guard.1.isSome then
        let sampled := OAI.EditApproximation.BinaryFraction.countedSampledOnlineReadWithWork center b initial table eta kappa band.1 hband
          G (G ^ 80) t accepted.1
        (some sampled.1, band.2 + setup.2 + accepted.2 + guard.2 + sampled.2 + 2)
      else (none, band.2 + setup.2 + accepted.2 + guard.2 + 1)

def preparedOnlineReadAllocationRaw {α : Type u_1} (source target : List α) {M : ℕ}
  (parent : OAI.EditApproximation.TargetInterval source.length) (P F exponent H b : ℕ) (_hb : 0 < b) (_hP : 0 < P)
  (tau eta kappa : OAI.EditApproximation.BinaryFraction)
  (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
  (table : ℕ → Fin M × OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
  (R : ℕ) (_hc : ∀ i q, (child i q).2 ≤ R) (_hi : ∀ i q, (initial i q).2 ≤ R)
  (childAllocation initialAllocation : Fin M → OAI.EditApproximation.TargetInterval target.length → ℕ)
  (tableAllocation : ℕ → Fin M × OAI.EditApproximation.TargetInterval target.length → ℕ)


    (t : ℕ) (center : OAI.EditApproximation.TargetInterval target.length) (integer : ℕ) : ℕ := by
  exact
    let band := (OAI.EditApproximation.BinaryFraction.preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
      tau (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) child).1
    let G := (OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork H band).1
    let accepted := (OAI.EditApproximation.BinaryFraction.reduceOnlineIntegerWithWork (G ^ 80) (by
      dsimp only [G]; rw [OAI.EditApproximation.Lemmas.onlineIndexSetupWithWork_value]; positivity) integer).1
    OAI.EditApproximation.BinaryFraction.preparedRepresentativeReadAllocation parent center (parent.hi - parent.lo) b P
      tau (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) child childAllocation +
      OAI.EditApproximation.BinaryFraction.onlineIndexSetupAllocation H band + OAI.EditApproximation.reduceOnlineIntegerAllocation (G ^ 80) integer +
      if hband : band = [] then 0 else
        OAI.EditApproximation.BinaryFraction.preparedUnskippedReadAllocation parent center b P exponent tau (OAI.EditApproximation.BinaryFraction.nat F)
          child initial childAllocation initialAllocation +
        if (OAI.EditApproximation.BinaryFraction.preparedUnskippedReadWithWorkRaw parent b P exponent tau (OAI.EditApproximation.BinaryFraction.nat F) child initial center).1.isSome then
          OAI.EditApproximation.BinaryFraction.countedSampledOnlineAllocation center b initial initialAllocation table tableAllocation eta kappa
            band hband G (G ^ 80) t accepted + 1
        else 0

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditDistortion

inductive Step (substitutions : Bool) {Alpha : Type u} : List Alpha → List Alpha → Prop
  | insert (p q : List Alpha) (a : Alpha) : Step substitutions (p ++ q) (p ++ a :: q)
  | delete (p q : List Alpha) (a : Alpha) : Step substitutions (p ++ a :: q) (p ++ q)
  | substitute (h : substitutions = true) (p q : List Alpha) (a b : Alpha) :
      Step substitutions (p ++ a :: q) (p ++ b :: q)

inductive Script (substitutions : Bool) {Alpha : Type u} : ℕ → List Alpha → List Alpha → Prop
  | nil (x : List Alpha) : Script substitutions 0 x x
  | cons {n : ℕ} {x y z : List Alpha} (first : OAI.EditDistortion.Step substitutions x y)
      (rest : Script substitutions n y z) : Script substitutions (n + 1) x z

noncomputable def edit {Alpha : Type u} (x y : List Alpha) : ℕ :=
  sInf {n | Script true n x y}

end OAI.EditDistortion

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditDistortion

variable {Alpha : Type u} {s : Bool}

noncomputable def cost (s : Bool) (x y : List Alpha) : ℕ := sInf {n | Script s n x y}

end OAI.EditDistortion

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.CoarseSourceTree

open Finset EditDistortion

def word {B : ℕ} {α : Type u} : {D : ℕ} → OAI.EditApproximation.CoarseSourceTree B α D → List α
  | _, .leaf letter => letter.toList
  | _, .branch children => (List.ofFn fun i => word (children i)).flatten

end OAI.EditApproximation.CoarseSourceTree

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def coarseLabelCount {B : ℕ} {α : Type u_1} (Q lam : ℚ) :
    {d : ℕ} → OAI.EditApproximation.CoarseSourceTree B α d → OAI.EditApproximation.CoarseThresholdDraws B d → ℚ → ℕ
  | _, tree, draws, allowance =>
    if (tree.word.length : ℚ) ≤ allowance then 0 else
    match tree, draws with
    | .leaf _, _ => 0
    | .branch children, (draws, below) => B +
      OAI.EditApproximation.coarseLabelChildren Q lam allowance (fun child => coarseLabelCount Q lam child)
        (List.ofFn fun i => (children i, draws i, below i))

def coarseIndexedEntryBinaryCost (N B d : ℕ) [NeZero B] (x y : List ℕ)
    (draws : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth x y) → OAI.EditApproximation.CoarseThresholdDraws B d) : ℕ :=
  (OAI.EditApproximation.BinaryFraction.coarseIndexedInitialWithWork (OAI.EditApproximation.inputHeight N ^ 4) (64 * OAI.EditApproximation.inputHeight N) N
    (Nat.pos_of_neZero B) (pow_pos (Nat.two_pow_pos _) _)
    (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) x y draws).2

def coarseInitialLabelCount {α : Type u_1} [DecidableEq α]
    (B d : ℕ) (Q lam : ℚ) (x y : List α)
    (draws : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth x y) → OAI.EditApproximation.CoarseThresholdDraws B d) : ℕ :=
  if 2 * x.length < y.length then 0
  else if x = y then 0
  else ∑ i, OAI.EditApproximation.coarseLabelCount Q lam (OAI.EditApproximation.coarseEntryTree B d x y) (draws i)
    (OAI.EditApproximation.coarseGuess (OAI.EditApproximation.coarseEntryWidth x y) i)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset EditDistortion

def coarseChildrenCost {B D : ℕ} {α : Type u} (k : ℕ)
    (value : OAI.EditApproximation.CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ) :
    List (OAI.EditApproximation.CoarseSourceTree B α D) → ℕ → Fin (2 * k + 1) → ℕ
  | [], _, _ => 0
  | child :: rest, start, shift =>
    univ.inf' univ_nonempty (fun next => value child start next + 2 * Nat.dist shift.val next.val) +
      coarseChildrenCost k value rest (start + child.word.length) shift

def coarseShiftCost {B : ℕ} {α : Type u} [DecidableEq α] (k : ℕ) (frame : List (Option α)) :
    {D : ℕ} → OAI.EditApproximation.CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ
  | _, .leaf none, _, _ => 0
  | _, .leaf (some letter), start, shift =>
    if (frame[start + shift.val]?.getD none) = some letter then 0 else 1
  | _, .branch children, start, shift =>
    OAI.EditApproximation.coarseChildrenCost k (fun child => coarseShiftCost k frame child)
      (List.ofFn children) start shift

end OAI.EditApproximation

end



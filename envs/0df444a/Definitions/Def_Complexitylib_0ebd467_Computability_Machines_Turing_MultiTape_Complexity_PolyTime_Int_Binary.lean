-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Int_Binary
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Int_Binary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:45.932019+00:00
-- url     : https://prove2.me/theorems/7be3fb3c-c9f8-48c5-852a-ce15b3ecac6f
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary — Polynomial-time arithmetic on binary integers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Polynomial-time certificates for arithmetic on the binary sign-magnitude integers
--   `Turing.MultiTapeTM.encIntBin`. The sign bit and the magnitude are read off the code directly. Every
--   other operation is an ordinary functional program over the sign and the magnitude, by cases on
--   the signs, built from the binary natural arithmetic of
--   `Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Binary.lean`; no new
--   machine
--   is involved. A result is assembled from a sign and a magnitude by
--   `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_signMagnitude`, which clears the sign of a
--   zero magnitude. Integers of equal sign add their magnitudes; otherwise the smaller magnitude is
--   subtracted from the larger one, which keeps its sign. A product multiplies the magnitudes, and is
--   negative when exactly one factor is. Lists are summed and powers taken by left folds, with
--   the binary length bounds of `Int.size_natAbs_add_le` and `Int.size_natAbs_mul_le`.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime.intBin_mul'`: multiply two plain-certified binary
--     integers from the same complete input encoding.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.intBin_prod_range`: the product of a plain-certified
--     family of binary integers over a computed unary range.
--
--   * `Int.size_natAbs_add_le`, `Int.size_natAbs_sub_le`, `Int.size_natAbs_mul_le`,
--     `Int.size_natAbs_pow_le`, `Int.size_natAbs_sum_le`, `Int.size_natAbs_prod_le`: binary lengths of
--     magnitudes of sums, differences, products, powers, list sums and list products.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_isNeg`, `.intBin_natAbs`: the sign and the
--     binary magnitude.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_signMagnitude`, `.intBin_natCast`: integers
--     from a sign and a binary magnitude, and from binary naturals.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_isZero`, `.intBin_isPos`, `.intBin_sign`,
--     `.intBin_toNat`: sign tests, the sign and truncation at zero.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_neg`, `.intBin_add`, `.intBin_sub`,
--     `.intBin_mul`, `.intBin_pow`: ring operations, powers to a unary exponent.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_lt`, `.intBin_le`: comparisons.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_sum`, `.intBin_prod`: the sum and product
--     of a list.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_add'`, `.intBin_sub'`, `.intBin_mul'`,
--     `.intBin_pow'`, `.intBin_lt'`, `.intBin_le'`: composition rules for `fun_prop`.
--
--   **Contents.** The module is published as a whole: 35 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Int_Binary`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Int/Binary.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_IntBinary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
import Mathlib.Algebra.BigOperators.Group.List.Basic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time arithmetic on binary integers

Polynomial-time certificates for arithmetic on the binary sign-magnitude integers
`Turing.MultiTapeTM.encIntBin`. The sign bit and the magnitude are read off the code directly. Every
other operation is an ordinary functional program over the sign and the magnitude, by cases on
the signs, built from the binary natural arithmetic of
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Binary.lean`; no new
machine
is involved. A result is assembled from a sign and a magnitude by
`Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_signMagnitude`, which clears the sign of a
zero magnitude. Integers of equal sign add their magnitudes; otherwise the smaller magnitude is
subtracted from the larger one, which keeps its sign. A product multiplies the magnitudes, and is
negative when exactly one factor is. Lists are summed and powers taken by left folds, with
the binary length bounds of `Int.size_natAbs_add_le` and `Int.size_natAbs_mul_le`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_mul'`: multiply two plain-certified binary
  integers from the same complete input encoding.
* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_prod_range`: the product of a plain-certified
  family of binary integers over a computed unary range.

* `Int.size_natAbs_add_le`, `Int.size_natAbs_sub_le`, `Int.size_natAbs_mul_le`,
  `Int.size_natAbs_pow_le`, `Int.size_natAbs_sum_le`, `Int.size_natAbs_prod_le`: binary lengths of
  magnitudes of sums, differences, products, powers, list sums and list products.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_isNeg`, `.intBin_natAbs`: the sign and the
  binary magnitude.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_signMagnitude`, `.intBin_natCast`: integers
  from a sign and a binary magnitude, and from binary naturals.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_isZero`, `.intBin_isPos`, `.intBin_sign`,
  `.intBin_toNat`: sign tests, the sign and truncation at zero.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_neg`, `.intBin_add`, `.intBin_sub`,
  `.intBin_mul`, `.intBin_pow`: ring operations, powers to a unary exponent.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_lt`, `.intBin_le`: comparisons.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_sum`, `.intBin_prod`: the sum and product
  of a list.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_add'`, `.intBin_sub'`, `.intBin_mul'`,
  `.intBin_pow'`, `.intBin_lt'`, `.intBin_le'`: composition rules for `fun_prop`.
-/

@[expose] public section

namespace Int

/-- The magnitude of a sum is at most one binary digit longer than the longer magnitude of the
summands. -/
theorem size_natAbs_add_le (a b : ℤ) :
    (a + b).natAbs.size ≤ max a.natAbs.size b.natAbs.size + 1 :=
  (Nat.size_le_size (Int.natAbs_add_le a b)).trans (Nat.size_add_le_max _ _)

/-- The magnitude of a difference is at most one binary digit longer than the longer magnitude of
the operands. -/
theorem size_natAbs_sub_le (a b : ℤ) :
    (a - b).natAbs.size ≤ max a.natAbs.size b.natAbs.size + 1 :=
  (Nat.size_le_size (Int.natAbs_sub_le a b)).trans (Nat.size_add_le_max _ _)

/-- The magnitude of a product is at most as long as the magnitudes of the factors together. -/
theorem size_natAbs_mul_le (a b : ℤ) : (a * b).natAbs.size ≤ a.natAbs.size + b.natAbs.size := by
  rw [Int.natAbs_mul]
  exact Nat.size_mul_le _ _

/-- The magnitude of a power is at most the exponent times the magnitude of the base, plus one
for the zeroth power. -/
theorem size_natAbs_pow_le (a : ℤ) (k : ℕ) : (a ^ k).natAbs.size ≤ k * a.natAbs.size + 1 := by
  rw [Int.natAbs_pow]
  exact Nat.size_pow_le _ _

/-- A sum of integers whose magnitudes have binary length at most `b` has a magnitude of binary
length at most `b` plus the binary length of the number of summands. -/
theorem size_natAbs_sum_le {l : List ℤ} {b : ℕ} (h : ∀ z ∈ l, z.natAbs.size ≤ b) :
    l.sum.natAbs.size ≤ b + l.length.size := by
  have habs (l : List ℤ) : l.sum.natAbs ≤ (l.map Int.natAbs).sum := by
    induction l with
    | nil => simp
    | cons z l ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)
  have hsum := Nat.size_sum_le (l := l.map Int.natAbs) (b := b) (by simpa using h)
  rw [List.length_map] at hsum
  exact (Nat.size_le_size (habs l)).trans hsum

/-- A product of integers has a magnitude of binary length at most the sum of the binary lengths
of the magnitudes of the factors, plus one for the empty product. -/
theorem size_natAbs_prod_le (l : List ℤ) :
    l.prod.natAbs.size ≤ (l.map fun z => z.natAbs.size).sum + 1 := by
  induction l with
  | nil => simp
  | cons z l ih =>
    have := size_natAbs_mul_le z l.prod
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    lia

end Int

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The sign of a binary integer: whether it is negative. -/
@[fun_prop]
theorem intBin_isNeg :
    ComputableTidilyInPolyTime (fun z : ℤ => decide (z < 0)) encIntBin encBool :=
  ((headD (encA := encBool) (encL := encBits) false).comp (encode encIntBin)).of_enc_eq
    fun z => by simp

/-- The magnitude of a binary integer, as a binary natural. -/
@[fun_prop]
theorem intBin_natAbs : ComputableTidilyInPolyTime Int.natAbs encIntBin encNat :=
  (bitsTail.comp (encode encIntBin)).of_enc_eq fun z => by simp

/-- Assemble a binary integer from a sign and a binary magnitude. A negative sign on a zero
magnitude is dropped, so the code stays unique. -/
@[fun_prop]
theorem intBin_signMagnitude :
    ComputableTidilyInPolyTime (fun p : Bool × ℕ => if p.1 then -(p.2 : ℤ) else p.2)
      (encPair encBool encNat) encIntBin := by
  have h : ComputableTidilyInPolyTime (fun p : Bool × ℕ => (p.1 && !p.2.bits.isEmpty) :: p.2.bits)
      (encPair encBool encNat) encBits := by
    fun_prop
  refine h.of_enc_eq fun ⟨s, n⟩ => ?_
  have hbits : n.bits.isEmpty = decide (n = 0) := by
    rw [Bool.eq_iff_iff, List.isEmpty_iff, decide_eq_true_eq, ← List.length_eq_zero_iff,
      Nat.size_eq_bits_len, Nat.size_eq_zero]
  cases s <;> simp [hbits, Nat.pos_iff_ne_zero]

/-- A binary natural as a binary integer. -/
@[fun_prop]
theorem intBin_natCast : ComputableTidilyInPolyTime (fun n : ℕ => (n : ℤ)) encNat encIntBin :=
  (bitsCons (const false) (encode encNat)).of_enc_eq fun n => by simp

/-- Negation of binary integers flips the sign of a nonzero magnitude. -/
@[fun_prop]
theorem intBin_neg : ComputableTidilyInPolyTime (fun z : ℤ => -z) encIntBin encIntBin := by
  have h := intBin_signMagnitude.comp ((bool_not.comp intBin_isNeg).prod intBin_natAbs)
  refine h.of_enc_eq fun z => congrArg encIntBin ?_
  by_cases hz : z < 0 <;> simp only [Function.comp_apply, hz, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;> lia

/-- Addition of binary integers, by cases on the signs of the summands. -/
@[fun_prop]
theorem intBin_add : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => p.1 + p.2)
    (encPair encIntBin encIntBin) encIntBin := by
  have hsa := intBin_isNeg.comp (fst encIntBin encIntBin)
  have hsb := intBin_isNeg.comp (snd encIntBin encIntBin)
  have hma := intBin_natAbs.comp (fst encIntBin encIntBin)
  have hmb := intBin_natAbs.comp (snd encIntBin encIntBin)
  have h := (bool_beq.comp (hsa.prod hsb)).ite'
    (intBin_signMagnitude.comp (hsa.prod (binary_add.comp (hma.prod hmb))))
    ((binary_le.comp (hmb.prod hma)).ite'
      (intBin_signMagnitude.comp (hsa.prod (binary_sub.comp (hma.prod hmb))))
      (intBin_signMagnitude.comp (hsb.prod (binary_sub.comp (hmb.prod hma)))))
  refine h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin ?_
  simp only [Function.comp_apply]
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;>
    simp only [ha, hb, decide_true, decide_false, beq_self_eq_true, Bool.true_beq,
      Bool.false_beq, Bool.not_true, Bool.false_eq_true, decide_eq_true_eq, ↓reduceIte] <;>
    (try split_ifs) <;> lia

/-- Multiplication of binary integers: the magnitudes multiply, and the product is negative when
exactly one factor is. -/
@[fun_prop]
theorem intBin_mul : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => p.1 * p.2)
    (encPair encIntBin encIntBin) encIntBin := by
  have hsa := intBin_isNeg.comp (fst encIntBin encIntBin)
  have hsb := intBin_isNeg.comp (snd encIntBin encIntBin)
  have hma := intBin_natAbs.comp (fst encIntBin encIntBin)
  have hmb := intBin_natAbs.comp (snd encIntBin encIntBin)
  have h := intBin_signMagnitude.comp
    ((bool_xor.comp (hsa.prod hsb)).prod (binary_mul.comp (hma.prod hmb)))
  refine h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin ?_
  simp only [Function.comp_apply, Nat.cast_mul, Int.natCast_natAbs]
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;>
    simp only [ha, hb, decide_true, decide_false, Bool.xor_true, Bool.xor_false, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  · rw [abs_of_neg ha, abs_of_neg hb]
    ring
  · rw [abs_of_neg ha, abs_of_nonneg (not_lt.1 hb)]
    ring
  · rw [abs_of_nonneg (not_lt.1 ha), abs_of_neg hb]
    ring
  · rw [abs_of_nonneg (not_lt.1 ha), abs_of_nonneg (not_lt.1 hb)]

/-- Subtraction of binary integers, as addition of the negation. -/
@[fun_prop]
theorem intBin_sub : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => p.1 - p.2)
    (encPair encIntBin encIntBin) encIntBin := by
  simpa only [Function.comp_def, ← sub_eq_add_neg] using
    intBin_add.comp ((fst encIntBin encIntBin).prod (intBin_neg.comp (snd encIntBin encIntBin)))

/-- Test whether a binary integer is zero: its magnitude has no digits. -/
@[fun_prop]
theorem intBin_isZero :
    ComputableTidilyInPolyTime (fun z : ℤ => decide (z = 0)) encIntBin encBool := by
  refine (bitsIsEmpty.comp (natBits.comp intBin_natAbs)).of_enc_eq fun z => congrArg encBool ?_
  rw [Function.comp_apply, Function.comp_apply, Bool.eq_iff_iff, decide_eq_true_eq,
    List.isEmpty_iff, ← List.length_eq_zero_iff, Nat.size_eq_bits_len, Nat.size_eq_zero,
    Int.natAbs_eq_zero]

/-- Test whether a binary integer is positive. -/
@[fun_prop]
theorem intBin_isPos :
    ComputableTidilyInPolyTime (fun z : ℤ => decide (0 < z)) encIntBin encBool := by
  refine (bool_and.comp ((bool_not.comp intBin_isNeg).prod (bool_not.comp intBin_isZero)))
    |>.of_enc_eq fun z => congrArg encBool ?_
  by_cases hz : 0 < z
  · simp only [Function.comp_apply, hz, decide_true]
    rw [decide_eq_false (by lia), decide_eq_false (by lia)]
    rfl
  · rw [decide_eq_false hz]
    by_cases hz' : z = 0
    · simp [hz']
    · simp only [Function.comp_apply, decide_eq_true (show z < 0 by lia), Bool.not_true,
        Bool.false_and]

/-- The sign of a binary integer, as a binary integer. -/
@[fun_prop]
theorem intBin_sign : ComputableTidilyInPolyTime Int.sign encIntBin encIntBin := by
  refine (intBin_isNeg.ite' (const (-1)) (intBin_isZero.ite' (const 0) (const 1))).of_enc_eq
    fun z => congrArg encIntBin ?_
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · simp [hz, Int.sign_eq_neg_one_of_neg hz]
  · simp
  · simp [Int.sign_eq_one_of_pos hz, hz.ne', not_lt.2 hz.le]

/-- Truncate a binary integer at zero, as a binary natural. -/
@[fun_prop]
theorem intBin_toNat : ComputableTidilyInPolyTime Int.toNat encIntBin encNat := by
  refine (intBin_isNeg.ite' (const 0) intBin_natAbs).of_enc_eq fun z => congrArg encNat ?_
  by_cases hz : z < 0
  · simp only [hz, decide_true, ↓reduceIte]
    lia
  · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte]
    lia

/-- Strict comparison of binary integers, through the sign of their difference. -/
@[fun_prop]
theorem intBin_lt : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => decide (p.1 < p.2))
    (encPair encIntBin encIntBin) encBool :=
  (intBin_isNeg.comp intBin_sub).of_enc_eq fun p => congrArg encBool (by simp [sub_neg])

/-- Comparison of binary integers. -/
@[fun_prop]
theorem intBin_le : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => decide (p.1 ≤ p.2))
    (encPair encIntBin encIntBin) encBool :=
  (bool_not.comp (intBin_lt.comp ((snd encIntBin encIntBin).prod (fst encIntBin encIntBin))))
    |>.of_enc_eq fun p => congrArg encBool (by
      simp only [Function.comp_apply, ← decide_not, not_lt])

/-- A power of a binary integer to a unary exponent, by repeated multiplication. -/
@[fun_prop]
theorem intBin_pow : ComputableTidilyInPolyTime (fun p : ℤ × ℕ => p.1 ^ p.2)
    (encPair encIntBin encUnary) encIntBin := by
  have hfold (z : ℤ) (k : ℕ) : (List.replicate k true).foldl (fun w _ => w * z) 1 = z ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ', List.foldl_append, ih, List.foldl_cons, List.foldl_nil, pow_succ]
  have hlist : ComputableTidilyInPolyTime (fun p : ℤ × ℕ => List.replicate p.2 true)
      (encPair encIntBin encUnary) encBits :=
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl).comp (snd encIntBin encUnary)
  have hq := fst (encPair encIntBin encIntBin) encBool
  have h := foldlWith_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encIntBin)
    (par := fun p : ℤ × ℕ => p.1) (step := fun z w _ => w * z) (init := fun _ => 1)
    (fst encIntBin encUnary) hlist (const 1) (intBin_mul.comp (hq.snd'.prod hq.fst'))
    (growth := fun p => (encPair encIntBin encUnary p).length) .self
    (fun p w _ _ => by
      have := Int.size_natAbs_mul_le w p.1
      have := length_le_encPair_left encIntBin encUnary p
      simp only [length_encIntBin] at this ⊢
      lia)
  simpa only [hfold] using h

/-- The sum of a list of binary integers, by a left fold of binary additions. -/
@[fun_prop]
theorem intBin_sum : ComputableTidilyInPolyTime List.sum (encList encIntBin) encIntBin := by
  have hq := fst (encPair (encList encIntBin) encIntBin) encIntBin
  have h := foldlWith_of_bounded_growth (encA := encIntBin) (encL := encList encIntBin)
    (encB := encIntBin) (par := fun l : List ℤ => l) (list := fun l => l)
    (step := fun _ s a => s + a) id' id' (const 0) (intBin_add.comp (hq.snd'.prod (snd _ _)))
    (growth := fun l => (encList encIntBin l).length) .self
    (fun l s a ha => by
      have hmem := length_le_encList_of_mem encIntBin ha
      have := Int.size_natAbs_add_le s a
      simp only [length_encIntBin] at hmem ⊢
      lia)
  simpa only [← List.sum_eq_foldl] using h

/-- The product of a list of binary integers, by a left fold of binary multiplications. -/
@[fun_prop]
theorem intBin_prod : ComputableTidilyInPolyTime List.prod (encList encIntBin) encIntBin := by
  have hq := fst (encPair (encList encIntBin) encIntBin) encIntBin
  have h := foldlWith_of_bounded_growth (encA := encIntBin) (encL := encList encIntBin)
    (encB := encIntBin) (par := fun l : List ℤ => l) (list := fun l => l)
    (step := fun _ s a => s * a) id' id' (const 1) (intBin_mul.comp (hq.snd'.prod (snd _ _)))
    (growth := fun l => (encList encIntBin l).length) .self
    (fun l s a ha => by
      have hmem := length_le_encList_of_mem encIntBin ha
      have := Int.size_natAbs_mul_le s a
      simp only [length_encIntBin] at hmem ⊢
      lia)
  simpa only [← List.prod_eq_foldl] using h

/-- Add computed binary integers, fixing their intermediate encodings for proof search. -/
@[fun_prop]
theorem intBin_add' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableTidilyInPolyTime left input encIntBin)
    (hright : ComputableTidilyInPolyTime right input encIntBin) :
    ComputableTidilyInPolyTime (fun a => left a + right a) input encIntBin :=
  intBin_add.comp (hleft.prod hright)

/-- Subtract computed binary integers, fixing their intermediate encodings. -/
@[fun_prop]
theorem intBin_sub' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableTidilyInPolyTime left input encIntBin)
    (hright : ComputableTidilyInPolyTime right input encIntBin) :
    ComputableTidilyInPolyTime (fun a => left a - right a) input encIntBin :=
  intBin_sub.comp (hleft.prod hright)

/-- Multiply computed binary integers, fixing their intermediate encodings. -/
@[fun_prop]
theorem intBin_mul' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableTidilyInPolyTime left input encIntBin)
    (hright : ComputableTidilyInPolyTime right input encIntBin) :
    ComputableTidilyInPolyTime (fun a => left a * right a) input encIntBin :=
  intBin_mul.comp (hleft.prod hright)

/-- Raise a computed binary integer to a computed unary exponent, fixing the intermediate
encodings. -/
@[fun_prop]
theorem intBin_pow' {α : Type} {input : α ↪ List Bool} {base : α → ℤ} {exponent : α → ℕ}
    (hbase : ComputableTidilyInPolyTime base input encIntBin)
    (hexponent : ComputableTidilyInPolyTime exponent input encUnary) :
    ComputableTidilyInPolyTime (fun a => base a ^ exponent a) input encIntBin :=
  intBin_pow.comp (hbase.prod hexponent)

/-- Strictly compare computed binary integers, fixing their intermediate encodings. -/
@[fun_prop]
theorem intBin_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableTidilyInPolyTime left input encIntBin)
    (hright : ComputableTidilyInPolyTime right input encIntBin) :
    ComputableTidilyInPolyTime (fun a => decide (left a < right a)) input encBool :=
  intBin_lt.comp (hleft.prod hright)

/-- Compare computed binary integers, fixing their intermediate encodings. -/
@[fun_prop]
theorem intBin_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableTidilyInPolyTime left input encIntBin)
    (hright : ComputableTidilyInPolyTime right input encIntBin) :
    ComputableTidilyInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  intBin_le.comp (hleft.prod hright)

/-- Multiply a uniformly computed family of binary integers over a computed unary range. -/
@[fun_prop]
theorem intBin_prod_range {α : Type} {enc : α ↪ List Bool}
    {f : α × ℕ → ℤ} {r : α → ℕ}
    (hf : ComputableTidilyInPolyTime f (encPair enc encUnary) encIntBin)
    (hr : ComputableTidilyInPolyTime r enc encUnary) :
    ComputableTidilyInPolyTime (fun a => ∏ i ∈ Finset.range (r a), f (a, i)) enc encIntBin := by
  have hl : ComputableTidilyInPolyTime
      (fun a => (List.range (r a)).map fun i => f (a, i)) enc (encList encIntBin) :=
    ComputableTidilyInPolyTime.mapWithInput (ComputableTidilyInPolyTime.range.comp hr) hf
  convert ComputableTidilyInPolyTime.intBin_prod.comp hl using 1
  funext a
  have he : (List.range (r a)).toFinset = Finset.range (r a) := by ext; simp
  simpa only [he, Function.comp_apply] using
    List.prod_toFinset (fun i => f (a, i)) (l := List.range (r a)) List.nodup_range

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Multiply computed binary integers, preserving the complete input encoding. -/
@[fun_prop]
theorem intBin_mul' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => left a * right a) input encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_mul' hleft.tidy hright.tidy)

/-- The cast of a binary natural number to a binary integer. -/
theorem intBin_natCast : ComputableInPolyTime (fun n : ℕ => (n : ℤ)) encNat encIntBin :=
  .of_tidy ComputableTidilyInPolyTime.intBin_natCast

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_toNat` for plain certificates. -/
theorem intBin_toNat : ComputableInPolyTime Int.toNat encIntBin encNat :=
  .of_tidy ComputableTidilyInPolyTime.intBin_toNat

/-- `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_sub` for plain certificates. -/
theorem intBin_sub : ComputableInPolyTime (fun p : ℤ × ℤ => p.1 - p.2)
    (encPair encIntBin encIntBin) encIntBin :=
  .of_tidy ComputableTidilyInPolyTime.intBin_sub

/-- `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_prod_range` for plain certificates. -/
@[fun_prop]
theorem intBin_prod_range {α : Type} {enc : α ↪ List Bool}
    {f : α × ℕ → ℤ} {r : α → ℕ}
    (hf : ComputableInPolyTime f (encPair enc encUnary) encIntBin)
    (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime (fun a => ∏ i ∈ Finset.range (r a), f (a, i)) enc encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_prod_range hf.tidy hr.tidy)

end Turing.MultiTapeTM.ComputableInPolyTime



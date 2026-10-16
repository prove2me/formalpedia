-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
-- name    : MIPRE_Foundations_ValueApprox_RawInt
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:05:46.586918+00:00
-- url     : https://prove2.me/theorems/bd928cfb-ad87-417e-8be4-b016a28a37a1
-- title:
--   Integers and Gaussian integers as pairs of naturals, with primitive recursive arithmetic
-- statement:
--   Mathlib's `Primrec` has no arithmetic on $\mathbb{Z}$ (and no `Primcodable ℤ`), so the enumeration behind `lem:value-lower-approx` carries its integers as pairs of natural numbers. This bundle fixes that representation and its arithmetic; every function in it is primitive recursive, with the proof next to the definition.
--
--   **Integers.** `MIPRE.ValueApprox.PInt` is `ℕ × ℕ`, the pair $(a, b)$ denoting $a - b$, and `PInt.toInt (a, b) = a - b` in $\mathbb{Z}$. The operations are `PInt.zero = (0, 0)`, `PInt.ofNat n = (n, 0)`, `PInt.ofInt m = (m.toNat, (-m).toNat)`, `PInt.add (a,b) (c,d) = (a+c, b+d)`, `PInt.neg (a,b) = (b,a)`, `PInt.mul (a,b) (c,d) = (ac+bd, ad+bc)`, and `PInt.sum`, the fold of `add` over a list. Equality and order are the semantic ones, `PInt.Eq' x y` $\iff x_1 + y_2 = y_1 + x_2$ and `PInt.Lt' x y` $\iff x_1 + y_2 < y_1 + x_2$, with the instances `PInt.instDecidableRelEq'` and `PInt.instDecidableRelLt'`.
--
--   **Gaussian integers.** `MIPRE.ValueApprox.GInt` is `PInt × PInt`, the pair $(m, n)$ denoting $m + n i$, and `GInt.toC z` is the complex number $\mathrm{toInt}(z_1) + \mathrm{toInt}(z_2)\, i$. The operations are `GInt.zero`, `GInt.ofNat n`, `GInt.ofInt m n` (the two integer parts), componentwise `GInt.add`, the product `GInt.mul` computed as
--   $$(m + n i)(m' + n' i) = (mm' - nn') + (mn' + nm')\, i,$$
--   the conjugate `GInt.conj (m, n) = (m, -n)`, `GInt.sum` over a list, and semantic equality `GInt.Eq'` (both components `PInt.Eq'`), with the instance `GInt.instDecidableRelEq'`.
--
--   The embedded lemmas say that `toInt` and `toC` commute with every operation (`toInt_zero`, `toInt_ofNat`, `toInt_ofInt`, `toInt_add`, `toInt_neg`, `toInt_mul`, `toInt_sum`; `toC_zero`, `toC_ofNat`, `toC_ofInt`, `toC_add`, `toC_mul`, `toC_conj`, `toC_sum`, with `re_toC`, `im_toC`), that `Eq'` and `Lt'` are equality and strict order of the denoted values (`eq'_iff`, `lt'_iff`), and that `ofNat`, `add`, `neg`, `mul`, `conj` and `sum` are `Primrec` while `Eq'` and `Lt'` are `PrimrecRel`.
--
--   **Formalization Note**. `PInt` and `GInt` are `abbrev`s for product types, so Mathlib's `Primcodable` instance for `ℕ × ℕ` applies unchanged and the `Primrec` proofs are compositions of `Primrec.pair`, `Primrec.nat_add`, `Primrec.nat_mul`, `Primrec.list_foldr`, `Primrec.eq` and `Primrec.nat_lt`. The representation is not canonical ($(a, b)$ and $(a+1, b+1)$ denote the same integer), which is why equality of denoted values is the relation `Eq'` and not equality of pairs.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/RawInt.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/RawInt.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic

/-!
# Integers and Gaussian integers as pairs of naturals

Mathlib's `Primrec` has no arithmetic on `ℤ` (and no `Primcodable ℤ`), so the enumeration behind
`lem:value-lower-approx` carries its integers as pairs of naturals: `PInt := ℕ × ℕ` denotes
`a - b`, and `GInt := PInt × PInt` denotes the Gaussian integer `m + n i`. Equality and order are
the semantic ones (`PInt.Eq'`, `PInt.Lt'`, `GInt.Eq'`), decidable and primitive recursive;
`PInt.toInt` and `GInt.toC` read the values off and commute with the operations provided. Every
function here is primitive recursive, with the proof next to the definition.
-/

namespace MIPRE.ValueApprox

/-! ## Integers -/

/-- An integer `a - b`, as the pair `(a, b)` of naturals. -/
abbrev PInt := ℕ × ℕ

namespace PInt

/-- The integer denoted. -/
def toInt (x : PInt) : ℤ := (x.1 : ℤ) - x.2

def zero : PInt := (0, 0)
def ofNat (n : ℕ) : PInt := (n, 0)
def ofInt (m : ℤ) : PInt := (m.toNat, (-m).toNat)
def add (x y : PInt) : PInt := (x.1 + y.1, x.2 + y.2)
def neg (x : PInt) : PInt := (x.2, x.1)
def mul (x y : PInt) : PInt := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def sum (l : List PInt) : PInt := l.foldr add zero

/-- Semantic equality of the denoted integers. -/
def Eq' (x y : PInt) : Prop := x.1 + y.2 = y.1 + x.2

/-- Semantic strict order of the denoted integers. -/
def Lt' (x y : PInt) : Prop := x.1 + y.2 < y.1 + x.2

instance : DecidableRel Eq' := fun x y => inferInstanceAs (Decidable (x.1 + y.2 = y.1 + x.2))
instance : DecidableRel Lt' := fun x y => inferInstanceAs (Decidable (x.1 + y.2 < y.1 + x.2))

@[simp] theorem toInt_zero : zero.toInt = 0 := by simp [toInt, zero]
@[simp] theorem toInt_ofNat (n : ℕ) : (ofNat n).toInt = n := by simp [toInt, ofNat]
@[simp] theorem toInt_ofInt (m : ℤ) : (ofInt m).toInt = m := by
  simp [toInt, ofInt]
@[simp] theorem toInt_add (x y : PInt) : (add x y).toInt = x.toInt + y.toInt := by
  simp [toInt, add]; ring
@[simp] theorem toInt_neg (x : PInt) : (neg x).toInt = -x.toInt := by simp [toInt, neg]
@[simp] theorem toInt_mul (x y : PInt) : (mul x y).toInt = x.toInt * y.toInt := by
  simp [toInt, mul]; ring
@[simp] theorem toInt_sum (l : List PInt) : (sum l).toInt = (l.map toInt).sum := by
  induction l with
  | nil => simp [sum]
  | cons a l ih => simp only [sum, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
                   rw [toInt_add, ih]

theorem eq'_iff {x y : PInt} : Eq' x y ↔ x.toInt = y.toInt := by
  simp only [Eq', toInt]; omega
theorem lt'_iff {x y : PInt} : Lt' x y ↔ x.toInt < y.toInt := by
  simp only [Lt', toInt]; omega

theorem primrec_ofNat : Primrec ofNat := Primrec.pair Primrec.id (Primrec.const 0)
theorem primrec_add : Primrec₂ add :=
  Primrec.pair (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
theorem primrec_neg : Primrec neg := Primrec.pair Primrec.snd Primrec.fst
theorem primrec_mul : Primrec₂ mul :=
  Primrec.pair
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
theorem primrec_sum : Primrec sum :=
  Primrec.list_foldr Primrec.id (Primrec.const zero)
    (primrec_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
theorem primrecRel_eq' : PrimrecRel Eq' :=
  Primrec.eq.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
theorem primrecRel_lt' : PrimrecRel Lt' :=
  Primrec.nat_lt.comp
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))

end PInt

/-! ## Gaussian integers -/

/-- A Gaussian integer `m + n i`, as a pair of `PInt`s. -/
abbrev GInt := PInt × PInt

namespace GInt

/-- The complex number denoted. -/
def toC (z : GInt) : ℂ := (z.1.toInt : ℂ) + (z.2.toInt : ℂ) * Complex.I

def zero : GInt := (PInt.zero, PInt.zero)
def ofNat (n : ℕ) : GInt := (PInt.ofNat n, PInt.zero)
def ofInt (m n : ℤ) : GInt := (PInt.ofInt m, PInt.ofInt n)
def add (x y : GInt) : GInt := (PInt.add x.1 y.1, PInt.add x.2 y.2)
def mul (x y : GInt) : GInt :=
  (PInt.add (PInt.mul x.1 y.1) (PInt.neg (PInt.mul x.2 y.2)),
    PInt.add (PInt.mul x.1 y.2) (PInt.mul x.2 y.1))
def conj (x : GInt) : GInt := (x.1, PInt.neg x.2)
def sum (l : List GInt) : GInt := l.foldr add zero

/-- Semantic equality of the denoted Gaussian integers. -/
def Eq' (x y : GInt) : Prop := PInt.Eq' x.1 y.1 ∧ PInt.Eq' x.2 y.2

instance : DecidableRel Eq' := fun x y =>
  inferInstanceAs (Decidable (PInt.Eq' x.1 y.1 ∧ PInt.Eq' x.2 y.2))

@[simp] theorem re_toC (z : GInt) : (toC z).re = z.1.toInt := by simp [toC]
@[simp] theorem im_toC (z : GInt) : (toC z).im = z.2.toInt := by simp [toC]
@[simp] theorem toC_zero : toC zero = 0 := by simp [toC, zero]
@[simp] theorem toC_ofNat (n : ℕ) : toC (ofNat n) = n := by simp [toC, ofNat]
@[simp] theorem toC_ofInt (m n : ℤ) : toC (ofInt m n) = m + n * Complex.I := by
  simp [toC, ofInt]
@[simp] theorem toC_add (x y : GInt) : toC (add x y) = toC x + toC y := by
  apply Complex.ext <;> simp [add]
@[simp] theorem toC_mul (x y : GInt) : toC (mul x y) = toC x * toC y := by
  apply Complex.ext <;> simp [mul, Complex.mul_re, Complex.mul_im]
  ring
@[simp] theorem toC_conj (x : GInt) : toC (conj x) = star (toC x) := by
  apply Complex.ext <;> simp [conj]
@[simp] theorem toC_sum (l : List GInt) : toC (sum l) = (l.map toC).sum := by
  induction l with
  | nil => simp [sum]
  | cons a l ih => simp only [sum, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
                   rw [toC_add, ih]

theorem eq'_iff {x y : GInt} : Eq' x y ↔ toC x = toC y := by
  rw [Eq', PInt.eq'_iff, PInt.eq'_iff, Complex.ext_iff, re_toC, re_toC, im_toC, im_toC,
    Int.cast_inj, Int.cast_inj]

theorem primrec_ofNat : Primrec ofNat := Primrec.pair PInt.primrec_ofNat (Primrec.const PInt.zero)
theorem primrec_add : Primrec₂ add :=
  Primrec.pair (PInt.primrec_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (PInt.primrec_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
theorem primrec_mul : Primrec₂ mul :=
  Primrec.pair
    (PInt.primrec_add.comp
      (PInt.primrec_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (PInt.primrec_neg.comp
        (PInt.primrec_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))))
    (PInt.primrec_add.comp
      (PInt.primrec_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (PInt.primrec_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
theorem primrec_conj : Primrec conj := Primrec.pair Primrec.fst (PInt.primrec_neg.comp Primrec.snd)
theorem primrec_sum : Primrec sum :=
  Primrec.list_foldr Primrec.id (Primrec.const zero)
    (primrec_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
theorem primrecRel_eq' : PrimrecRel Eq' :=
  PrimrecPred.and (PInt.primrecRel_eq'.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (PInt.primrecRel_eq'.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

end GInt

end MIPRE.ValueApprox



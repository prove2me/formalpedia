-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
-- name    : MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:24:00.751572+00:00
-- url     : https://prove2.me/theorems/167c5605-d524-4185-b115-136645833afa
-- title:
--   Definitions of BinaryQuotientOrbit: Polynomial products with coefficients in an explicit binary quotient
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryQuotientOrbit` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Polynomial products with coefficients in an explicit binary quotient
--
--   **Definitions** (18): `MIPRE.LowDegree.BinaryQuotient.ProductState` (Modulus and accumulated coefficient list for a product of linear factors.); `MIPRE.LowDegree.BinaryQuotient.SquareState` (State for successive Frobenius powers, retaining the modulus.); `MIPRE.LowDegree.BinaryQuotient.coeffPolynomial` (Interpret a list of binary coefficient vectors as a polynomial.); `MIPRE.LowDegree.BinaryQuotient.linearMulBits` (Multiplication by `X + a` on encoded coefficient lists.); `MIPRE.LowDegree.BinaryQuotient.linearMulBitsProg` (Polynomial-time multiplication by one encoded monic linear factor.); `MIPRE.LowDegree.BinaryQuotient.linearMulCarry` (Multiply by a linear factor, with an extra constant coefficient carried in.); `MIPRE.LowDegree.BinaryQuotient.linearMulCarryProg` (A uniform linear-factor multiplication program on arbitrary nested lists.); `MIPRE.LowDegree.BinaryQuotient.linearProductBits` (Product of the monic linear factors with the supplied roots.); `MIPRE.LowDegree.BinaryQuotient.linearProductBitsProg` (One globally polynomial-time program for a product of encoded linear factors.); `MIPRE.LowDegree.BinaryQuotient.orbitBits` (The first Frobenius powers of a supplied represented element.); `MIPRE.LowDegree.BinaryQuotient.orbitBitsProg` (A polynomial-time orbit printer, valid on every raw input.); `MIPRE.LowDegree.BinaryQuotient.orbitProductBits` (Multiply the monic linear factors for a specified Frobenius orbit.); and 5 more.
--
--   **Embedded lemmas** (18): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coeffPolynomial_cons`, `coeffPolynomial_nil`, `esize_coefficients_le`, `fold_productStep_shape`, `fold_productStep_width`, `iterate_squareStep_shape`, `length_linearMulBits`, `length_linearMulCarry`, `length_orbitBits`, `length_orbitProductBits`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryQuotientOrbit` (`MIPRE/Foundations/LowDegree/BinaryQuotientOrbit.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 31 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryQuotientOrbit.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientOrbit.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce_le

/-! # Polynomial products with coefficients in an explicit binary quotient -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

variable {R : Type*} [CommRing R]

/-- Interpret a list of binary coefficient vectors as a polynomial. -/
def coeffPolynomial (z : R) : List BitStr → Polynomial R
  | [] => 0
  | c :: cs => C (evalBits z c) + X * coeffPolynomial z cs

@[simp] theorem coeffPolynomial_nil (z : R) : coeffPolynomial z [] = 0 := rfl

@[simp] theorem coeffPolynomial_cons (z : R) (c : BitStr) (cs : List BitStr) :
    coeffPolynomial z (c :: cs) = C (evalBits z c) + X * coeffPolynomial z cs := rfl

/-- Multiply by a linear factor, with an extra constant coefficient carried in. -/
def linearMulCarry (p a carry : BitStr) (cs : List BitStr) : List BitStr :=
  (carry :: cs).zipWith xorBits ((cs.map (mulReduce p a)) ++ [zeroBits p])

/-- Multiplication by `X + a` on encoded coefficient lists. -/
def linearMulBits (p a : BitStr) (cs : List BitStr) : List BitStr :=
  linearMulCarry p a (zeroBits p) cs

@[simp] theorem length_linearMulCarry (p a carry : BitStr) (cs : List BitStr) :
    (linearMulCarry p a carry cs).length = cs.length + 1 := by
  simp [linearMulCarry]

@[simp] theorem length_linearMulBits (p a : BitStr) (cs : List BitStr) :
    (linearMulBits p a cs).length = cs.length + 1 := length_linearMulCarry ..

/-- Scalar multiplication of all coefficient vectors by a supplied quotient element. -/
def scaleCoeffProg : PolyTimeFun (List BitStr × BitStr × BitStr) (List BitStr) :=
  mapWith (mulReduceProg.comp ((fst.comp snd).pair ((snd.comp snd).pair fst)))

/-- A uniform linear-factor multiplication program on arbitrary nested lists. -/
def linearMulCarryProg : PolyTimeFun (BitStr × BitStr × BitStr × List BitStr) (List BitStr) :=
  let p := fst
  let a := fst.comp snd
  let carry := fst.comp (snd.comp snd)
  let cs := snd.comp (snd.comp snd)
  let scaled := scaleCoeffProg.comp (cs.pair (p.pair a))
  let padded := append.comp (scaled.pair (cons (zeroBitsProg.comp p) (const [])))
  (map xorBitsProg).comp (zip.comp ((cons carry cs).pair padded))

@[simp] theorem linearMulCarryProg_apply (p a carry : BitStr) (cs : List BitStr) :
    linearMulCarryProg (p, a, carry, cs) = linearMulCarry p a carry cs := by
  change (((carry :: cs).zip ((cs.map (mulReduce p a)) ++ [zeroBits p])).map
    (fun pair => xorBits pair.1 pair.2)) = _
  exact List.map_zip_eq_zipWith

/-- Polynomial-time multiplication by one encoded monic linear factor. -/
def linearMulBitsProg : PolyTimeFun (BitStr × BitStr × List BitStr) (List BitStr) :=
  linearMulCarryProg.comp
    (fst.pair ((fst.comp snd).pair ((zeroBitsProg.comp fst).pair (snd.comp snd))))

@[simp] theorem linearMulBitsProg_apply (p a : BitStr) (cs : List BitStr) :
    linearMulBitsProg (p, a, cs) = linearMulBits p a cs := by
  change linearMulCarryProg (p, a, zeroBits p, cs) = _
  rw [linearMulCarryProg_apply]
  rfl

/-- Malformed coefficient arithmetic cannot increase a retained coefficient width. -/
theorem linearMulCarry_width_le (p a carry : BitStr) (cs : List BitStr) (N : ℕ)
    (hc : carry.length ≤ N) (hs : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ linearMulCarry p a carry cs, c.length ≤ N := by
  induction cs generalizing carry with
  | nil =>
    intro c he
    have heq : c = xorBits carry (zeroBits p) := by simpa [linearMulCarry] using he
    rw [heq, length_xorBits]
    exact (min_le_left _ _).trans hc
  | cons c cs ih =>
    change ∀ d ∈ xorBits carry (mulReduce p a c) :: linearMulCarry p a c cs, d.length ≤ N
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · rw [length_xorBits]
      exact (min_le_left _ _).trans hc
    · exact ih c (hs c (by simp)) (fun d hd => hs d (by simp [hd])) d hd

/-- Modulus and accumulated coefficient list for a product of linear factors. -/
abbrev ProductState := BitStr × List BitStr

/-- Multiply the accumulated polynomial by the next supplied linear factor. -/
def productStep (s : ProductState) (a : BitStr) : ProductState :=
  (s.1, linearMulBits s.1 a s.2)

/-- The product loop retains its modulus and adds one coefficient per iteration. -/
theorem fold_productStep_shape (bs : List BitStr) (s : ProductState) :
    (bs.foldl productStep s).1 = s.1 ∧
      (bs.foldl productStep s).2.length = s.2.length + bs.length := by
  induction bs generalizing s with
  | nil => simp
  | cons a bs ih =>
    have h := ih (productStep s a)
    simpa only [List.foldl_cons, productStep, length_linearMulBits, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1 bs.length] using h

/-- Every coefficient width remains bounded independently of the number of factors. -/
theorem fold_productStep_width (bs : List BitStr) (p : BitStr) (cs : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (hs : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ (bs.foldl productStep (p, cs)).2, c.length ≤ N := by
  induction bs generalizing cs with
  | nil => exact hs
  | cons a bs ih =>
    apply ih (linearMulBits p a cs)
    exact linearMulCarry_width_le p a (zeroBits p) cs N (by simpa using hp) hs

/-- Product of the monic linear factors with the supplied roots. -/
def linearProductBits (p : BitStr) (bs : List BitStr) : List BitStr :=
  (bs.foldl productStep (p, [oneBits p])).2

def productStepProg : PolyTimeFun (ProductState × BitStr) ProductState :=
  congr ((fst.comp fst).pair (linearMulBitsProg.comp
    ((fst.comp fst).pair (snd.pair (snd.comp fst)))))
    (fun q => productStep q.1 q.2) (by
      rintro ⟨⟨p, cs⟩, a⟩
      change (p, linearMulBitsProg (p, a, cs)) = (p, linearMulBits p a cs)
      rw [linearMulBitsProg_apply])

/-- Nested coefficient-list encoded size is polynomial in count and width. -/
theorem esize_coefficients_le (cs : List BitStr) (N : ℕ)
    (hs : ∀ c ∈ cs, c.length ≤ N) : esize cs ≤ cs.length * (4 * N + 2) + 1 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := esize_bitStr_le c
    have hl := hs c (by simp)
    have ht := ih (fun d hd => hs d (by simp [hd]))
    rw [esize_list_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem productStep_bounded : FoldBounded productStepProg (10 * X ^ 2 + 10 * X + 10) := by
  intro bs s pre post heq
  rcases s with ⟨p, cs⟩
  let N := esize (bs, p, cs)
  have hp : p.length ≤ N := by
    have h := length_le_esize_list p
    simp only [N, esize_prod]
    omega
  have hc : cs.length ≤ N := by
    have h := length_le_esize_list cs
    simp only [N, esize_prod]
    omega
  have hb : pre.length ≤ N := by
    have h := length_le_esize_list bs
    have he := congrArg List.length heq
    simp only [N, esize_prod, List.length_append] at *
    omega
  have hw : ∀ c ∈ cs, c.length ≤ N := by
    intro c hc'
    have h₁ := esize_mem_le hc'
    have h₂ := length_le_esize_bitStr c
    simp only [N, esize_prod]
    omega
  have hs := fold_productStep_shape pre (p, cs)
  have hsize := esize_coefficients_le _ N (fold_productStep_width pre p cs N hp hw)
  have hlen : (pre.foldl productStep (p, cs)).2.length = cs.length + pre.length := hs.2
  have hn : (pre.foldl productStep (p, cs)).2.length ≤ 2 * N := by omega
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  have hpe : esize p ≤ N := by simp only [N, esize_prod]; omega
  change esize (pre.foldl productStep (p, cs)) ≤ _
  rw [esize_prod, hs.1]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + esize (pre.foldl productStep (p, cs)).2 + 1 ≤ 10 * N ^ 2 + 10 * N + 10
  nlinarith

/-- One globally polynomial-time program for a product of encoded linear factors. -/
def linearProductBitsProg : PolyTimeFun (BitStr × List BitStr) (List BitStr) :=
  snd.comp ((foldl productStepProg (10 * X ^ 2 + 10 * X + 10) productStep_bounded).comp
    (snd.pair (fst.pair (cons (oneBitsProg.comp fst) (const [])))))

@[simp] theorem linearProductBitsProg_apply (p : BitStr) (bs : List BitStr) :
    linearProductBitsProg (p, bs) = linearProductBits p bs := rfl

/-- State for successive Frobenius powers, retaining the modulus. -/
abbrev SquareState := BitStr × BitStr

/-- One repeated-squaring step in a supplied binary quotient. -/
def squareStep (s : SquareState) : SquareState := (s.1, mulReduce s.1 s.2 s.2)

/-- Squaring cannot increase the width even on malformed inputs. -/
theorem iterate_squareStep_shape (n : ℕ) (s : SquareState) :
    (squareStep^[n] s).1 = s.1 ∧ (squareStep^[n] s).2.length ≤ s.2.length := by
  induction n generalizing s with
  | zero => exact ⟨rfl, le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨hm, hw⟩ := ih (squareStep s)
    exact ⟨hm, hw.trans (length_mulReduce_le ..)⟩

def squareStepProg : PolyTimeFun SquareState SquareState := fst.pair squareProg

theorem squareStep_bounded (n : ℕ) (s : SquareState) :
    esize ((squareStepProg : SquareState → SquareState)^[n] s) ≤
      (5 * X + 5 : Polynomial ℕ).eval (esize s) := by
  change esize (squareStep^[n] s) ≤ _
  obtain ⟨hm, hw⟩ := iterate_squareStep_shape n s
  have ha := esize_bitStr_le (squareStep^[n] s).2
  have hb := length_le_esize_bitStr s.2
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  rw [esize_prod, hm]
  simp only [eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- The first Frobenius powers of a supplied represented element. -/
def orbitBits (u : Unary) (p a : BitStr) : List BitStr :=
  (recordIterates squareStep u (p, a)).map Prod.snd

/-- The orbit list has exactly its unary budget of elements. -/
@[simp] theorem length_orbitBits (u : Unary) (p a : BitStr) :
    (orbitBits u p a).length = u.length := by simp [orbitBits, recordIterates]

/-- A polynomial-time orbit printer, valid on every raw input. -/
def orbitBitsProg : PolyTimeFun (Unary × BitStr × BitStr) (List BitStr) :=
  (map snd).comp (recordIteratesProg squareStepProg (5 * X + 5) squareStep_bounded)

@[simp] theorem orbitBitsProg_apply (u : Unary) (p a : BitStr) :
    orbitBitsProg (u, p, a) = orbitBits u p a := rfl

/-- Multiply the monic linear factors for a specified Frobenius orbit. -/
def orbitProductBits (u : Unary) (p a : BitStr) : List BitStr :=
  linearProductBits p (orbitBits u p a)

/-- A uniform polynomial-time Frobenius-orbit product program. -/
def orbitProductBitsProg : PolyTimeFun (Unary × BitStr × BitStr) (List BitStr) :=
  linearProductBitsProg.comp ((fst.comp snd).pair orbitBitsProg)

@[simp] theorem orbitProductBitsProg_apply (u : Unary) (p a : BitStr) :
    orbitProductBitsProg (u, p, a) = orbitProductBits u p a := by
  change linearProductBitsProg (p, orbitBits u p a) = _
  rw [linearProductBitsProg_apply]
  rfl

/-- The orbit product has exactly one more coefficient than its orbit length. -/
@[simp] theorem length_orbitProductBits (u : Unary) (p a : BitStr) :
    (orbitProductBits u p a).length = u.length + 1 := by
  have h := (fold_productStep_shape (orbitBits u p a) (p, [oneBits p])).2
  simpa only [orbitProductBits, linearProductBits, List.length_singleton, length_orbitBits,
    Nat.add_comm 1 u.length] using h

end MIPRE.LowDegree.BinaryQuotient

end



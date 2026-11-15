-- Prove2me | Definitions.Def_TimeSpaceMA_GUVFieldOperations
-- name    : TimeSpaceMA_GUVFieldOperations
-- status  : Definition
-- author  : @bersubs
-- created : 2026-11-14T20:29:45.48314+00:00
-- url     : https://prove2.me/theorems/4dd5b035-aa00-4bdf-a69e-a4d646b85c7e
-- title:
--   Binary field operations for the folded Reed–Solomon map
-- statement:
--   Specifies binary labels for a finite field and its quadratic extension, a field embedding, and a primitive element of the smaller field. It requires uniform polynomial-time coded addition and multiplication, the two input coefficient labels, zero, and the embedded primitive element.

import Definitions.Def_TimeSpaceMA_TUZExtractorComponents
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace TimeSpaceMA.GUV
open Polynomial Turing.MultiTapeTM

/-- The floor of one on width only affects malformed width-zero queries. -/
def halfSeed (a n : ℕ) : ℕ := a*(max 1 n).size

theorem halfSeed_of_pos {a n : ℕ} (hn : 1 ≤ n) : halfSeed a n = a*n.size := by
  simp [halfSeed, max_eq_right hn]

theorem halfSeed_pos {a : ℕ} (ha : 0 < a) (n : ℕ) : 0 < halfSeed a n :=
  Nat.mul_pos ha (Nat.size_pos.mpr (by have := Nat.le_max_left 1 n; omega))
def symbols (c k : ℕ) : ℕ := (k+c-1)/c

theorem symbols_width {c k : ℕ} : 2*c*(symbols c k+1) ≤ 2*(k+2*c) := by
  have h := Nat.mul_div_le (k+c-1) c
  change c * symbols c k ≤ _ at h
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left 2 (by omega)

noncomputable def vectorPoly {K : Type} [Field K] {n : ℕ} (a : Fin n → K) : K[X] :=
  ∑ i : Fin n, monomial i.val (a i)

variable {F : Type*} [Field F] in
noncomputable def fold (z : F) (i : ℕ) (f : F[X]) : F[X] :=
  f.comp (C (z ^ i) * X)

noncomputable def inputCode {K : Type} {c n : ℕ} (basis : Fin (2^c) ≃ K)
    (hc : 0 < c) (x : Fin (2^n)) (j : Fin n) : K :=
  basis ⟨x.val / 2^j.val % 2, (Nat.mod_lt _ (by decide : 0 < 2)).trans_le
    (Nat.le_pow hc : 2 ≤ 2^c)⟩

noncomputable def outputCode {F : Type} {c k : ℕ} (basis : Fin (2^(2*c)) ≃ F) :
    (F × (Fin (symbols c k) → F)) ↪ Fin (2^(2*(k+2*c))) :=
  ((basis.symm.prodCongr ((Equiv.piCongrRight (fun _ : Fin (symbols c k) => basis.symm)).trans
      finFunctionFinEquiv)).trans (finProdFinEquiv.trans (finCongr (by rw [← pow_succ',
      ← pow_mul])))).toEmbedding.trans (Fin.castLEEmb
        (Nat.pow_le_pow_right (by decide) symbols_width))

/-- An arithmetic implementation of the folded Reed–Solomon evaluator. The chosen
field labels may be any bijective representations. The contract compares exact
numeric outputs, and requires no expansion or probability hypothesis. -/
structure FoldedEvaluator (a : ℕ) (ha : 0 < a) (cond : ExtractorInput → ℕ) where
  native : ComputableInPolyTime cond encExtractorInput encNat
  K : ℕ → Type
  F : ℕ → Type
  fieldK (n : ℕ) : Field (K n)
  fieldF (n : ℕ) : Field (F n)
  charF (n : ℕ) : CharP (F n) 2
  codeK (n : ℕ) : Fin (2 ^ halfSeed a n) ≃ K n
  codeF (n : ℕ) : Fin (2 ^ (2 * halfSeed a n)) ≃ F n
  embed (n : ℕ) : K n →+* F n
  primitive (n : ℕ) : K n
  primitive_order (n : ℕ) (hn : 1 ≤ n) : orderOf (primitive n) = 2^halfSeed a n - 1
  correct (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
      (x : Fin (2^n)) (y : Fin (2^(2*halfSeed a n))) :
    cond (n,k,2*halfSeed a n,x.val,y.val) =
      (outputCode (k := k) (codeF n) (codeF n y, fun i =>
        (fold (embed n (primitive n)) i.val ((vectorPoly (inputCode (codeK n) (show 0 < halfSeed a n from halfSeed_pos ha n) x)).map (embed n))).eval
          (codeF n y))).val

abbrev FieldWord (a : ℕ) (n : ℕ) := Fin (2^(2*halfSeed a n))
abbrev FieldBinInput := ℕ × ℕ × ℕ
abbrev encFieldBinInput : FieldBinInput ↪ List Bool :=
  encPair encUnary (encPair encNat encNat)
abbrev FieldCoeffInput := ℕ × Bool
abbrev encFieldCoeffInput : FieldCoeffInput ↪ List Bool := encPair encUnary encBool

/-- A presentation of binary extension fields with coded arithmetic.
Syntactic operations return natural numbers, clipped by the caller to the field
word width. The primitive is represented after embedding into the larger field. -/
structure BinaryFieldArithmetic (a : ℕ) (ha : 0 < a) where
  K : ℕ → Type
  F : ℕ → Type
  fieldK (n : ℕ) : Field (K n)
  fieldF (n : ℕ) : Field (F n)
  charF (n : ℕ) : CharP (F n) 2
  codeK (n : ℕ) : Fin (2 ^ halfSeed a n) ≃ K n
  codeF (n : ℕ) : FieldWord a n ≃ F n
  embed (n : ℕ) : K n →+* F n
  primitive (n : ℕ) : K n
  primitive_order (n : ℕ) (hn : 1 ≤ n) : orderOf (primitive n) = 2^halfSeed a n - 1
  add : FieldBinInput → ℕ
  mul : FieldBinInput → ℕ
  coeff : FieldCoeffInput → ℕ
  zero : ℕ → ℕ
  generator : ℕ → ℕ
  add_native : ComputableInPolyTime add encFieldBinInput encNat
  mul_native : ComputableInPolyTime mul encFieldBinInput encNat
  coeff_native : ComputableInPolyTime coeff encFieldCoeffInput encNat
  zero_native : ComputableInPolyTime zero encUnary encNat
  generator_native : ComputableInPolyTime generator encUnary encNat
  add_correct (n : ℕ) (hn : 1 ≤ n) (x y : FieldWord a n) :
    add (n,x.val,y.val) % 2^(2*halfSeed a n) = ((codeF n).symm (codeF n x + codeF n y)).val
  mul_correct (n : ℕ) (hn : 1 ≤ n) (x y : FieldWord a n) :
    mul (n,x.val,y.val) % 2^(2*halfSeed a n) = ((codeF n).symm (codeF n x * codeF n y)).val
  coeff_correct (n : ℕ) (hn : 1 ≤ n) (b : Bool) :
    coeff (n,b) % 2^(2*halfSeed a n) =
      ((codeF n).symm (embed n (codeK n ⟨b.toNat,
        (show b.toNat < 2 from by cases b <;> decide).trans_le
          (Nat.le_pow (halfSeed_pos ha n))⟩))).val
  zero_correct (n : ℕ) (hn : 1 ≤ n) :
    zero n % 2^(2*halfSeed a n) = ((codeF n).symm 0).val
  generator_correct (n : ℕ) (hn : 1 ≤ n) :
    generator n % 2^(2*halfSeed a n) = ((codeF n).symm (embed n (primitive n))).val

end TimeSpaceMA.GUV



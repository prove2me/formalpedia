-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeNatFrontends
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeNatFrontends
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:48:14.593912+00:00
-- url     : https://prove2.me/theorems/1659649c-d151-4209-b4a9-de93e4c88621
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends — Direct unary comparison and bit-access frontends
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   These canonical interfaces retain the original word folds: unary subtraction folds predecessor,
--   unary-to-binary conversion folds the binary successor, and indexed access folds the word tail
--   before using the existing head codec. No higher tidy calculus supplies a plain primitive.
--
--   **Contents.** The module is published as a whole: 10 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeNatFrontends`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimeNatFrontends.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeUnaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.GetD

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct unary comparison and bit-access frontends

These canonical interfaces retain the original word folds: unary subtraction folds predecessor,
unary-to-binary conversion folds the binary successor, and indexed access folds the word tail
before using the existing head codec. No higher tidy calculus supplies a plain primitive.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Truncated subtraction of unary naturals. -/
@[fun_prop]
theorem unary_sub :
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
      (encPair encUnary encUnary) encUnary := by
  have hrep (a b : ℕ) : (List.replicate b true).foldl (fun n _ => n - 1) a = a - b := by
    induction b generalizing a with
    | zero => rfl
    | succ b ih => rw [List.replicate_succ, List.foldl_cons, ih]; omega
  have hfold := foldl' (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun p : ℕ × ℕ => List.replicate p.2 true) (step := fun n _ => n - 1)
    ((of_eq (f := fun n => List.replicate n true) (encIn := encUnary) (encOut := encBits)
      fun _ => rfl).comp (snd encUnary encUnary))
    (fst encUnary encUnary)
    (ComputableInDegree.unary_pred.computableInPolyTime.comp (fst encUnary encBool))
    (B := fun p => (encPair encUnary encUnary p).length) .self (fun p i _ => by
      rw [List.take_replicate, hrep]
      simp only [encPair_apply, encUnary_apply, List.length_append, length_frame,
        List.length_replicate]
      omega)
  simpa only [hrep] using hfold

/-- Comparison of unary naturals. -/
@[fun_prop]
theorem unary_le :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool := by
  simpa only [Function.comp_def, Nat.sub_eq_zero_iff_le] using
    ComputableInDegree.unary_isZero.computableInPolyTime.comp unary_sub

/-- Strict comparison of unary naturals. -/
@[fun_prop]
theorem unary_lt :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
      (encPair encUnary encUnary) encBool := by
  simpa only [Function.comp_def, ← decide_not, Nat.not_le] using bool_not.comp
    (unary_le.comp ((snd encUnary encUnary).prod (fst encUnary encUnary)))

/-- Compare computed unary values, with both operand encodings fixed. -/
@[fun_prop]
theorem unary_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  unary_le.comp (hleft.prod hright)

/-- Strictly compare computed unary values, with both operand encodings fixed. -/
@[fun_prop]
theorem unary_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => decide (left a < right a)) input encBool :=
  unary_lt.comp (hleft.prod hright)

/-- Convert a unary natural to its binary encoding. -/
@[fun_prop]
theorem unary_to_binary : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat := by
  have hsize (n : ℕ) : (encNat n).length ≤ n := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hsucc := ComputableInO.natSucc.computableInPolyTime
    (PolyBounded.of_forall_le 1 2 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
  have h := foldl' (encA := encBool) (encL := encBits) (list := fun n => List.replicate n true)
    (step := fun n _ => n + 1)
    (of_eq (encIn := encUnary) (encOut := encBits) fun _ => rfl) (const 0)
    (hsucc.comp (fst encNat encBool))
    (B := fun n => (encUnary n).length) .self (fun n i _ => by
      simpa [List.foldl_const] using (hsize (min i n)).trans (Nat.min_le_right i n))
  simpa [List.foldl_const] using h

private theorem bitsDropUnary :
    ComputableInPolyTime (fun p : List Bool × ℕ => p.1.drop p.2)
      (encPair encBits encUnary) encBits := by
  have heq (l : List Bool) (n : ℕ) :
      (List.replicate n true).foldl (fun acc _ => acc.tail) l = l.drop n := by
    simp [List.foldl_const, List.tail_iterate]
  have h := foldl' (encA := encBool) (encL := encBits)
    (list := fun p : List Bool × ℕ => List.replicate p.2 true) (step := fun acc _ => acc.tail)
    ((of_eq (encIn := encUnary) (encOut := encBits) fun _ => rfl).comp (snd encBits encUnary))
    (fst encBits encUnary) (bitsTail.comp (fst encBits encBool))
    (B := fun p => (encPair encBits encUnary p).length) .self (fun p i _ => by
      rw [List.take_replicate, heq]
      simp only [length_encPair, encBits_apply, List.length_drop]
      omega)
  simpa only [heq] using h

/-- Read a bit at a unary index with a fixed fallback. Fixing the raw encoding avoids
guessing a list-encoding instance during compositional proof search. -/
@[fun_prop]
theorem bitsGetD (fallback : Bool) :
    ComputableInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 fallback)
      (encPair encBits encUnary) encBool := by
  have hhead : ComputableInPolyTime (fun l : List Bool => l.headD fallback) encBits encBool := by
    exact (ListEncoding.headD
      (enc₁ := encBool) (enc := encBits) fallback).computableInPolyTime
  simpa only [Function.comp_def, List.headD_eq_head?_getD, List.head?_drop,
    List.getD_eq_getElem?_getD] using hhead.comp bitsDropUnary

/-- Read the bit of a computed binary number at a computed unary position. -/
@[fun_prop]
theorem binary_testBit {α : Type} {input : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n input encNat)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => (n a).testBit (i a)) input encBool := by
  have hbits := (of_eq (encIn := encNat) (encOut := encBits) (f := Nat.bits) fun _ => rfl).comp hn
  refine ((bitsGetD false).comp (hbits.prod hi)).of_enc_eq fun a => ?_
  simp only [Function.comp_apply, Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
  rfl

/-- Read the bit of a computed unary number at a computed unary position. -/
@[fun_prop]
theorem unary_testBit' {α : Type} {input : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => (n a).testBit (i a)) input encBool :=
  binary_testBit (unary_to_binary.comp hn) hi

end Turing.MultiTapeTM.ComputableInPolyTime



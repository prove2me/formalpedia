-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Primitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Primitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:50:29.284214+00:00
-- url     : https://prove2.me/theorems/d33cd380-418b-4dd8-94e0-d95fd6c54661
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives — Basic functions with bounds of given degrees
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Functions on unary numbers and integers, in linear time and space, and equality tests, in quadratic
--   time and space.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.encUnary`: natural numbers in unary.
--   * `Turing.MultiTapeTM.encInt`: integers as a sign followed by a unary magnitude.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInDegree.eq`: equality, for any encoding.
--   * successor, predecessor and zero test in unary, and adding one or subtracting one on integers.
--
--   **Contents.** The module is published as a whole: 20 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Primitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Primitives.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeUnaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_WordEquality
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Fold
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer_Copy
import Mathlib.Tactic.FinCases

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Basic functions with bounds of given degrees

Functions on unary numbers and integers, in linear time and space, and equality tests, in quadratic
time and space.

## Main definitions

* `Turing.MultiTapeTM.encUnary`: natural numbers in unary.
* `Turing.MultiTapeTM.encInt`: integers as a sign followed by a unary magnitude.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInDegree.eq`: equality, for any encoding.
* successor, predecessor and zero test in unary, and adding one or subtracting one on integers.
-/

namespace Turing.MultiTapeTM

/-! ### Unary numbers -/

namespace ComputableTidilyInDegree

public theorem unary_succ : ComputableTidilyInDegree (· + 1) encUnary encUnary 1 1 :=
  .of_linear (.of_cons_true fun n => by simp [List.replicate_succ])

public theorem unary_pred : ComputableTidilyInDegree (· - 1) encUnary encUnary 1 1 :=
  .of_linear (.of_tail fun n => by cases n <;> simp [List.replicate_succ])

public theorem unary_isZero :
    ComputableTidilyInDegree (fun n => decide (n = 0)) encUnary encBool 1 1 :=
  .of_linear (.of_isEmpty fun n => by cases n <;> simp [List.replicate_succ])

end ComputableTidilyInDegree

/-! ### Integers -/

/-- Integers: `false` followed by `n` in unary for `n ≥ 0`, and `true` followed by `n` in unary for
`-(n + 1)`. -/
@[expose] public def encInt : ℤ ↪ List Bool :=
  ⟨fun z => match z with
    | .ofNat n => false :: List.replicate n true
    | .negSucc n => true :: List.replicate n true,
   fun a b h => by
    cases a <;> cases b <;> simp_all [List.replicate_inj]⟩

@[simp]
public lemma encInt_ofNat (n : ℕ) : encInt (Int.ofNat n) = false :: List.replicate n true := rfl

@[simp]
public lemma encInt_natCast (n : ℕ) : encInt (n : ℤ) = false :: List.replicate n true := rfl

@[simp]
public lemma encInt_zero : encInt 0 = [false] := rfl

@[simp]
public lemma encInt_natCast_add_one (n : ℕ) :
    encInt ((n : ℤ) + 1) = false :: true :: List.replicate n true :=
  rfl

@[simp]
public lemma encInt_negSucc (n : ℕ) : encInt (Int.negSucc n) = true :: List.replicate n true :=
  rfl

public lemma length_encInt (z : ℤ) :
    (encInt z).length = if z < 0 then (-z).toNat else z.toNat + 1 := by
  rcases z with n | n <;> simp [Int.negSucc_lt_zero]

public lemma length_encInt_add_one_le (z : ℤ) :
    (encInt (z + 1)).length ≤ (encInt z).length + 1 := by
  rw [length_encInt, length_encInt]; split_ifs <;> omega

public lemma length_encInt_sub_one_le (z : ℤ) :
    (encInt (z - 1)).length ≤ (encInt z).length + 1 := by
  rw [length_encInt, length_encInt]; split_ifs <;> omega

namespace EncInt

/-- Adds one to an encoded integer. -/
@[simps q₀ step final]
def succT : Transducer Bool (Fin 3) where
  q₀ := 0
  step q b := match q, b with
    | 0, false => (2, [false, true])
    | 0, true => (1, [])
    | 1, b => (2, [b])
    | _, b => (2, [b])
  final q := if q = 1 then [false] else []
  length_step_le q b := by fin_cases q <;> cases b <;> simp
  length_final_le q := by split_ifs <;> simp

/-- Subtracts one from an encoded integer. -/
@[simps q₀ step final]
def predT : Transducer Bool (Fin 3) where
  q₀ := 0
  step q b := match q, b with
    | 0, false => (1, [])
    | 0, true => (2, [true, true])
    | 1, _ => (2, [false])
    | _, b => (2, [b])
  final q := if q = 1 then [true] else []
  length_step_le q b := by fin_cases q <;> cases b <;> simp
  length_final_le q := by split_ifs <;> simp

end EncInt

namespace ComputableTidilyInDegree

open EncInt in
public theorem int_succ : ComputableTidilyInDegree (· + 1) encInt encInt 1 1 := by
  refine .of_linear (succT.computableTidilyInLinearTimeAndSpace fun z => ?_)
  have hc := Transducer.run_eq_self succT 2 (fun b => by cases b <;> rfl) rfl
  rcases z with n | _ | n
  · simp [hc]
  · rfl
  · change encInt (Int.negSucc n) = _
    simp [hc, List.replicate_succ]

open EncInt in
public theorem int_pred : ComputableTidilyInDegree (· - 1) encInt encInt 1 1 := by
  refine .of_linear (predT.computableTidilyInLinearTimeAndSpace fun z => ?_)
  have hc := Transducer.run_eq_self predT 2 (fun b => by cases b <;> rfl) rfl
  rcases z with (_ | n) | n
  · rfl
  · simp [hc]
  · simp [hc, List.replicate_succ]

end ComputableTidilyInDegree

/-! ### Equality -/

namespace ComputableTidilyInDegree

/-- A step of comparing words. -/
public theorem eqWordsStep : ComputableTidilyInDegree (fun q : (List Bool × Bool) × Bool =>
    EqWords.step q.1 q.2) (encPair (encPair encBits encBool) encBool) (encPair encBits encBool)
    1 1 := by
  -- the rest of the second word, and the facts it is compared by
  have hq := fst (encPair encBits encBool) encBool
  have hrest := hq.fst'
  have hlast := ((headD (enc₁ := encBool) false).comp hrest).pair
    (snd (encPair encBits encBool) encBool) (enc := encPair encBool encBool)
  have hfacts := hq.snd'.prod (((isEmpty (enc₁ := encBool)).comp hrest).prod hlast)
  exact (((tail (enc₁ := encBool)).comp hrest).prod
    ((of_finite (encIn := encPair encBool (encPair encBool (encPair encBool encBool)))
      (encMid := encBool) fun t : Bool × Bool × Bool × Bool =>
        t.1 && !t.2.1 && (t.2.2.1 == t.2.2.2)).comp hfacts)).mono

/-- The result of comparing words, from the state after the last step. -/
public theorem eqWordsResult :
    ComputableTidilyInDegree (fun s : List Bool × Bool => s.2 && s.1.isEmpty)
      (encPair encBits encBool) encBool 1 0 :=
  ((of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun t : Bool × Bool => t.1 && t.2).comp ((snd encBits encBool).prod
      ((isEmpty (enc₁ := encBool)).comp (fst encBits encBool)))).mono

/-- Equality of words. -/
public theorem eqWords :
    ComputableTidilyInDegree (fun p : List Bool × List Bool => decide (p.1 = p.2))
      (encPair encBits encBits) encBool 2 0 := by
  have hfold := ComputableTidilyInDegree.foldl' (encA := encBool) (encL := encBits)
    (encB := encPair encBits encBool) (fst encBits encBits)
    ((snd encBits encBits).prod (const true)) eqWordsStep
    (B := fun p => 2 * (encPair encBits encBits p).length + 2)
    ((DegreeBounded.self.smul 2).add_const 2)
    (fun p i hi => by
      rw [show ((p.1.take i).foldl EqWords.step (p.2, true)) =
        ((p.2.drop (p.1.take i).length), ((p.1.take i).foldl EqWords.step (p.2, true)).2) from
          Prod.ext (EqWords.foldl_fst _ _ _) rfl]
      simp only [encPair_apply, encBits_apply, encBool_apply, List.length_append, length_frame,
        List.length_drop, List.length_singleton]
      omega)
  have h : ComputableTidilyInDegree (_ ∘ _) _ encBool 2 0 := (eqWordsResult.comp hfold).mono
  convert h using 1
  funext p
  simpa using (EqWords.foldl_result p.1 p.2 true).symm

/-- Equality, for any encoding. -/
public theorem eq {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableTidilyInDegree (fun p : α × α => decide (p.1 = p.2)) (encPair enc enc) encBool
      2 0 := by
  have h : ComputableTidilyInDegree (_ ∘ _) _ encBool 2 0 := (eqWords.comp (of_eq
    (f := fun p : α × α => (enc p.1, enc p.2)) (encIn := encPair enc enc)
    (encMid := encPair encBits encBits) fun _ => rfl)).mono
  convert h using 1
  funext p
  simp [enc.injective.eq_iff]

end ComputableTidilyInDegree

end Turing.MultiTapeTM



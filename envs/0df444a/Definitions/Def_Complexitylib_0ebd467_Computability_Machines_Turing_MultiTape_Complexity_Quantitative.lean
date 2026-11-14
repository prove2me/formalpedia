-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Quantitative
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Quantitative
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:56:02.700835+00:00
-- url     : https://prove2.me/theorems/c0cdfe4c-5f5a-402d-8697-61940ef51e92
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative — Quantitative computability rules
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `fun_prop (disch := lia)` composes degree certificates (`ComputableInDegree` and
--   `ComputableTidilyInDegree`) without replacing output-size bounds by
--   runtime bounds. Computation premises determine the intermediate encodings and degrees before the
--   arithmetic obligations compare the resulting degrees with the requested ones. The same `fun_prop`
--   interface recognizes ordinary finite-state bit folds with linear time and constant work space.
--   For nested projections with inferred degrees, `disch := first | apply le_refl | lia` first
--   instantiates a missing degree with the derived bound, then checks arithmetic inequalities.
--   Framed-list and option rules infer the payload encoding from the representation explicitly.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInDegree.foldl'`,
--     `Turing.MultiTapeTM.ComputableInDegree.foldlWith`: plain left folds with degree bounds.
--   * `Turing.MultiTapeTM.ComputableInDegree.natSucc`: binary successor with degrees one.
--   * `Turing.MultiTapeTM.computableInDegree_add`, `Turing.MultiTapeTM.computableInDegree_mul`:
--     plain binary addition (quadratic) and multiplication (cubic).
--   * `Turing.MultiTapeTM.ComputableInO.comp_enc`: reuse a bit-word computation on encoded
--     instances, with bounds evaluated on their encodings.
--   * `Turing.MultiTapeTM.ComputableInO.lengthUnary`: compute bit-word length in unary within
--     linear time and space.
--   * `Turing.MultiTapeTM.ComputableInO.unary_two_pow`: compute `2 ^ n` from unary `n` within
--     time `O((n + 1) * 2 ^ n)` and space `O(2 ^ n)`.
--   * `Turing.MultiTapeTM.ComputableInDegree.comp_le`, `.prod_le`, `.ite_le`: plain composition,
--     pairing, and branching at requested degrees, retaining output-size bounds.
--   * `Turing.MultiTapeTM.ComputableInDegree.bitsReverse`,
--     `Turing.MultiTapeTM.ComputableInDegree.bitsDropLast`,
--     `Turing.MultiTapeTM.ComputableInDegree.bitsGetLast?ToList`,
--     `Turing.MultiTapeTM.ComputableInDegree.bitsGetLast?`,
--     `Turing.MultiTapeTM.ComputableInDegree.optionBoolToList`,
--     `Turing.MultiTapeTM.ComputableInDegree.bitsAppend`,
--     `Turing.MultiTapeTM.ComputableInDegree.unaryAdd`: plain degree rules for raw bit-list reversal,
--     prefix, last-bit extraction, concatenation, and unary addition (alongside tidy counterparts).
--
--   ### References
--
--   Uses Christian Reitwiessner's degree calculus and streaming backend; see the source markers in
--   `Degree.lean` and `Complexity/Computability/Machines/Turing/MultiTape/Encodings/StreamFold.lean`.
--
--   **Contents.** The module is published as a whole: 54 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Quantitative`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Quantitative.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Streaming
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_EqualityPrimitives
public import Mathlib.Tactic.FunProp
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer_Copy
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OLoops
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryAddition
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Doubling
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Quantitative computability rules

`fun_prop (disch := lia)` composes degree certificates (`ComputableInDegree` and
`ComputableTidilyInDegree`) without replacing output-size bounds by
runtime bounds. Computation premises determine the intermediate encodings and degrees before the
arithmetic obligations compare the resulting degrees with the requested ones. The same `fun_prop`
interface recognizes ordinary finite-state bit folds with linear time and constant work space.
For nested projections with inferred degrees, `disch := first | apply le_refl | lia` first
instantiates a missing degree with the derived bound, then checks arithmetic inequalities.
Framed-list and option rules infer the payload encoding from the representation explicitly.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.foldl'`,
  `Turing.MultiTapeTM.ComputableInDegree.foldlWith`: plain left folds with degree bounds.
* `Turing.MultiTapeTM.ComputableInDegree.natSucc`: binary successor with degrees one.
* `Turing.MultiTapeTM.computableInDegree_add`, `Turing.MultiTapeTM.computableInDegree_mul`:
  plain binary addition (quadratic) and multiplication (cubic).
* `Turing.MultiTapeTM.ComputableInO.comp_enc`: reuse a bit-word computation on encoded
  instances, with bounds evaluated on their encodings.
* `Turing.MultiTapeTM.ComputableInO.lengthUnary`: compute bit-word length in unary within
  linear time and space.
* `Turing.MultiTapeTM.ComputableInO.unary_two_pow`: compute `2 ^ n` from unary `n` within
  time `O((n + 1) * 2 ^ n)` and space `O(2 ^ n)`.
* `Turing.MultiTapeTM.ComputableInDegree.comp_le`, `.prod_le`, `.ite_le`: plain composition,
  pairing, and branching at requested degrees, retaining output-size bounds.
* `Turing.MultiTapeTM.ComputableInDegree.bitsReverse`,
  `Turing.MultiTapeTM.ComputableInDegree.bitsDropLast`,
  `Turing.MultiTapeTM.ComputableInDegree.bitsGetLast?ToList`,
  `Turing.MultiTapeTM.ComputableInDegree.bitsGetLast?`,
  `Turing.MultiTapeTM.ComputableInDegree.optionBoolToList`,
  `Turing.MultiTapeTM.ComputableInDegree.bitsAppend`,
  `Turing.MultiTapeTM.ComputableInDegree.unaryAdd`: plain degree rules for raw bit-list reversal,
  prefix, last-bit extraction, concatenation, and unary addition (alongside tidy counterparts).

## References

Uses Christian Reitwiessner's degree calculus and streaming backend; see the source markers in
`Degree.lean` and `Complexity/Computability/Machines/Turing/MultiTape/Encodings/StreamFold.lean`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

universe u

namespace ComputableInDegree

/-- The first component of a pair computed with given degrees. -/
theorem fst' {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {d e : ℕ}
    {f : α → β₁ × β₂} (h : ComputableInDegree f encIn (encPair enc₁ enc₂) d e) :
    ComputableInDegree (fun x => (f x).1) encIn enc₁ (max d e) e :=
  ((fst enc₁ enc₂).comp h).mono

/-- The second component of a pair computed with given degrees. -/
theorem snd' {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {d e : ℕ}
    {f : α → β₁ × β₂} (h : ComputableInDegree f encIn (encPair enc₁ enc₂) d e) :
    ComputableInDegree (fun x => (f x).2) encIn enc₂ (max d e) e :=
  ((snd enc₁ enc₂).comp h).mono

/-- `List.headD` on any list encoding. -/
theorem headD {β : Type*} {enc₁ : β ↪ List Bool} {enc : List β ↪ List Bool}
    [ListEncoding enc₁ enc] (d : β) :
    ComputableInDegree (fun l => l.headD d) enc enc₁ 1 1 :=
  ListEncoding.headD d

/-- `List.tail` on any list encoding. -/
theorem tail {β : Type*} {enc₁ : β ↪ List Bool} {enc : List β ↪ List Bool}
    [ListEncoding enc₁ enc] :
    ComputableInDegree List.tail enc enc 1 1 :=
  ListEncoding.tail (enc₁ := enc₁)

/-- `List.isEmpty` on any list encoding. -/
theorem isEmpty {β : Type*} {enc₁ : β ↪ List Bool} {enc : List β ↪ List Bool}
    [ListEncoding enc₁ enc] :
    ComputableInDegree List.isEmpty enc encBool 1 1 :=
  ListEncoding.isEmpty (enc₁ := enc₁)

/-- **Left folds with bounds of given degrees**, compiled directly from plain degree
certificates. -/
theorem foldl' {γ α β : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    [ListEncoding encA encL] [hS : SizedListEncoding encA encL]
    {list : γ → List α} {init : γ → β} {step : β → α → β} {dL eL dI eI dS eS b : ℕ}
    (hlist : ComputableInDegree list encIn encL dL eL)
    (hinit : ComputableInDegree init encIn encB dI eI)
    (hstep : ComputableInDegree (fun p : β × α => step p.1 p.2) (encPair encB encA) encB dS eS)
    {B : γ → ℕ} (hB : DegreeBounded (fun x => (encIn x).length) B b)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableInDegree (fun x => (list x).foldl step (init x)) encIn encB
      (max (max dL dI) (eL + max 1 dS * max b eL)) b := by
  have hl := hlist.2
  obtain ⟨t₁, s₁, ht₁, hs₁, kl, Ql, _, tml, h₁⟩ := Internal.NormalForm.degree hlist
  obtain ⟨t₂, s₂, ht₂, hs₂, ki, Qi, _, tmi, h₂⟩ := Internal.NormalForm.degree hinit
  obtain ⟨tS, sS, ⟨ct, htS⟩, ⟨cs, hsS⟩, ks, Qs, _, tms, hS'⟩ := Internal.NormalForm.degree hstep
  set a := max b eL
  set D := max 1 dS * a
  have haMax : DegreeBounded (fun x => (encIn x).length)
      (fun x => 2 * B x + 1 + (encL (list x)).length) a :=
    ((hB.smul 2).add_const 1).add_max hl
  have hlMax : DegreeBounded (fun x => (encIn x).length)
      (fun x => 2 * (encL (list x)).length + 1 + B x) a :=
    ((hl.mono_deg (le_max_right _ _)).smul 2 |>.add_const 1).add (hB.mono_deg (le_max_left _ _))
  have hround {c : ℕ} : DegreeBounded (fun x => (encIn x).length)
      (fun x => c * (2 * B x + 1 + (encL (list x)).length + 1) ^ dS) D :=
    (DegreeBounded.comp (size' := id) (v := fun n => c * (n + 1) ^ dS) ⟨c, fun _ => le_rfl⟩
      haMax).mono_deg (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (le_max_right _ _))
  have hargs : ∀ x i (hi : i < (list x).length),
      (encPair encB encA (((list x).take i).foldl step (init x), (list x)[i])).length ≤
        2 * B x + 1 + (encL (list x)).length := fun x i hi => by
    have h₁ := hstates x i hi.le
    have h₂ := hS.length_elem_le (list x) _ (List.getElem_mem hi)
    simp only [length_encPair]
    omega
  have hrest : ∀ x, ∀ i ≤ (list x).length,
      (encPair encL encB ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤
        2 * (encL (list x)).length + 1 + B x := fun x i hi => by
    have h₁ := hstates x i hi
    have h₂ := hS.length_drop_le (list x) i
    simp only [length_encPair]
    omega
  have haD : a ≤ D := Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.one_pos (le_max_left _ _))
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := Internal.FoldCompiler.foldl (encA := encA) (encL := encL)
    (encBA := encPair encB encA) (encS := encPair encL encB)
    (encO := encOption (encPair encL encB))
    (t := fun x => t₁ x + t₂ x) (s := fun x => s₁ x + s₂ x)
    (fun x => (h₁ x).mono (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    (fun x => (h₂ x).mono (Nat.le_add_left _ _) (Nat.le_add_left _ _)) hS'
    (tMax := fun x => ct * (2 * B x + 1 + (encL (list x)).length + 1) ^ dS)
    (sMax := fun x => cs * (2 * B x + 1 + (encL (list x)).length + 1) ^ dS)
    (lMax := fun x => 2 * (encL (list x)).length + 1 + B x)
    (fun x i hi => (htS _).trans (Nat.mul_le_mul_left ct (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hargs x i hi) 1) dS)))
    (fun x i hi => (hsS _).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hargs x i hi) 1) dS))) hrest
  have hd₀ : max dL dI ≤ max (max dL dI) (eL + D) := le_max_left _ _
  have hd₁ : eL + D ≤ max (max dL dI) (eL + D) := le_max_right _ _
  have hlen : DegreeBounded (fun x => (encIn x).length) (fun x => (list x).length + 1) eL :=
    (hl.add_const 1).mono fun x => Nat.add_le_add_right (hS.length_le _) 1
  have ht := ht₁.add_max ht₂
  have hs := hs₁.add_max hs₂
  refine ⟨⟨_, _, ((ht.mono_deg hd₀).add ((hlen.mul ((hround.add (hlMax.mono_deg haD)).add_const
    1)).mono_deg hd₁)).smul c, ((((hs.mono_deg hd₀).add (hround.mono_deg (by omega))).add
      (hlMax.mono_deg (by omega))).add_const 1).smul c,
    k, Q, hfin, tm, fun x => (htm x).computesInTimeAndSpace⟩, hB.mono fun x => ?_⟩
  simpa using hstates x _ le_rfl

/-- **Left folds with a parameter**, keeping `par x` in the fold state. -/
theorem foldlWith {γ α β π : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encP : π ↪ List Bool} [ListEncoding encA encL] [SizedListEncoding encA encL]
    {par : γ → π} {list : γ → List α} {init : γ → β} {step : π → β → α → β}
    {dP eP dL eL dI eI dS eS b : ℕ}
    (hpar : ComputableInDegree par encIn encP dP eP)
    (hlist : ComputableInDegree list encIn encL dL eL)
    (hinit : ComputableInDegree init encIn encB dI eI)
    (hstep : ComputableInDegree (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB dS eS)
    {B : γ → ℕ} (hB : DegreeBounded (fun x => (encIn x).length) B b)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableInDegree (fun x => (list x).foldl (step (par x)) (init x)) encIn encB
      (max (max dL (max dP dI)) (eL + max 1 dS * max (max eP b) eL)) b := by
  have heq (l : List α) (s : π × β) :
      l.foldl (fun s a => (s.1, step s.1 s.2 a)) s = (s.1, l.foldl (step s.1) s.2) :=
    List.foldl_hom (fun acc => (s.1, acc)) (fun _ _ => rfl)
  have hfold := foldl' (encB := encPair encP encB) hlist
    (hpar.prod hinit) (step := fun s a => (s.1, step s.1 s.2 a))
    (((fst encP encB).comp (fst (encPair encP encB) encA)).prod hstep)
    (B := fun x => 2 * (encP (par x)).length + 1 + B x)
    ((((hpar.2.mono_deg (le_max_left eP b)).smul 2).add_const 1).add
      (hB.mono_deg (le_max_right eP b)))
    (fun x i hi => by
      have := hstates x i hi
      rw [heq]
      simp only [length_encPair]
      omega)
  have h := (snd encP encB).comp hfold
  have hf : (Prod.snd ∘ fun x => (list x).foldl (fun s a => (s.1, step s.1 s.2 a))
      (par x, init x)) = fun x => (list x).foldl (step (par x)) (init x) := by
    funext x
    simp [heq]
  rw [hf, show max 1 (max (max 1 (1 * 1)) dS) = max 1 dS by omega, Nat.mul_one] at h
  have hY : max eP b ≤ max (max dL (max dP dI)) (eL + max 1 dS * max (max eP b) eL) :=
    le_max_of_le_right (le_add_left ((le_max_left _ eL).trans
      (Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.one_pos (le_max_left _ _)))))
  exact ⟨(h.mono (max_le le_rfl hY) le_rfl).1, hB.mono fun x => by simpa using hstates x _ le_rfl⟩

/-- Adding an element in front of a framed list: the identity on encoded words. -/
theorem cons {α : Type} (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : α × List α => p.1 :: p.2) (encPair enc (encList enc))
      (encList enc) 1 1 :=
  of_eq fun _ => rfl

/-- Adding an element at the end of a framed list. -/
theorem snoc {α : Type} (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × α => p.1 ++ [p.2]) (encPair (encList enc) enc)
      (encList enc) 1 1 :=
  ((fst (encList enc) enc).append ((ComputableInDegree.of_frame (f := id) (encIn := enc)
      (encMid := encFramed enc) fun _ => rfl).comp (snd (encList enc) enc))
    (enc₂ := encFramed enc) fun _ => by simp).mono

/-- Concatenating two framed lists. -/
theorem listAppend {α : Type} (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × List α => p.1 ++ p.2)
      (encPair (encList enc) (encList enc)) (encList enc) 1 1 :=
  ((fst (encList enc) (encList enc)).append (snd (encList enc) (encList enc))
    fun _ => by simp).mono

/-- Truncated subtraction of unary numbers. -/
theorem unary_sub :
    ComputableInDegree (fun p : ℕ × ℕ => p.1 - p.2) (encPair encUnary encUnary)
      encUnary 2 1 := by
  have hrep (a b : ℕ) : (List.replicate b true).foldl (fun n _ => n - 1) a = a - b := by
    induction b generalizing a with
    | zero => rfl
    | succ b ih => rw [List.replicate_succ, List.foldl_cons, ih]; omega
  have hfold := foldl' (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun p : ℕ × ℕ => List.replicate p.2 true) (step := fun n _ => n - 1)
    ((of_eq (f := fun n => List.replicate n true) (encIn := encUnary) (encMid := encBits)
      fun _ => rfl).comp (snd encUnary encUnary))
    (fst encUnary encUnary) (unary_pred.comp (fst encUnary encBool))
    (B := fun p => (encPair encUnary encUnary p).length) .self (fun p i _ => by
      rw [List.take_replicate, hrep]
      simp only [encPair_apply, encUnary_apply, List.length_append, length_frame,
        List.length_replicate]
      omega)
  convert hfold.mono (d' := 2) (e' := 1) using 1
  funext p
  rw [hrep]

/-- The minimum of unary numbers. -/
theorem unary_min :
    ComputableInDegree (fun p : ℕ × ℕ => min p.1 p.2) (encPair encUnary encUnary)
      encUnary 2 1 := by
  convert (unary_sub.comp ((fst encUnary encUnary).prod unary_sub)).mono (d' := 2) (e' := 1)
    using 1
  funext p
  simp only [Function.comp_apply]
  omega

private def intSuccT : Transducer Bool (Fin 3) where
  q₀ := 0
  step q b := match q, b with
    | 0, false => (2, [false, true])
    | 0, true => (1, [])
    | 1, b => (2, [b])
    | _, b => (2, [b])
  final q := if q = 1 then [false] else []
  length_step_le q b := by fin_cases q <;> cases b <;> simp
  length_final_le q := by split_ifs <;> simp

private def intPredT : Transducer Bool (Fin 3) where
  q₀ := 0
  step q b := match q, b with
    | 0, false => (1, [])
    | 0, true => (2, [true, true])
    | 1, _ => (2, [false])
    | _, b => (2, [b])
  final q := if q = 1 then [true] else []
  length_step_le q b := by fin_cases q <;> cases b <;> simp
  length_final_le q := by split_ifs <;> simp

/-- Adding one on unary-magnitude signed integers. -/
theorem int_succ : ComputableInDegree (· + 1) encInt encInt 1 1 := by
  refine of_transducer intSuccT fun z => ?_
  have hc := Transducer.run_eq_self intSuccT 2 (fun b => by cases b <;> rfl) rfl
  rcases z with n | _ | n
  · rw [show intSuccT.q₀ = 0 from rfl]
    simp only [encInt_ofNat, Transducer.run_cons]
    change false :: true :: List.replicate n true =
      [false, true] ++ intSuccT.run 2 (List.replicate n true)
    simp [hc]
  · rfl
  · change encInt (Int.negSucc n) =
      intSuccT.run 0 (true :: true :: List.replicate n true)
    simp only [encInt_negSucc, Transducer.run_cons]
    change true :: List.replicate n true =
      [] ++ ([true] ++ intSuccT.run 2 (List.replicate n true))
    simp [hc]

/-- Subtracting one on unary-magnitude signed integers. -/
theorem int_pred : ComputableInDegree (· - 1) encInt encInt 1 1 := by
  refine of_transducer intPredT fun z => ?_
  have hc := Transducer.run_eq_self intPredT 2 (fun b => by cases b <;> rfl) rfl
  rcases z with (_ | n) | n
  · rfl
  · rw [show Int.ofNat (n + 1) - 1 = Int.ofNat n by simp, show intPredT.q₀ = 0 from rfl]
    simp only [encInt_ofNat, List.replicate_succ, Transducer.run_cons]
    change false :: List.replicate n true =
      [] ++ ([false] ++ intPredT.run 2 (List.replicate n true))
    simp [hc]
  · change encInt (Int.negSucc (n + 1)) =
      intPredT.run 0 (true :: List.replicate n true)
    simp only [encInt_negSucc, List.replicate_succ, Transducer.run_cons]
    change true :: true :: List.replicate n true =
      [true, true] ++ intPredT.run 2 (List.replicate n true)
    simp [hc]

/-- Equality of bit words in quadratic time/space and constant output length. -/
theorem eqWords :
    ComputableInDegree (fun p : List Bool × List Bool => decide (p.1 = p.2))
      (encPair encBits encBits) encBool 2 0 := by
  have hfold := foldl' (encA := encBool) (encL := encBits)
    (encB := encPair encBits encBool) (fst encBits encBits)
    ((snd encBits encBits).prod (const true)) eqWordsStep
    (B := fun p => 2 * (encPair encBits encBits p).length + 2)
    ((DegreeBounded.self.smul 2).add_const 2)
    (fun p i _ => by
      rw [show ((p.1.take i).foldl EqWords.step (p.2, true)) =
        ((p.2.drop (p.1.take i).length), ((p.1.take i).foldl EqWords.step (p.2, true)).2) from
          Prod.ext (EqWords.foldl_fst _ _ _) rfl]
      simp only [encPair_apply, encBits_apply, encBool_apply, List.length_append, length_frame,
        List.length_drop, List.length_singleton]
      omega)
  have h : ComputableInDegree (_ ∘ _) _ encBool 2 0 := (eqWordsResult.comp hfold).mono
  convert h using 1
  funext p
  simpa using (EqWords.foldl_result p.1 p.2 true).symm

/-- Equality for any encoding in quadratic time/space and constant output length. -/
theorem eq {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : α × α => decide (p.1 = p.2)) (encPair enc enc) encBool 2 0 := by
  have h : ComputableInDegree (_ ∘ _) _ encBool 2 0 := (eqWords.comp (of_eq
    (f := fun p : α × α => (enc p.1, enc p.2)) (encIn := encPair enc enc)
    (encMid := encPair encBits encBits) fun _ => rfl)).mono
  convert h using 1
  funext p
  simp [enc.injective.eq_iff]

end ComputableInDegree

/-- **Addition is computable in quadratic time and space**, with linear output length, in the
binary encoding. -/
theorem computableInDegree_add :
    ComputableInDegree (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat 2 1 :=
  ComputableInO.natAdd.computableInDegree
    ⟨1, fun _ => by simp⟩ ⟨1, fun _ => by simp⟩ (by decide)

/-- **Multiplication is computable in cubic time and space**, with linear output length, in the
binary encoding. -/
theorem computableInDegree_mul :
    ComputableInDegree (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat 3 1 :=
  ComputableInO.natMul.computableInDegree ⟨1, fun _ => by simp⟩ ⟨1, fun _ => by simp⟩ (by decide)

attribute [fun_prop] ComputableInDegree
attribute [fun_prop] ComputableInDegree.const ComputableInDegree.fst
  ComputableInDegree.snd ComputableInDegree.comp ComputableInDegree.prod
  ComputableInDegree.fst' ComputableInDegree.snd'
  ComputableInDegree.cons ComputableInDegree.snoc
  ComputableInDegree.listAppend ComputableInDegree.isSome
  ComputableInDegree.unary_succ ComputableInDegree.unary_pred
  ComputableInDegree.unary_sub ComputableInDegree.unary_min
  ComputableInDegree.int_succ ComputableInDegree.int_pred

namespace ComputableInDegree

/-- The result encoding fixes the element encoding, without reversing `ListEncoding` inference. -/
@[fun_prop]
theorem listTail {α : Type*} (enc : α ↪ List Bool) :
    ComputableInDegree List.tail (encList enc) (encList enc) 1 1 :=
  tail (enc₁ := enc)

/-- The framed input list determines the encoding of its head, including a fixed fallback. -/
@[fun_prop]
theorem listHeadD {α : Type*} (enc : α ↪ List Bool) (fallback : α) :
    ComputableInDegree (fun l => l.headD fallback) (encList enc) enc 1 1 :=
  headD (enc₁ := enc) fallback

/-- Testing a framed list for emptiness. -/
@[fun_prop]
theorem listIsEmpty {α : Type*} (enc : α ↪ List Bool) :
    ComputableInDegree List.isEmpty (encList enc) encBool 1 1 :=
  isEmpty (enc₁ := enc)

/-- The option encoding determines the encoding used for the payload and fallback. -/
@[fun_prop]
theorem optionGetD {α : Type*} (enc : α ↪ List Bool) (fallback : α) :
    ComputableInDegree (fun o => o.getD fallback) (encOption enc) enc 1 1 :=
  getD (enc₁ := enc) fallback

/-- Copy an encoded value. This identity rule also lets `fun_prop` retain a shared let binding. -/
@[fun_prop]
theorem id' {α : Type*} {enc : α ↪ List Bool} :
    ComputableInDegree (fun x : α => x) enc enc 1 1 :=
  of_eq fun _ => rfl

/-- Reverse a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsReverse :
    ComputableInDegree List.reverse encBits encBits 1 1 :=
  of_bounds ⟨2, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableTidilyInTimeAndSpace.reverse_bits.computableInTimeAndSpace

/-- Drop the last bit of a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsDropLast :
    ComputableInDegree List.dropLast encBits encBits 1 1 :=
  of_bounds ⟨8, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableTidilyInTimeAndSpace.dropLast_bits.computableInTimeAndSpace

/-- Extract the last bit of a raw bit list as a 0-or-1-element list in linear time and constant
output size. -/
@[fun_prop]
theorem bitsGetLast?ToList :
    ComputableInDegree (fun l : List Bool => l.getLast?.toList) encBits encBits 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableTidilyInTimeAndSpace.getLast?_toList_bits.computableInTimeAndSpace⟩,
    ⟨1, fun l => by simp [Option.length_toList_le]⟩⟩

/-- Extract the last bit of a raw bit list as an `Option Bool` in linear time and constant output
size. -/
@[fun_prop]
theorem bitsGetLast? :
    ComputableInDegree (List.getLast? (α := Bool)) encBits (encOption encBool) 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableTidilyInTimeAndSpace.getLast?_bits.computableInTimeAndSpace⟩,
    ⟨2, fun l => by cases h : l.getLast? <;> simp [h]⟩⟩

/-- Convert an `Option Bool` to a 0-or-1-element bit list in linear time and linear output size. -/
@[fun_prop]
theorem optionBoolToList :
    ComputableInDegree (Option.toList (α := Bool)) (encOption encBool) encBits 1 1 :=
  (Internal.DecoderWords.tail_degree.comp
    (of_eq (f := encOption encBool) (encIn := encOption encBool) (encMid := encBits)
      fun _ => rfl)).of_enc_eq fun o => by cases o <;> rfl

/-- Concatenate two raw bit lists while preserving their time and output degrees independently. -/
@[fun_prop]
theorem bitsAppend {α : Type*} {encIn : α ↪ List Bool} {f g : α → List Bool}
    {df ef dg eg d e : ℕ}
    (hf : ComputableInDegree f encIn encBits df ef)
    (hg : ComputableInDegree g encIn encBits dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => f x ++ g x) encIn encBits d e :=
  (hf.append hg fun _ => rfl).mono hd he

/-- Add two unary natural numbers while preserving their time and output degrees independently. -/
@[fun_prop]
theorem unaryAdd {α : Type*} {encIn : α ↪ List Bool} {f g : α → ℕ}
    {df ef dg eg d e : ℕ}
    (hf : ComputableInDegree f encIn encUnary df ef)
    (hg : ComputableInDegree g encIn encUnary dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => f x + g x) encIn encUnary d e :=
  (hf.append hg fun _ => List.replicate_add _ _ true).mono hd he

/-- Compose using the intermediate output size. The computation premises determine the degrees
before arithmetic compares them with the requested bound. -/
@[fun_prop]
theorem comp_le {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β} {df ef dg eg d e : ℕ}
    (hg : ComputableInDegree g encIn encMid dg eg)
    (hf : ComputableInDegree f encMid encOut df ef)
    (hd : max dg (eg * df) ≤ d) (he : eg * ef ≤ e) :
    ComputableInDegree (fun x => f (g x)) encIn encOut d e :=
  (hf.comp hg).mono hd he

/-- Pair two results while preserving their output degrees independently of computation time. -/
@[fun_prop]
theorem prod_le {α β γ : Type u} {encIn : α ↪ List Bool} {encF : β ↪ List Bool}
    {encG : γ ↪ List Bool} {f : α → β} {g : α → γ} {df ef dg eg d e : ℕ}
    (hf : ComputableInDegree f encIn encF df ef)
    (hg : ComputableInDegree g encIn encG dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => (f x, g x)) encIn (encPair encF encG) d e :=
  (hf.prod hg).mono hd he

/-- Branching on a computed Boolean, retaining each branch's output degree. -/
@[fun_prop]
theorem ite_le {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {condition : α → Bool} {f g : α → β} {dc ec df ef dg eg d e : ℕ}
    (hc : ComputableInDegree condition encIn encBool dc ec)
    (hf : ComputableInDegree f encIn encOut df ef)
    (hg : ComputableInDegree g encIn encOut dg eg)
    (hd : max dc (max df dg) ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => if condition x then f x else g x) encIn encOut d e :=
  (hc.ite (hf.restrict _) (hg.restrict _)).mono hd he

end ComputableInDegree

attribute [fun_prop] ComputableTidilyInDegree ComputableTidilyInO
attribute [fun_prop] ComputableTidilyInTimeAndSpace
attribute [fun_prop] ComputableTidilyInDegree.const ComputableTidilyInDegree.fst
  ComputableTidilyInDegree.snd ComputableTidilyInDegree.comp ComputableTidilyInDegree.prod
  ComputableTidilyInDegree.fst' ComputableTidilyInDegree.snd'
  ComputableTidilyInDegree.cons ComputableTidilyInDegree.snoc
  ComputableTidilyInDegree.listAppend ComputableTidilyInDegree.isSome
  ComputableTidilyInDegree.unary_succ ComputableTidilyInDegree.unary_pred
  ComputableTidilyInDegree.unary_sub ComputableTidilyInDegree.unary_min
  ComputableTidilyInDegree.int_succ ComputableTidilyInDegree.int_pred
  ComputableTidilyInO.foldl_bits_finite ComputableTidilyInTimeAndSpace.map_bits
  ComputableTidilyInTimeAndSpace.reverse_bits ComputableTidilyInTimeAndSpace.dropLast_bits
  ComputableTidilyInTimeAndSpace.length_bits ComputableTidilyInTimeAndSpace.getLast?_toList_bits
  ComputableTidilyInTimeAndSpace.getLast?_bits

namespace ComputableTidilyInDegree

/-- The result encoding fixes the element encoding, without reversing `ListEncoding` inference. -/
@[fun_prop]
theorem listTail {α : Type*} (enc : α ↪ List Bool) :
    ComputableTidilyInDegree List.tail (encList enc) (encList enc) 1 1 :=
  tail (enc₁ := enc)

/-- The framed input list determines the encoding of its head, including a fixed fallback. -/
@[fun_prop]
theorem listHeadD {α : Type*} (enc : α ↪ List Bool) (fallback : α) :
    ComputableTidilyInDegree (fun l => l.headD fallback) (encList enc) enc 1 1 :=
  headD (enc₁ := enc) fallback

/-- Testing a framed list for emptiness. -/
@[fun_prop]
theorem listIsEmpty {α : Type*} (enc : α ↪ List Bool) :
    ComputableTidilyInDegree List.isEmpty (encList enc) encBool 1 1 :=
  isEmpty (enc₁ := enc)

/-- The option encoding determines the encoding used for the payload and fallback. -/
@[fun_prop]
theorem optionGetD {α : Type*} (enc : α ↪ List Bool) (fallback : α) :
    ComputableTidilyInDegree (fun o => o.getD fallback) (encOption enc) enc 1 1 :=
  getD (enc₁ := enc) fallback

/-- Copy an encoded value. This identity rule also lets `fun_prop` retain a shared let binding. -/
@[fun_prop]
theorem id' {α : Type*} {enc : α ↪ List Bool} :
    ComputableTidilyInDegree (fun x : α => x) enc enc 1 1 :=
  of_eq fun _ => rfl

/-- Reverse a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsReverse :
    ComputableTidilyInDegree List.reverse encBits encBits 1 1 :=
  of_bounds ⟨2, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableTidilyInTimeAndSpace.reverse_bits

/-- Drop the last bit of a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsDropLast :
    ComputableTidilyInDegree List.dropLast encBits encBits 1 1 :=
  of_bounds ⟨8, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableTidilyInTimeAndSpace.dropLast_bits

/-- Extract the last bit of a raw bit list as a 0-or-1-element list in linear time and constant
output size. -/
@[fun_prop]
theorem bitsGetLast?ToList :
    ComputableTidilyInDegree (fun l : List Bool => l.getLast?.toList) encBits encBits 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableTidilyInTimeAndSpace.getLast?_toList_bits⟩,
    ⟨1, fun l => by simp [Option.length_toList_le]⟩⟩

/-- Extract the last bit of a raw bit list as an `Option Bool` in linear time and constant output
size. -/
@[fun_prop]
theorem bitsGetLast? :
    ComputableTidilyInDegree (List.getLast? (α := Bool)) encBits (encOption encBool) 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableTidilyInTimeAndSpace.getLast?_bits⟩,
    ⟨2, fun l => by cases h : l.getLast? <;> simp [h]⟩⟩

/-- Convert an `Option Bool` to a 0-or-1-element bit list in linear time and linear output size. -/
@[fun_prop]
theorem optionBoolToList :
    ComputableTidilyInDegree (Option.toList (α := Bool)) (encOption encBool) encBits 1 1 :=
  of_linear (.of_tail fun o => by cases o <;> rfl)

/-- Concatenate two raw bit lists while preserving their time and output degrees independently. -/
@[fun_prop]
theorem bitsAppend {α : Type*} {encIn : α ↪ List Bool} {f g : α → List Bool}
    {df ef dg eg d e : ℕ}
    (hf : ComputableTidilyInDegree f encIn encBits df ef)
    (hg : ComputableTidilyInDegree g encIn encBits dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => f x ++ g x) encIn encBits d e :=
  (hf.append hg fun _ => rfl).mono hd he

/-- Add two unary natural numbers while preserving their time and output degrees independently. -/
@[fun_prop]
theorem unaryAdd {α : Type*} {encIn : α ↪ List Bool} {f g : α → ℕ}
    {df ef dg eg d e : ℕ}
    (hf : ComputableTidilyInDegree f encIn encUnary df ef)
    (hg : ComputableTidilyInDegree g encIn encUnary dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => f x + g x) encIn encUnary d e :=
  (hf.append hg fun _ => List.replicate_add _ _ true).mono hd he

/-- Compose using the intermediate output size. The computation premises determine the degrees
before arithmetic compares them with the requested bound. -/
@[fun_prop]
theorem comp_le {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β} {df ef dg eg d e : ℕ}
    (hg : ComputableTidilyInDegree g encIn encMid dg eg)
    (hf : ComputableTidilyInDegree f encMid encOut df ef)
    (hd : max dg (eg * df) ≤ d) (he : eg * ef ≤ e) :
    ComputableTidilyInDegree (fun x => f (g x)) encIn encOut d e :=
  (hf.comp hg).mono hd he

/-- Pair two results while preserving their output degrees independently of computation time. -/
@[fun_prop]
theorem prod_le {α β γ : Type u} {encIn : α ↪ List Bool} {encF : β ↪ List Bool}
    {encG : γ ↪ List Bool} {f : α → β} {g : α → γ} {df ef dg eg d e : ℕ}
    (hf : ComputableTidilyInDegree f encIn encF df ef)
    (hg : ComputableTidilyInDegree g encIn encG dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => (f x, g x)) encIn (encPair encF encG) d e :=
  (hf.prod hg).mono hd he

/-- Branching on a computed Boolean, retaining each branch's output degree. -/
@[fun_prop]
theorem ite_le {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {condition : α → Bool} {f g : α → β} {dc ec df ef dg eg d e : ℕ}
    (hc : ComputableTidilyInDegree condition encIn encBool dc ec)
    (hf : ComputableTidilyInDegree f encIn encOut df ef)
    (hg : ComputableTidilyInDegree g encIn encOut dg eg)
    (hd : max dc (max df dg) ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => if condition x then f x else g x) encIn encOut d e :=
  (hc.ite (hf.restrict _) (hg.restrict _)).mono hd he

end ComputableTidilyInDegree

namespace ComputableInO

variable {α β : Type} {encOut : β ↪ List Bool}

/-- A function of bit words computed within given bounds is computed by the same machine on encoded
instances. -/
theorem comp_enc {f : List Bool → β} {T S : List Bool → ℕ}
    (h : ComputableInO f encBits encOut T S) (enc : α ↪ List Bool) :
    ComputableInO (fun a => f (enc a)) enc encOut (fun a => T (enc a)) fun a => S (enc a) :=
  h.of_encIn_eq enc fun _ => rfl

/-- The length of a bit word in unary, within linear time and space, by the streaming machine of
`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.length_bits`. -/
theorem lengthUnary : ComputableInO (fun l : List Bool => l.length) encBits encUnary
    (fun l => l.length) fun l => l.length :=
  .of_bounds ComputableTidilyInTimeAndSpace.length_bits.computableInTimeAndSpace 8
    (fun l => by omega) (fun _ => Nat.zero_le _)
    fun l => by simp only [encUnary_apply, List.length_replicate]; omega

/-- Doubling `m` once for each element of a list of length `n` multiplies it by `2 ^ n`. -/
private theorem foldl_double (n m : ℕ) :
    (List.replicate n true).foldl (fun m _ => m + m) m = m * 2 ^ n := by
  rw [List.foldl_add_self_eq_mul_two_pow, List.length_replicate]

/-- **`2 ^ n` in unary**, by doubling `n` times, within time `O((n + 1) * 2 ^ n)` and space
`O(2 ^ n)`. -/
theorem unary_two_pow : ComputableInO (fun n : ℕ => 2 ^ n) encUnary encUnary
    (fun n => (n + 1) * 2 ^ n) fun n => 2 ^ n := by
  have hstep : ComputableInO (fun p : ℕ × Bool => p.1 + p.1) (encPair encUnary encBool)
      encUnary (fun p => (encPair encUnary encBool p).length)
      fun p => (encPair encUnary encBool p).length :=
    (ComputableInDegree.unaryAdd (ComputableInDegree.fst encUnary encBool)
      (ComputableInDegree.fst encUnary encBool) le_rfl le_rfl).inO_one
  have hstate (n i : ℕ) : (encUnary (((List.replicate n true).take i).foldl
      (fun m _ => m + m) 1)).length ≤ 2 ^ n := by
    rw [List.take_replicate, foldl_double, encUnary_apply, List.length_replicate, one_mul]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _)
  have h := foldl (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun n : ℕ => List.replicate n true) (init := fun _ => 1)
    (step := fun m _ => m + m)
    (of_linear (.of_eq (f := fun n : ℕ => List.replicate n true) (encIn := encUnary)
      (encMid := encBits) fun _ => rfl)) (const 1) hstep
    (R := fun n => 2 * 2 ^ n + 2) (Q := fun n => 2 * 2 ^ n + 2) (B := fun n => 2 ^ n)
    (fun n i _ => by
      have := hstate n i
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    (fun n i _ => by
      have := hstate n i
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    fun n i _ => hstate n i
  refine (h.mono 8 (fun n => ?_) fun n => ?_).of_enc_eq fun n => ?_
  · have h₁ : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    have h₂ := Nat.mul_le_mul_left (n + 1) h₁
    simp only [encUnary_apply, encBits_apply, List.length_replicate]
    nlinarith
  · have h₁ : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    simp only [encUnary_apply, encBits_apply, List.length_replicate]
    omega
  · rw [foldl_double, one_mul]

end ComputableInO

end Turing.MultiTapeTM



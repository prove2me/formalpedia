-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:47:15.720272+00:00
-- url     : https://prove2.me/theorems/47b0015a-8fb3-4432-aba6-bc04e65d59ae
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives — Direct plain list primitives
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Finite-state word transducers implement unary successor and append a framed element to a list.
--   Their machine clocks are linear and use no work tapes. The proofs do not invoke a tidy
--   computability calculus.
--
--   **Contents.** The module is published as a whole: 33 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimeListPrimitives.lean

/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeLoops
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_UnaryMachines
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Append

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct plain list primitives

Finite-state word transducers implement unary successor and append a framed element to a list.
Their machine clocks are linear and use no work tapes. The proofs do not invoke a tidy
computability calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib Internal.Unary

private theorem ofTransducer {Q : Type} [Finite Q] (τ : Transducer Bool Q)
    {α β : Type*} {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
    (hf : ∀ a, output (f a) = τ.run τ.q₀ (input a)) :
    ComputableInPolyTime f input output := by
  refine ⟨fun n => 2 * n + 3, fun _ => 0, by fun_prop, by fun_prop,
    0, _, inferInstance, τ.toTM, fun a => ?_⟩
  rw [hf a]
  exact τ.computesInTimeAndSpace_toTM (input a)

private theorem appendEncoded {γ α β δ : Type*} {input : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {output : δ ↪ List Bool}
    {left : γ → α} {right : γ → β} {result : γ → δ}
    (hleft : ComputableInPolyTime left input encA)
    (hright : ComputableInPolyTime right input encB)
    (hout : ∀ x, output (result x) = encA (left x) ++ encB (right x)) :
    ComputableInPolyTime result input output := by
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := Internal.NormalForm.polyTime hleft
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := Internal.NormalForm.polyTime hright
  let bound := fun n => c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ + 2 * max k₁ k₂
  have hb : PolynomiallyBounded bound := by dsimp [bound]; fun_prop
  refine ⟨bound, bound, hb, hb, max k₁ k₂, S₁ ⊕ S₂, inferInstance,
    appendTM tm₁ tm₂, fun x => ?_⟩
  rw [hout x]
  exact (((h₁ x).append (h₂ x)).mono (Nat.le_add_right _ _) le_rfl).computesInTimeAndSpace

private def snocTransducer : Transducer Bool (Option Bool) where
  q₀ := none
  step
    | none, true => (some false, [])
    | none, false => (some true, [])
    | some false, bit => (none, [bit])
    | some true, bit => (some true, [true, bit])
  final _ := [false]
  length_step_le q bit := by
    cases q with
    | none => cases bit <;> simp
    | some q => cases q <;> simp
  length_final_le _ := by decide

private theorem snocRunTail (word : List Bool) :
    snocTransducer.run (some true) word = frame word := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    change [true, bit] ++ snocTransducer.run (some true) word = true :: bit :: frame word
    rw [ih]
    rfl

private theorem snocRun (left right : List Bool) :
    snocTransducer.run none (frame left ++ right) = left ++ frame right := by
  induction left with
  | nil =>
    change snocTransducer.run (some true) right = frame right
    exact snocRunTail right
  | cons bit left ih =>
    change [bit] ++ snocTransducer.run none (frame left ++ right) =
      (bit :: left) ++ frame right
    rw [ih]
    rfl

private abbrev RangeState := ℕ × List ℕ

private abbrev rangeEncoding : RangeState ↪ List Bool :=
  encPair encUnary (encList encUnary)

private def rangeStep (state : RangeState) (_ : Bool) : RangeState :=
  (state.1 + 1, state.2 ++ [state.1])

private theorem rangeFold (n : ℕ) :
    (List.replicate n true).foldl rangeStep (0, []) = (n, List.range n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, rangeStep, List.range_succ]

private theorem rangeEncodingSize (n : ℕ) :
    (encList encUnary (List.range n)).length = n * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ]
    change ((List.range n ++ [n]).flatMap (frame ∘ encUnary)).length = (n + 1) * (n + 1)
    rw [List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, Function.comp_apply, List.append_nil]
    change (encList encUnary (List.range n)).length + (frame (encUnary n)).length =
      (n + 1) * (n + 1)
    rw [ih, length_frame]
    simp only [encUnary_apply, List.length_replicate]
    nlinarith

private theorem rangeStateSize (n : ℕ) :
    (rangeEncoding (n, List.range n)).length = 2 * n + 1 + n * n := by
  change (encPair encUnary (encList encUnary) (n, List.range n)).length = _
  rw [length_encPair]
  simp only [encUnary_apply, List.length_replicate, rangeEncodingSize]

private def rangeOutputBound (n : ℕ) : ℕ := n * (2 * n + 1)

private theorem foldlAll {α : Type} (test : α → Bool) (list : List α) (init : Bool) :
    list.foldl (fun state value => state && test value) init = (init && list.all test) := by
  induction list generalizing init with
  | nil => simp
  | cons a list ih => simp [ih, Bool.and_assoc]

private theorem foldlReverse {α : Type} (word acc : List α) :
    word.foldl (fun reversed bit => bit :: reversed) acc = word.reverse ++ acc := by
  induction word generalizing acc with
  | nil => simp
  | cons bit word ih => simp [ih, List.reverse_cons, List.append_assoc]

/-- Appending mapped elements in a left fold retains the initial output prefix. -/
theorem foldlMap {α β : Type} (f : α → β) (list : List α) (acc : List β) :
    list.foldl (fun mapped value => mapped ++ [f value]) acc = acc ++ list.map f := by
  induction list generalizing acc with
  | nil => simp
  | cons a list ih => simp [ih, List.append_assoc]

namespace ComputableInPolyTime

/-- Unary successor is a direct finite-state transduction, including the empty word for zero. -/
@[fun_prop]
theorem unary_succ : ComputableInPolyTime (· + 1) encUnary encUnary := by
  apply ofTransducer unarySuccTransducer
  intro n
  change List.replicate (n + 1) true =
    unarySuccTransducer.run true (List.replicate n true)
  rw [(unarySuccRun _).1]
  simp only [List.replicate_succ]

/-- Append one element to a framed list, for an arbitrary fixed element encoding. -/
@[fun_prop]
theorem snoc {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × α => p.1 ++ [p.2])
      (encPair (encList enc) enc) (encList enc) := by
  apply ofTransducer snocTransducer
  intro p
  change encList enc (p.1 ++ [p.2]) =
    snocTransducer.run none (Turing.MultiTapeTM.frame (encList enc p.1) ++ enc p.2)
  rw [snocRun]
  change ((p.1 ++ [p.2]).flatMap (Turing.MultiTapeTM.frame ∘ enc)) =
    p.1.flatMap (Turing.MultiTapeTM.frame ∘ enc) ++ Turing.MultiTapeTM.frame (enc p.2)
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    Function.comp_apply, List.append_nil]

/-- Prepend a computed bit to a computed word, retaining both input certificates. -/
@[fun_prop]
theorem bitsCons {γ : Type} {input : γ ↪ List Bool} {head : γ → Bool}
    {tail : γ → List Bool} (hhead : ComputableInPolyTime head input encBool)
    (htail : ComputableInPolyTime tail input encBits) :
    ComputableInPolyTime (fun x => head x :: tail x) input encBits :=
  appendEncoded hhead htail fun _ => rfl

/-- Reverse arbitrary bit strings with the direct prefix-bounded fold. -/
@[fun_prop]
theorem bitsReverse : ComputableInPolyTime List.reverse encBits encBits := by
  have hfold := foldl' (encA := encBool) (encL := encBits) (encB := encBits)
    (list := id) (init := fun _ => []) (step := fun reversed bit => bit :: reversed)
    id' (const []) (bitsCons (snd encBits encBool) (fst encBits encBool))
    (B := fun word => word.length) (by
      apply PolyBounded.of_forall_le 1 1
      intro word
      simp only [encBits_apply, Nat.pow_one, Nat.one_mul]
      omega) (by
      intro word i _
      rw [foldlReverse]
      simp only [encBits_apply, List.length_append, List.length_reverse,
        List.length_take, List.length_nil, Nat.add_zero]
      exact Nat.min_le_right _ _)
  simpa only [foldlReverse, List.append_nil, id_eq] using hfold

/-- Drop one symbol of an arbitrary word, reusing the existing word-codec machine. -/
@[fun_prop]
theorem bitsTail : ComputableInPolyTime List.tail encBits encBits := by
  exact (ListEncoding.tail (enc₁ := encBool) (enc := encBits)).computableInPolyTime

/-- Test whether the complete raw word is empty, with the Boolean result encoding fixed. -/
@[fun_prop]
theorem bitsIsEmpty : ComputableInPolyTime List.isEmpty encBits encBool := by
  exact (ListEncoding.isEmpty (enc₁ := encBool) (enc := encBits)).computableInPolyTime

/-- Drop the head of a list in any list encoding, reusing the encoding's linear-time machine. -/
@[fun_prop]
theorem tail {α : Type} {encA : α ↪ List Bool} {encL : List α ↪ List Bool}
    [ListEncoding encA encL] : ComputableInPolyTime (List.tail (α := α)) encL encL := by
  exact (ListEncoding.tail (enc₁ := encA) (enc := encL)).computableInPolyTime

/-- Test a list in any list encoding for emptiness, reusing the encoding's linear-time machine. -/
@[fun_prop]
theorem listIsEmpty {α : Type} {encA : α ↪ List Bool} {encL : List α ↪ List Bool}
    [ListEncoding encA encL] : ComputableInPolyTime (List.isEmpty (α := α)) encL encBool := by
  exact (ListEncoding.isEmpty (enc₁ := encA) (enc := encL)).computableInPolyTime

private theorem rangeStepCertificate :
    ComputableInPolyTime (fun p : RangeState × Bool => rangeStep p.1 p.2)
      (encPair rangeEncoding encBool) rangeEncoding := by
  have hstate := fst rangeEncoding encBool
  exact (unary_succ.comp hstate.fst').prod
    ((snoc encUnary).comp (hstate.snd'.prod hstate.fst'))

/-- Enumerate all naturals below a unary bound. Both the bound and each list element remain
unary; the reachable framed output has quadratic length. -/
@[fun_prop]
theorem range : ComputableInPolyTime List.range encUnary (encList encUnary) := by
  have hlist : ComputableInPolyTime (fun n : ℕ => List.replicate n true) encUnary encBits :=
    of_eq fun _ => rfl
  have hbound : PolyBounded (fun n => (encUnary n).length)
      (fun n => 2 * n + 1 + rangeOutputBound n) := by
    apply PolyBounded.of_forall_le 8 2
    intro n
    simp only [encUnary_apply, List.length_replicate]
    dsimp [rangeOutputBound]
    nlinarith
  have hfold := foldl' (encA := encBool) (encL := encBits) (encB := rangeEncoding)
    (list := fun n : ℕ => List.replicate n true) (init := fun _ => (0, [])) (step := rangeStep)
    hlist (const (0, [])) rangeStepCertificate hbound (by
      intro n i _
      rw [List.take_replicate, rangeFold, rangeStateSize]
      have hk := Nat.min_le_right i n
      have hsq := Nat.mul_le_mul hk hk
      dsimp [rangeOutputBound]
      nlinarith)
  simpa only [Function.comp_def, rangeFold] using (snd encUnary (encList encUnary)).comp hfold

/-- Test all elements of a computed framed list with the full original input captured by the
uniform callback machine. No finite-element assumption is needed. -/
@[fun_prop]
theorem allWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x => (list x).all (test x)) encIn encBool := by
  have houter := fst (encPair encIn encBool) encA
  have hvalue := snd (encPair encIn encBool) encA
  have hstep : ComputableInPolyTime
      (fun q : (γ × Bool) × α => q.1.2 && test q.1.1 q.2)
      (encPair (encPair encIn encBool) encA) encBool :=
    bool_and.comp (houter.snd'.prod (htest.comp (houter.fst'.prod hvalue)))
  have hfold := foldlWith (encA := encA) (encL := encList encA) (encP := encIn)
    (encB := encBool) (par := id) (list := list) (init := fun _ => true)
    (step := fun par state value => state && test par value)
    id' hlist (const true) hstep (PolyBounded.const 1) (by simp)
  simpa only [foldlAll, Bool.true_and, id_eq] using hfold

/-- For a fixed list, only its members need callback certificates. The index type may live in
any universe and needs neither an encoding nor a finite-type instance. -/
@[fun_prop]
theorem allConst {γ : Type} {encIn : γ ↪ List Bool} {ι : Type*} (l : List ι)
    {test : γ → ι → Bool}
    (htest : ∀ i ∈ l, ComputableInPolyTime (fun x => test x i) encIn encBool) :
    ComputableInPolyTime (fun x => l.all (test x)) encIn encBool := by
  induction l with
  | nil => exact const true
  | cons a l ih =>
    exact bool_and.comp ((htest a (List.mem_cons_self ..)).prod
      (ih fun b hb => htest b (List.mem_cons_of_mem _ hb)))

/-- Mapping a uniform encoded function over a runtime framed list is polynomial-time. The
callback's output bound follows from its actual machine, rather than an extra list premise. -/
@[fun_prop]
theorem map {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → β}
    (hf : ComputableInPolyTime f encA encB) :
    ComputableInPolyTime (List.map f) (encList encA) (encList encB) := by
  obtain ⟨c, d, hfsize⟩ := hf.polyBounded_length.exists_le
  let bound := fun n : ℕ => n * (2 * (c * (n + 1) ^ d) + 1)
  have hb : PolynomiallyBounded bound := by dsimp [bound]; fun_prop
  have hstep : ComputableInPolyTime (fun p : List β × α => p.1 ++ [f p.2])
      (encPair (encList encB) encA) (encList encB) :=
    (snoc encB).comp ((fst (encList encB) encA).prod (hf.comp (snd (encList encB) encA)))
  have hfold := foldl' (encA := encA) (encL := encList encA) (encB := encList encB)
    (list := id) (init := fun _ => []) (step := fun mapped value => mapped ++ [f value])
    id' (const []) hstep
    (PolyBounded.of_polynomiallyBounded (fun list : List α => (encList encA list).length) hb)
    (by
      intro list i _
      simp only [foldlMap, List.nil_append, id_eq]
      let n := (encList encA list).length
      have heach : ∀ b ∈ (list.take i).map f, (encB b).length ≤ c * (n + 1) ^ d := by
        intro b hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        have hain := (List.take_sublist i list).subset ha
        have haBound := SizedListEncoding.length_elem_le
          (encA := encA) (encL := encList encA) list a hain
        exact (hfsize a).trans (Nat.mul_le_mul_left c
          (Nat.pow_le_pow_left (Nat.add_le_add_right haBound 1) d))
      apply (length_encList_le encB _ heach).trans
      dsimp [bound]
      apply Nat.mul_le_mul_right
      simp only [List.length_map, List.length_take]
      exact (Nat.min_le_right i list.length).trans
        (SizedListEncoding.length_le (encA := encA) (encL := encList encA) list))
  simpa only [foldlMap, List.nil_append, id_eq] using hfold

/-- Reverse a computed word, fixing its raw intermediate encoding before proof search.
The input certificate may itself convert from another representation. -/
@[fun_prop]
theorem bitsReverseWithInput {γ : Type} {encIn : γ ↪ List Bool} {word : γ → List Bool}
    (hword : ComputableInPolyTime word encIn encBits) :
    ComputableInPolyTime (fun a => (word a).reverse) encIn encBits :=
  bitsReverse.comp hword

/-- Prepend computed data. The result encoding determines the element encoding before
`fun_prop` searches for the two component certificates. -/
@[fun_prop]
theorem cons' {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {head : γ → α} {tail : γ → List α}
    (hhead : ComputableInPolyTime head encIn encA)
    (htail : ComputableInPolyTime tail encIn (encList encA)) :
    ComputableInPolyTime (fun x => head x :: tail x) encIn (encList encA) := by
  have hframe : ComputableInPolyTime (fun a : α => a) encA (encFramed encA) :=
    ofTransducer Encodings.frameT fun a => (Encodings.frameT_run (encA a)).symm
  exact appendEncoded (hframe.comp hhead) htail fun _ => rfl

/-- Concatenate computed lists, inferring their shared encoding from the result. -/
@[fun_prop]
theorem listAppend' {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {left right : γ → List α}
    (hleft : ComputableInPolyTime left encIn (encList encA))
    (hright : ComputableInPolyTime right encIn (encList encA)) :
    ComputableInPolyTime (fun x => left x ++ right x) encIn (encList encA) := by
  apply appendEncoded hleft hright
  intro x
  change ((left x ++ right x).flatMap (Turing.MultiTapeTM.frame ∘ encA)) =
    (left x).flatMap (Turing.MultiTapeTM.frame ∘ encA) ++
      (right x).flatMap (Turing.MultiTapeTM.frame ∘ encA)
  exact List.flatMap_append

/-- Reverse a computed framed list, inferring its element encoding from the result. -/
@[fun_prop]
theorem listReverseWithInput {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {list : γ → List α} (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun a => (list a).reverse) encIn (encList encA) := by
  have hreverse : ComputableInPolyTime List.reverse (encList encA) (encList encA) := by
    have hfold := foldl' (encA := encA) (encL := encList encA)
      (step := fun reversed value => value :: reversed) (init := fun _ => []) id' (const [])
      (cons' (snd (encList encA) encA) (fst (encList encA) encA))
      (B := fun l => (encList encA l).length) .self (fun l i _ => by
        rw [foldlReverse]
        simp only [List.append_nil]
        have hp := (List.reverse_perm (l.take i)).flatMap_right (Turing.MultiTapeTM.frame ∘ encA)
        change (((l.take i).reverse).flatMap (Turing.MultiTapeTM.frame ∘ encA)).length ≤
          (l.flatMap (Turing.MultiTapeTM.frame ∘ encA)).length
        rw [hp.length_eq]
        exact ((List.take_sublist i l).flatMap (Turing.MultiTapeTM.frame ∘ encA)).length_le)
    simpa only [foldlReverse, List.append_nil, id_eq] using hfold
  exact hreverse.comp hlist

/-- Enumerate `0, …, n a - 1` for a computed unary bound, fixing the intermediate encoding. -/
theorem unary_range' {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a => List.range (n a)) input (encList encUnary) :=
  range.comp hn

end ComputableInPolyTime
end Turing.MultiTapeTM



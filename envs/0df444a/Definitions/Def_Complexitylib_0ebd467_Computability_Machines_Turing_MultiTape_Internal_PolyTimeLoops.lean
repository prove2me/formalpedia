-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeLoops
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeLoops
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:45:54.605771+00:00
-- url     : https://prove2.me/theorems/531d834c-928b-4d46-a60c-f7cfa0b3c93c
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops — Direct plain folds with reachable-prefix bounds
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Derived from the machine-level plain fold of the credited #869 supplier. The accumulator is
--   bounded only on reachable prefixes; no bound on arbitrary unreachable states is assumed.
--   The rules use the canonical direct core and its independent polynomial-growth algebra.
--
--   **Contents.** The module is published as a whole: 17 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeLoops`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimeLoops.lean

/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_Fold

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct plain folds with reachable-prefix bounds

Derived from the machine-level plain fold of the credited #869 supplier. The accumulator is
bounded only on reachable prefixes; no bound on arbitrary unreachable states is assumed.
The rules use the canonical direct core and its independent polynomial-growth algebra.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

private theorem unaryWordCertificate {α : Type} {input : α ↪ List Bool} {count : α → ℕ}
    (h : ComputableInPolyTime count input encUnary) :
    ComputableInPolyTime (fun x => List.replicate (count x) true) input encBits := by
  exact h.of_enc_eq fun _ => rfl

namespace ComputableInPolyTime

/-- A unary-output certificate bounds the actual numeric value by a polynomial in input size. -/
theorem polyBounded {α : Type*} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary) :
    PolyBounded (fun x => (input x).length) f := by
  simpa only [encUnary_apply, List.length_replicate] using hf.polyBounded_length

/-- A unary-output polynomial-time function is polynomially bounded in its unary input. -/
theorem polynomiallyBounded {f : ℕ → ℕ} (hf : ComputableInPolyTime f encUnary encUnary) :
    PolynomiallyBounded f :=
  (show PolyBounded (fun n : ℕ => n) f by
    simpa only [encUnary_apply, List.length_replicate] using hf.polyBounded).polynomiallyBounded

/-- A polynomial bound on the encoded accumulators of reachable prefixes suffices for a
uniform polynomial-time fold. The list and callback encodings are preserved. -/
theorem foldl' {γ α β : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    [ListEncoding encA encL] [hS : SizedListEncoding encA encL]
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {B : γ → ℕ}
    (hB : PolyBounded (fun x => (encIn x).length) B)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  obtain ⟨cL, dL, hL⟩ := hlist.polyBounded_length.exists_le
  obtain ⟨cB, dB, hB⟩ := hB.exists_le
  let A := fun n : ℕ => cL * (n + 1) ^ dL
  let D := fun n : ℕ => cB * (n + 1) ^ dB
  let P := fun n => 3 * A n + 3 * D n + 3
  have hP : PolynomiallyBounded P := by dsimp [P, A, D]; fun_prop
  apply ComputableInPolyTime.foldl (encA := encA) (encB := encB) (encL := encL)
    (list := list) (init := init) (step := step) (encBA := encPair encB encA)
    (encS := encPair encL encB) (encO := encOption (encPair encL encB))
    hlist hinit hstep hP
  · intro x
    exact (hS.length_le _).trans ((hL x).trans (by dsimp [P, A, D]; omega))
  · intro x i hi
    have hs := (hstates x i hi.le).trans (hB x)
    have ha := (hS.length_elem_le (list x) _ (List.getElem_mem hi)).trans (hL x)
    simp only [length_encPair]
    dsimp [P, A, D]
    omega
  · intro x i hi
    have hs := (hstates x i hi).trans (hB x)
    have hl := (hS.length_drop_le (list x) i).trans (hL x)
    simp only [length_encPair]
    dsimp [P, A, D]
    omega

/-- A captured parameter is computed uniformly, retained through every step, and bounded
separately from the accumulator. Only reachable prefix states need the supplied bound. -/
theorem foldlWith {γ α β π : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encL : List α ↪ List Bool} {encP : π ↪ List Bool}
    [ListEncoding encA encL] [SizedListEncoding encA encL]
    {par : γ → π} {list : γ → List α} {init : γ → β} {step : π → β → α → β}
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB)
    {B : γ → ℕ}
    (hB : PolyBounded (fun x => (encIn x).length) B)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableInPolyTime (fun x => (list x).foldl (step (par x)) (init x)) encIn encB := by
  have houter : ComputableInPolyTime (fun q : (π × β) × α => q.1)
      (encPair (encPair encP encB) encA) (encPair encP encB) :=
    ComputableInPolyTime.fst (encPair encP encB) encA
  have hfirst : ComputableInPolyTime (fun p : π × β => p.1) (encPair encP encB) encP :=
    ComputableInPolyTime.fst encP encB
  have hstart : ComputableInPolyTime (fun x => (par x, init x)) encIn (encPair encP encB) :=
    ComputableInPolyTime.pair (enc₁ := encP) (enc₂ := encB) hpar hinit
  have hjoint : ComputableInPolyTime
      (fun q : (π × β) × α => (q.1.1, step q.1.1 q.1.2 q.2))
      (encPair (encPair encP encB) encA) (encPair encP encB) :=
    ComputableInPolyTime.pair (enc₁ := encP) (enc₂ := encB)
      (ComputableInPolyTime.comp hfirst houter) hstep
  obtain ⟨cP, dP, hP⟩ := hpar.polyBounded_length.exists_le
  obtain ⟨cB, dB, hB⟩ := hB.exists_le
  let C := fun x => 2 * (encP (par x)).length + 1 + B x
  let P := fun n : ℕ => 2 * (cP * (n + 1) ^ dP) + 1 + cB * (n + 1) ^ dB
  have hp : PolynomiallyBounded P := by dsimp [P]; fun_prop
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hp
  have hC : ∀ x, C x ≤ c * ((encIn x).length + 1) ^ d := by
    intro x
    apply le_trans (b := P (encIn x).length) _ (hcd _)
    dsimp [C, P]
    have := hP x
    have := hB x
    omega
  have hfold := foldl' (encA := encA) (encB := encPair encP encB)
    (list := list) (init := fun x => (par x, init x))
    (step := fun state value => (state.1, step state.1 state.2 value))
    hlist hstart hjoint (B := C) (PolyBounded.of_forall_le c d hC) (by
      intro x i hi
      simp only [List.foldl_keep_fst, length_encPair]
      dsimp [C]
      exact Nat.add_le_add_left (hstates x i hi) _)
  have hsecond : ComputableInPolyTime (fun p : π × β => p.2) (encPair encP encB) encB :=
    ComputableInPolyTime.snd encP encB
  simpa only [Function.comp_def, List.foldl_keep_fst] using ComputableInPolyTime.comp hsecond hfold

/-- A computed captured parameter and a unary loop count give a uniform loop when every
reachable iterate has polynomially bounded encoded size. -/
theorem iterateWith {α β π : Type} {encIn : α ↪ List Bool} {encState : β ↪ List Bool}
    {encPar : π ↪ List Bool} {par : α → π} {count : α → ℕ} {init : α → β}
    {step : π → β → β}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime (fun p : π × β => step p.1 p.2)
      (encPair encPar encState) encState)
    {bound : α → ℕ}
    (hbound : PolyBounded (fun x => (encIn x).length) bound)
    (hstates : ∀ x, ∀ i ≤ count x,
      (encState ((step (par x))^[i] (init x))).length ≤ bound x) :
    ComputableInPolyTime (fun x => (step (par x))^[count x] (init x)) encIn encState := by
  have hprojection : ComputableInPolyTime (fun p : (π × β) × Bool => p.1)
      (encPair (encPair encPar encState) encBool) (encPair encPar encState) :=
    ComputableInPolyTime.fst (encPair encPar encState) encBool
  simpa only [List.foldl_const, List.length_replicate] using
    foldlWith (encA := encBool) (encL := encBits) (step := fun par state _ => step par state)
      hpar (unaryWordCertificate hcount) hinit (ComputableInPolyTime.comp hstep hprojection) hbound
      (fun x i _ => by
        simpa only [List.take_replicate, List.foldl_const, List.length_replicate] using
          hstates x (min i (count x)) (Nat.min_le_right _ _))

/-- A unary count and a bound only on the reachable states suffice for polynomial-time
iteration, with the original state encoding. -/
theorem iterate {α β : Type} {encIn : α ↪ List Bool} {encState : β ↪ List Bool}
    {count : α → ℕ} {init : α → β} {step : β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    {bound : α → ℕ}
    (hbound : PolyBounded (fun x => (encIn x).length) bound)
    (hstates : ∀ x, ∀ i ≤ count x, (encState (step^[i] (init x))).length ≤ bound x) :
    ComputableInPolyTime (fun x => step^[count x] (init x)) encIn encState := by
  have hprojection : ComputableInPolyTime (fun p : β × Bool => p.1)
      (encPair encState encBool) encState :=
    ComputableInPolyTime.fst encState encBool
  simpa only [List.foldl_const, List.length_replicate] using
    foldl' (encA := encBool) (encL := encBits) (step := fun state _ => step state)
      (unaryWordCertificate hcount) hinit (ComputableInPolyTime.comp hstep hprojection) hbound
      (fun x i _ => by
        simpa only [List.take_replicate, List.foldl_const, List.length_replicate] using
          hstates x (min i (count x)) (Nat.min_le_right _ _))

section CapturedFoldSpecifications

variable {γ α β π : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
  {encB : β ↪ List Bool} {encL : List α ↪ List Bool} {encP : π ↪ List Bool}
  [ListEncoding encA encL] [SizedListEncoding encA encL]

/-- A prefix invariant supplies both the accumulator bound and the final postcondition for a
fold with a captured parameter. The size bound may depend on the original input and need not be
computable. The step certificate is uniform jointly in the parameter, accumulator and element. -/
theorem foldlWith_spec {par : γ → π} {list : γ → List α} {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB)
    (invariant : γ → List α → β → Prop)
    (hbase : ∀ x, invariant x [] (init x))
    (hpreserve : ∀ x consumed state value, consumed ++ [value] <+: list x →
      invariant x consumed state → invariant x (consumed ++ [value]) (step (par x) state value))
    {size : γ → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x consumed state, consumed <+: list x → invariant x consumed state →
      (encB state).length ≤ size x) :
    ComputableInPolyTime (fun x => (list x).foldl (step (par x)) (init x)) encIn encB ∧
      ∀ x, invariant x (list x) ((list x).foldl (step (par x)) (init x)) := by
  have htrace (x : γ) (i : ℕ) (hi : i ≤ (list x).length) :
      invariant x ((list x).take i) (((list x).take i).foldl (step (par x)) (init x)) := by
    apply List.foldl_take_invariant (list x) (step (par x)) (init x)
      (fun i state => invariant x ((list x).take i) state) (by simpa using hbase x) ?_ i hi
    intro j hj state hstate
    simpa only [List.take_succ_eq_append_getElem hj] using
      hpreserve x ((list x).take j) state (list x)[j]
        (by simpa only [List.take_succ_eq_append_getElem hj] using
          List.take_prefix (j + 1) (list x)) hstate
  exact ⟨foldlWith hpar hlist hinit hstep hsize
    (fun x i hi => hbound x ((list x).take i) _ (List.take_prefix ..) (htrace x i hi)),
    fun x => by simpa using htrace x (list x).length le_rfl⟩

/-- A prefix invariant supplies both the accumulator bound and the final postcondition.
The size bound may depend on the original input and need not be computable. The list and step
must have uniform polynomial-time certificates. -/
theorem foldl_spec {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    (invariant : γ → List α → β → Prop)
    (hbase : ∀ x, invariant x [] (init x))
    (hpreserve : ∀ x consumed state value, consumed ++ [value] <+: list x →
      invariant x consumed state → invariant x (consumed ++ [value]) (step state value))
    {size : γ → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x consumed state, consumed <+: list x → invariant x consumed state →
      (encB state).length ≤ size x) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB ∧
      ∀ x, invariant x (list x) ((list x).foldl step (init x)) :=
  foldlWith_spec (step := fun (_ : Bool) => step) (const false) hlist hinit
    (hstep.comp ((fst (encPair encBool encB) encA).snd'.prod (snd _ _)))
    invariant hbase hpreserve hsize hbound

/-- A captured fold may add a polynomial amount of storage per element, measured against the
original input. The growth bound covers every accumulator and each element in the runtime list;
the joint step certificate still covers all parameters, accumulators and elements. -/
theorem foldlWith_of_bounded_growth {par : γ → π} {list : γ → List α} {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB)
    {growth : γ → ℕ} (hpoly : PolyBounded (fun x => (encIn x).length) growth)
    (hgrowth : ∀ x state value, value ∈ list x →
      (encB (step (par x) state value)).length ≤ (encB state).length + growth x) :
    ComputableInPolyTime (fun x => (list x).foldl (step (par x)) (init x)) encIn encB := by
  refine (foldlWith_spec hpar hlist hinit hstep
    (fun x consumed state => (encB state).length ≤
      (encB (init x)).length + consumed.length * growth x)
    (by simp) ?_
    (hinit.polyBounded_length.add (hlist.polyBounded_length.mul hpoly)) ?_).1
  · intro x consumed state value hprefix hs
    have := hgrowth x state value (hprefix.subset (by simp))
    simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    lia
  · intro x consumed state hprefix hs
    have hlen := hprefix.length_le.trans
      (SizedListEncoding.length_le (encA := encA) (encL := encL) (list x))
    exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (growth x) hlen) _)

omit [ListEncoding encA encL] [SizedListEncoding encA encL] in
/-- A fold callback may capture its original input. Growth is needed only on elements of the
runtime list, for every accumulator. Joint computation and encoding evidence lets automation
choose compatible list and callback certificates; paired growth obligations select a common
polynomial bound. The general `foldlWith_of_bounded_growth` contract takes separate premises. -/
theorem foldlWithInput_of_bounded_growth {list : γ → List α} {init : γ → β}
    {step : γ → β → α → β}
    (hinit : ComputableInPolyTime init encIn encB)
    (hcompute : ComputableInPolyTime list encIn encL ∧
      ComputableInPolyTime (fun p : (γ × β) × α => step p.1.1 p.1.2 p.2)
        (encPair (encPair encIn encB) encA) encB ∧
      ListEncoding encA encL ∧ SizedListEncoding encA encL)
    {growth : γ → ℕ} (hbound : PolyBounded (fun x => (encIn x).length) growth ∧
      ∀ x state value, value ∈ list x →
      (encB (step x state value)).length ≤ (encB state).length + growth x) :
    ComputableInPolyTime (fun x => (list x).foldl (step x) (init x)) encIn encB := by
  let := hcompute.2.2.1
  let := hcompute.2.2.2
  exact foldlWith_of_bounded_growth id' hcompute.1 hinit hcompute.2.1 hbound.1 hbound.2

/-- Constant additive growth discharges the fold's intermediate-size obligation. -/
theorem foldl_of_bounded_growth {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {growth : ℕ}
    (hgrowth : ∀ state value, (encB (step state value)).length ≤
      (encB state).length + growth) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  foldlWith_of_bounded_growth (step := fun (_ : Bool) => step) (const false) hlist hinit
    (hstep.comp ((fst (encPair encBool encB) encA).snd'.prod (snd _ _)))
    (.const growth) (fun _ state value _ => hgrowth state value)

end CapturedFoldSpecifications

section IterationSpecifications

variable {α β : Type} {encIn : α ↪ List Bool} {encState : β ↪ List Bool}

/-- Iteration may capture a computed parameter. The joint step certificate must be uniform
in that parameter; the invariant and size bound concern the original input. The bound need not
be computable and may use properties of the input beyond its encoded length. -/
theorem iterateWith_spec {π : Type} {encPar : π ↪ List Bool}
    {par : α → π} {count : α → ℕ} {init : α → β} {step : π → β → β}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime (fun p : π × β => step p.1 p.2)
      (encPair encPar encState) encState)
    (invariant : α → ℕ → β → Prop)
    (hbase : ∀ x, invariant x 0 (init x))
    (hpreserve : ∀ x i state, i < count x → invariant x i state →
      invariant x (i + 1) (step (par x) state))
    {size : α → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x i state, i ≤ count x → invariant x i state →
      (encState state).length ≤ size x) :
    ComputableInPolyTime (fun x => (step (par x))^[count x] (init x)) encIn encState ∧
      ∀ x, invariant x (count x) ((step (par x))^[count x] (init x)) := by
  have htrace (x : α) (i : ℕ) (hi : i ≤ count x) :
      invariant x i ((step (par x))^[i] (init x)) := by
    induction i with
    | zero => exact hbase x
    | succ i ih =>
      simpa only [Function.iterate_succ_apply'] using
        hpreserve x i _ (by lia) (ih (by lia))
  exact ⟨iterateWith hpar hcount hinit hstep hsize
    (fun x i hi => hbound x i _ hi (htrace x i hi)), fun x => htrace x (count x) le_rfl⟩

/-- One invariant proves both the resource bound and the final loop postcondition. -/
theorem iterate_spec {count : α → ℕ} {init : α → β} {step : β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    (invariant : α → ℕ → β → Prop)
    (hbase : ∀ x, invariant x 0 (init x))
    (hpreserve : ∀ x i state, i < count x → invariant x i state →
      invariant x (i + 1) (step state))
    {size : α → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x i state, i ≤ count x → invariant x i state →
      (encState state).length ≤ size x) :
    ComputableInPolyTime (fun x => step^[count x] (init x)) encIn encState ∧
      ∀ x, invariant x (count x) (step^[count x] (init x)) :=
  iterateWith_spec (step := fun (_ : Bool) => step) (const false) hcount hinit
    (hstep.comp (snd encBool encState)) invariant hbase hpreserve hsize hbound

/-- A captured loop may add a polynomial amount of storage per iteration, measured against the
original input. A bound depending only on the current state would not justify this rule. -/
theorem iterateWith_of_bounded_growth {π : Type} {encPar : π ↪ List Bool}
    {par : α → π} {count : α → ℕ} {init : α → β} {step : π → β → β}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime (fun p : π × β => step p.1 p.2)
      (encPair encPar encState) encState)
    {growth : α → ℕ} (hpoly : PolyBounded (fun x => (encIn x).length) growth)
    (hgrowth : ∀ x state, (encState (step (par x) state)).length ≤
      (encState state).length + growth x) :
    ComputableInPolyTime (fun x => (step (par x))^[count x] (init x)) encIn encState := by
  refine (iterateWith_spec hpar hcount hinit hstep
    (fun x i state => (encState state).length ≤ (encState (init x)).length + i * growth x)
    (by simp) ?_ (hinit.polyBounded_length.add (hcount.polyBounded.mul hpoly)) ?_).1
  · intro x i state _ hstate
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
      (hgrowth x state).trans (Nat.add_le_add_right hstate _)
  · intro x i state hi hstate
    exact hstate.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _)

/-- An iteration step may capture its original input. Paired growth obligations let automation
select a common polynomial bound. The uniform joint step certificate charges the captured input
on every iteration; the growth bound need not itself be computable. -/
theorem iterateWithInput_of_bounded_growth {count : α → ℕ} {init : α → β} {step : α → β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime (fun p : α × β => step p.1 p.2)
      (encPair encIn encState) encState)
    {growth : α → ℕ} (hbound : PolyBounded (fun x => (encIn x).length) growth ∧
      ∀ x state, (encState (step x state)).length ≤ (encState state).length + growth x) :
    ComputableInPolyTime (fun x => (step x)^[count x] (init x)) encIn encState :=
  iterateWith_of_bounded_growth id' hcount hinit hstep hbound.1 hbound.2

/-- A loop with constant additive state growth has polynomially bounded intermediate states. -/
theorem iterate_of_bounded_growth {count : α → ℕ} {init : α → β} {step : β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    {growth : ℕ} (hgrowth : ∀ state, (encState (step state)).length ≤
      (encState state).length + growth) :
    ComputableInPolyTime (fun x => step^[count x] (init x)) encIn encState := by
  exact iterateWith_of_bounded_growth (step := fun (_ : Bool) => step)
    (const false) hcount hinit (hstep.comp (snd encBool encState)) (.const growth)
    (fun _ state => hgrowth state)

end IterationSpecifications

end ComputableInPolyTime
end Turing.MultiTapeTM



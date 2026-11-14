-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:28.331658+00:00
-- url     : https://prove2.me/theorems/12aedf71-e9b7-41c3-b668-792d36f24125
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives — Direct plain polynomial-time primitives
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The canonical rules normalize plain realizing machines inside the internal proof, combine them
--   with machine-level combinators, and conclude plain computability. No tidy asymptotic predicate
--   or bridge participates in their statements or derivations.
--
--   ### Main results
--
--   * `ComputableInPolyTime.comp`, `.trans`, `.pair`, `.ite`, `.foldl`: direct closure rules.
--   * `ComputableInPolyTime.fst`, `.snd`: ordinary encoded-pair projections.
--   * `ComputableInPolyTime.frame`, `.unframe`, `.dropFrame`: total word framing and parsers.
--
--   **Contents.** The module is published as a whole: 27 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimePrimitives.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_NormalForm
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FoldCompiler
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Polynomial

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct plain polynomial-time primitives

The canonical rules normalize plain realizing machines inside the internal proof, combine them
with machine-level combinators, and conclude plain computability. No tidy asymptotic predicate
or bridge participates in their statements or derivations.

## Main results

* `ComputableInPolyTime.comp`, `.trans`, `.pair`, `.ite`, `.foldl`: direct closure rules.
* `ComputableInPolyTime.fst`, `.snd`: ordinary encoded-pair projections.
* `ComputableInPolyTime.frame`, `.unframe`, `.dropFrame`: total word framing and parsers.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib

universe u
variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- A tidy machine within resources bounded by a polynomially bounded function of the length of
the encoded input certifies plain polynomial time. -/
private theorem of_computesTidily {f : α → β} {k : ℕ} {State : Type} [Finite State]
    {tm : MultiTapeTM k Bool State} {t s : α → ℕ} {T : ℕ → ℕ} (hT : PolynomiallyBounded T)
    (h : ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a)) (t a) (s a))
    (ht : ∀ a, t a ≤ T (encIn a).length) (hs : ∀ a, s a ≤ T (encIn a).length) :
    ComputableInPolyTime f encIn encMid :=
  ⟨T, T, hT, hT, k, State, inferInstance, tm,
    fun a => ((h a).mono (ht a) (hs a)).computesInTimeAndSpace⟩

/-- Package a plain machine whose resources share a polynomial bound. -/
private theorem of_computesPlain {f : α → β} {k : ℕ} {State : Type} [Finite State]
    {tm : MultiTapeTM k Bool State} {t s : α → ℕ} {T : ℕ → ℕ} (hT : PolynomiallyBounded T)
    (h : ∀ a, tm.ComputesInTimeAndSpace (encIn a) (encMid (f a)) (t a) (s a))
    (ht : ∀ a, t a ≤ T (encIn a).length) (hs : ∀ a, s a ≤ T (encIn a).length) :
    ComputableInPolyTime f encIn encMid :=
  ⟨T, T, hT, hT, k, State, inferInstance, tm,
    fun a => ⟨(h a).1, (h a).2.1.mono (ht a), (h a).2.2.mono (hs a)⟩⟩

/-- Frame a raw word with the existing streaming encoder. -/
@[fun_prop]
theorem frame : ComputableInPolyTime Turing.MultiTapeTM.frame encBits encBits :=
  (ComputableInDegree.of_frame (fun _ => rfl)).computableInPolyTime

/-- Read the first framed word, including incomplete or malformed inputs. -/
@[fun_prop]
theorem unframe : ComputableInPolyTime Turing.MultiTapeTM.unframe encBits encBits :=
  (ComputableInDegree.of_unframe (fun _ => rfl)).computableInPolyTime

/-- Drop the first framed word, including incomplete or malformed inputs. -/
@[fun_prop]
theorem dropFrame : ComputableInPolyTime Turing.MultiTapeTM.dropFrame encBits encBits :=
  (ComputableInDegree.of_dropFrame (fun _ => rfl)).computableInPolyTime

/-- **Composition**, through the machine-level composition of tidy machines. The intermediate word
is no longer than the time of the inner machine. -/
theorem comp {f : β → γ} {g : α → β} (hf : ComputableInPolyTime f encMid encOut)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (f ∘ g) encIn encOut := by
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := Internal.NormalForm.polyTime hg
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := Internal.NormalForm.polyTime hf
  refine of_computesTidily (tm := tm₂.comp tm₁ true)
    (T := fun n => 6 * (c₁ * (n + 1) ^ d₁) + c₂ * (c₁ * (n + 1) ^ d₁ + 1) ^ d₂ +
      (6 * max k₁ k₂ + 20)) (by fun_prop) (fun a => (h₁ a).comp (h₂ (g a)) true)
    (fun a => ?_) (fun a => ?_) <;>
  · have hl := (h₁ a).length_output_le
    have := Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) d₂)
    omega

/-- Compose in execution order. This lets `fun_prop` infer the intermediate encoding from the
inner function when it cannot be inferred from the outer function. -/
@[fun_prop]
theorem trans {f : α → β} {g : β → γ} (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encMid encOut) :
    ComputableInPolyTime (fun x => g (f x)) encIn encOut :=
  hg.comp hf

-- Infer an intermediate encoding from the inner computation first. The outer-first
-- composition rule remains available when the outer computation determines it instead.
@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} (hf : ComputableInPolyTime f encMid encOut)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun a => f (g a)) encIn encOut :=
  hf.comp hg

/-- **Pairing**, for any encoding of pairs, through its pairing combinator. -/
@[fun_prop]
theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {enc : β₁ × β₂ ↪ List Bool} [PairEncoding enc₁ enc₂ enc]
    {f : α → β₁} {g : α → β₂} (hf : ComputableInPolyTime f encIn enc₁)
    (hg : ComputableInPolyTime g encIn enc₂) :
    ComputableInPolyTime (fun x => (f x, g x)) encIn enc := by
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := Internal.NormalForm.polyTime hf
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := Internal.NormalForm.polyTime hg
  obtain ⟨c, k, S, _, tm, h⟩ := PairEncoding.pair_mono (enc := enc)
    (t₁ := fun a => c₁ * ((encIn a).length + 1) ^ d₁)
    (s₁ := fun a => c₁ * ((encIn a).length + 1) ^ d₁)
    (t₂ := fun a => c₂ * ((encIn a).length + 1) ^ d₂)
    (s₂ := fun a => c₂ * ((encIn a).length + 1) ^ d₂)
    ⟨k₁, S₁, inferInstance, tm₁, fun a => (h₁ a).computesInTimeAndSpace⟩
    ⟨k₂, S₂, inferInstance, tm₂, fun a => (h₂ a).computesInTimeAndSpace⟩
  -- the encoded pair, kept in the space bound, is no longer than the time bound
  refine of_computesPlain (T := fun n =>
      c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ + 1) +
      c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ +
        c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ + 1) + 1))
    (by fun_prop) h (fun a => ?_) (fun a => ?_)
  · exact Nat.le_add_right _ _
  · have hl := (h a).length_output_le
    beta_reduce at hl
    exact (Nat.mul_le_mul_left c (by omega)).trans (Nat.le_add_left _ _)

/-- **Case distinction** on a Boolean test computable in polynomial time, in any encoding of
`Bool`. -/
@[fun_prop]
theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c encIn encC) (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun x => if c x then f x else g x) encIn encMid := by
  obtain ⟨c₀, d₀, k₀, S₀, _, tm₀, h₀⟩ := Internal.NormalForm.polyTime hc
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := Internal.NormalForm.polyTime hf
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := Internal.NormalForm.polyTime hg
  obtain ⟨k, K, S, _, tm, h⟩ := Internal.conditional (encOut := encMid)
    (f := f) (g := g)
    (tc := fun a => c₀ * ((encIn a).length + 1) ^ d₀)
    (sc := fun a => c₀ * ((encIn a).length + 1) ^ d₀)
    (tf := fun a => c₁ * ((encIn a).length + 1) ^ d₁)
    (sf := fun a => c₁ * ((encIn a).length + 1) ^ d₁)
    (tg := fun a => c₂ * ((encIn a).length + 1) ^ d₂)
    (sg := fun a => c₂ * ((encIn a).length + 1) ^ d₂)
    h₀ (fun x => h₁ x.1) (fun x => h₂ x.1)
  refine of_computesTidily (T := fun n =>
      c₀ * (n + 1) ^ d₀ + (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂) + k)
    (by fun_prop) h (fun a => ?_) (fun a => ?_) <;>
  · split_ifs <;> omega

/-- **Left folds**, through the machine-level loop. Besides certificates for the list, the initial
value and the step, a polynomially bounded `L` must bound the length of the list, the encoded
arguments of every step and the encoded intermediate states. -/
theorem foldl {γ α β : Type u} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
    {encO : Option (List α × β) ↪ List Bool}
    [ListEncoding encA encL] [PairEncoding encB encA encBA] [PairEncoding encL encB encS]
    [OptionEncoding encS encO] {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL) (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : β × α => step p.1 p.2) encBA encB)
    {L : ℕ → ℕ} (hL : PolynomiallyBounded L)
    (hlen : ∀ x, (list x).length ≤ L (encIn x).length)
    (harg : ∀ x i (hi : i < (list x).length),
      (encBA (((list x).take i).foldl step (init x), (list x)[i])).length ≤ L (encIn x).length)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encS ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤
        L (encIn x).length) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := Internal.NormalForm.polyTime hlist
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := Internal.NormalForm.polyTime hinit
  obtain ⟨c₃, d₃, k₃, S₃, _, tm₃, h₃⟩ := Internal.NormalForm.polyTime hstep
  -- the step on the arguments that occur, within the bound at the largest argument
  have hmax (x : γ) (i : ℕ) (hi : i < (list x).length) :
      c₃ * ((encBA (((list x).take i).foldl step (init x), (list x)[i])).length + 1) ^ d₃ ≤
        c₃ * (L (encIn x).length + 1) ^ d₃ :=
    Nat.mul_le_mul_left c₃ (Nat.pow_le_pow_left (Nat.add_le_add_right (harg x i hi) 1) d₃)
  obtain ⟨c, k, S, _, tm, h⟩ := Internal.FoldCompiler.foldl (encA := encA)
    (encL := encL) (encBA := encBA) (encS := encS) (encO := encO) (step := step)
    (t := fun x => c₁ * ((encIn x).length + 1) ^ d₁ + c₂ * ((encIn x).length + 1) ^ d₂)
    (s := fun x => c₁ * ((encIn x).length + 1) ^ d₁ + c₂ * ((encIn x).length + 1) ^ d₂)
    (tStep := fun p => c₃ * ((encBA p).length + 1) ^ d₃)
    (sStep := fun p => c₃ * ((encBA p).length + 1) ^ d₃)
    (tMax := fun x => c₃ * (L (encIn x).length + 1) ^ d₃)
    (sMax := fun x => c₃ * (L (encIn x).length + 1) ^ d₃)
    (lMax := fun x => L (encIn x).length)
    (fun x => (h₁ x).mono (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    (fun x => (h₂ x).mono (Nat.le_add_left _ _) (Nat.le_add_left _ _))
    h₃ hmax hmax hstate
  refine of_computesTidily (T := fun n =>
      c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ +
        (L n + 1) * (c₃ * (L n + 1) ^ d₃ + L n + 1)) +
      c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ + c₃ * (L n + 1) ^ d₃ + L n + 1))
    (by fun_prop) h (fun x => ?_) (fun x => ?_)
  · have := Nat.mul_le_mul_right (c₃ * (L (encIn x).length + 1) ^ d₃ + L (encIn x).length + 1)
      (Nat.add_le_add_right (hlen x) 1)
    exact (Nat.mul_le_mul_left c (by omega)).trans (Nat.le_add_right _ _)
  · exact Nat.le_add_left _ _

/-- The first projection of an encoding of pairs, from its linear-time machine. -/
theorem _root_.Turing.MultiTapeTM.PairEncoding.computableInPolyTime_fst
    {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc] :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.1) enc enc₁ :=
  h.fst.computableInPolyTime

/-- The second projection of an encoding of pairs, from its linear-time machine. -/
theorem _root_.Turing.MultiTapeTM.PairEncoding.computableInPolyTime_snd
    {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc] :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.2) enc enc₂ :=
  h.snd.computableInPolyTime

/-- Project the first entry of an ordinary framed pair. -/
@[fun_prop]
theorem fst {α β : Type u} (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) :
    ComputableInPolyTime (fun p : α × β => p.1) (encPair enc₁ enc₂) enc₁ :=
  PairEncoding.computableInPolyTime_fst (enc₁ := enc₁) (enc₂ := enc₂) (enc := encPair enc₁ enc₂)

/-- Project the second entry of an ordinary framed pair. -/
@[fun_prop]
theorem snd {α β : Type u} (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) :
    ComputableInPolyTime (fun p : α × β => p.2) (encPair enc₁ enc₂) enc₂ :=
  PairEncoding.computableInPolyTime_snd (enc₁ := enc₁) (enc₂ := enc₂) (enc := encPair enc₁ enc₂)

/-- Reuse the same realizing machine for an equal encoded output. -/
theorem of_enc_eq {δ : Type*} {encD : δ ↪ List Bool} {f : α → β} {g : α → δ}
    (hf : ComputableInPolyTime f encIn encMid)
    (h : ∀ a, encD (g a) = encMid (f a)) : ComputableInPolyTime g encIn encD :=
  let ⟨t, s, ht, hs, k, State, hfinite, tm, htm⟩ := hf
  ⟨t, s, ht, hs, k, State, hfinite, tm, fun a => h a ▸ htm a⟩

/-- The complete encoded output is bounded by the actual time of its realizing machine. -/
theorem polyBounded_length {f : α → β} (hf : ComputableInPolyTime f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) (fun a => (encMid (f a)).length) := by
  obtain ⟨c, d, _, _, _, _, h⟩ := Internal.NormalForm.polyTime hf
  exact PolyBounded.of_forall_le c d fun a => (h a).length_output_le

/-- Pair two computed outputs using the standard pair encoding. -/
@[fun_prop]
theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {f : α → β₁} {g : α → β₂}
    (hf : ComputableInPolyTime f encIn enc₁) (hg : ComputableInPolyTime g encIn enc₂) :
    ComputableInPolyTime (fun a => (f a, g a)) encIn (encPair enc₁ enc₂) := pair hf hg

/-- Project the first entry after computing a pair; the input universe is independent. -/
theorem fst' {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (hf : ComputableInPolyTime f encIn (encPair enc₁ enc₂)) :
    ComputableInPolyTime (fun a => (f a).1) encIn enc₁ := (fst enc₁ enc₂).comp hf

/-- Project the second entry after computing a pair; the input universe is independent. -/
theorem snd' {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (hf : ComputableInPolyTime f encIn (encPair enc₁ enc₂)) :
    ComputableInPolyTime (fun a => (f a).2) encIn enc₂ := (snd enc₁ enc₂).comp hf

/-- Boolean conjunction on its fixed finite input domain. -/
@[fun_prop]
theorem bool_and : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Conjunction of two computed Booleans. -/
theorem bool_and' {γ : Type} {input : γ ↪ List Bool} {left right : γ → Bool}
    (hleft : ComputableInPolyTime left input encBool)
    (hright : ComputableInPolyTime right input encBool) :
    ComputableInPolyTime (fun a => left a && right a) input encBool :=
  bool_and.comp (hleft.prod hright)

/-- Boolean negation on its fixed finite input domain. -/
@[fun_prop]
theorem bool_not : ComputableInPolyTime Bool.not encBool encBool := of_finite _

/-- Boolean disjunction is polynomial-time in the standard Boolean encoding. -/
@[fun_prop]
theorem bool_or :
    ComputableInPolyTime (fun (p : Bool × Bool) => p.1 || p.2)
  (encPair encBool encBool)
  encBool := of_finite _

/-- Boolean exclusive disjunction on its fixed finite input domain. -/
@[fun_prop]
theorem bool_xor : ComputableInPolyTime (fun p : Bool × Bool => p.1 ^^ p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Conjunction preserves the full input encoding of both decision procedures. -/
@[fun_prop]
theorem decide_and {α : Type} {encA : α ↪ List Bool}
    {left right : α → Prop} [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hleft : ComputableInPolyTime (fun a => decide (left a)) encA encBool)
    (hright : ComputableInPolyTime (fun a => decide (right a)) encA encBool) :
    ComputableInPolyTime (fun a => decide (left a ∧ right a)) encA encBool := by
  simpa only [Bool.decide_and, Function.comp_def] using bool_and.comp (hleft.prod hright)

/-- A proposition-valued conditional computes its decision in the standard Boolean encoding. -/
@[fun_prop]
theorem ite_decide {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {condition : α → Prop} [∀ a, Decidable (condition a)] {yes no : α → β}
    (hcondition : ComputableInPolyTime (fun a => decide (condition a)) encA encBool)
    (hyes : ComputableInPolyTime yes encA encB)
    (hno : ComputableInPolyTime no encA encB) :
    ComputableInPolyTime (fun a => if condition a then yes a else no a) encA encB := by
  simpa only [decide_eq_true_eq] using ite hcondition hyes hno

end Turing.MultiTapeTM.ComputableInPolyTime



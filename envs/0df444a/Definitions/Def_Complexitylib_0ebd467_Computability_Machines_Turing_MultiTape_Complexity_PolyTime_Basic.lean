-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Basic
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:51:37.663639+00:00
-- url     : https://prove2.me/theorems/9dff711b-7575-4468-8799-9240a2acc31f
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic — Basic polynomial-time rules
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Polynomial-time counterparts of Christian Reitwiessner's degree-bounded operations, and Boolean
--   rules for `fun_prop`.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.PolyBounded.exists_polynomial`: express a resource bound by a polynomial.
--
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.exists_degree`: polynomial-time functions
--     admit explicit time and output degrees.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.polyBounded`: a computed unary value bounds
--     resources polynomially in the original input encoding.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_enc_eq`: reuse identical encoded outputs.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.encoded`, `.unframe`, `.dropFrame`: compose
--     encoded values and total frame parsing without requiring an inverse for an encoding.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_finite`: functions on finite domains.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.fstWithEncoding`, `.sndWithEncoding`: projections
--     that compose with a known encoding conversion.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_eq`, `.beq`: equality for fixed encodings.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bool_and'`, `.decide_and`, `.cond`, `.ite_decide`:
--     compound guards and conditionals with fixed intermediate Boolean encodings.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.decide_or`, `.bne`: disjunction and Boolean inequality
--     for plain certificates.
--
--   **Contents.** The module is published as a whole: 30 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Basic`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Basic.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Primitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_EqualityPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Basic polynomial-time rules

Polynomial-time counterparts of Christian Reitwiessner's degree-bounded operations, and Boolean
rules for `fun_prop`.

## Main results

* `Turing.MultiTapeTM.PolyBounded.exists_polynomial`: express a resource bound by a polynomial.

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.exists_degree`: polynomial-time functions
  admit explicit time and output degrees.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.polyBounded`: a computed unary value bounds
  resources polynomially in the original input encoding.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_enc_eq`: reuse identical encoded outputs.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.encoded`, `.unframe`, `.dropFrame`: compose
  encoded values and total frame parsing without requiring an inverse for an encoding.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_finite`: functions on finite domains.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.fstWithEncoding`, `.sndWithEncoding`: projections
  that compose with a known encoding conversion.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_eq`, `.beq`: equality for fixed encodings.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bool_and'`, `.decide_and`, `.cond`, `.ite_decide`:
  compound guards and conditionals with fixed intermediate Boolean encodings.
* `Turing.MultiTapeTM.ComputableInPolyTime.decide_or`, `.bne`: disjunction and Boolean inequality
  for plain certificates.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- A polynomially bounded resource admits a polynomial upper bound at every input size. -/
theorem PolyBounded.exists_polynomial {α : Type*} {size u : α → ℕ}
    (h : PolyBounded size u) : ∃ p : Polynomial ℕ, ∀ a, u a ≤ p.eval (size a) := by
  obtain ⟨c, d, hle⟩ := h.exists_le
  exact ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun a => by simpa using hle a⟩

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- An efficiently computed unary value is polynomially bounded in the original encoded input.
This supplies input-dependent resource bounds without exposing their polynomial coefficients. -/
theorem polyBounded {f : α → ℕ} (hf : ComputableTidilyInPolyTime f encA encUnary) :
    PolyBounded (fun x => (encA x).length) f := by
  simpa only [encUnary_apply, List.length_replicate] using hf.polyBounded_length

/-- Compose in execution order. This also lets `fun_prop` infer the intermediate encoding from
the inner function when it cannot be inferred from the outer function. -/
@[fun_prop]
theorem trans {δ : Type} {encD : δ ↪ List Bool} {f : α → β} {g : β → δ}
    (hf : ComputableTidilyInPolyTime f encA encB)
    (hg : ComputableTidilyInPolyTime g encB encD) :
    ComputableTidilyInPolyTime (fun x => g (f x)) encA encD := hg.comp hf

/-- Project the first component of a polynomial-time pair-valued function. -/
@[fun_prop]
theorem fst' {δ : Type} {encD : δ ↪ List Bool} {f : α → β × δ}
    (hf : ComputableTidilyInPolyTime f encA (encPair encB encD)) :
    ComputableTidilyInPolyTime (fun x => (f x).1) encA encB :=
  (fst encB encD).comp hf

/-- Project the second component of a polynomial-time pair-valued function. -/
@[fun_prop]
theorem snd' {δ : Type} {encD : δ ↪ List Bool} {f : α → β × δ}
    (hf : ComputableTidilyInPolyTime f encA (encPair encB encD)) :
    ComputableTidilyInPolyTime (fun x => (f x).2) encA encD :=
  (snd encB encD).comp hf

/-- Project a first component and convert its encoding. Certifying the pair-valued function first
determines the source encoding before automation searches for the conversion certificate. -/
@[fun_prop]
theorem fstWithEncoding {γ : Type} {encC : γ ↪ List Bool}
    {output : α ↪ List Bool} {f : γ → α × β}
    (hf : ComputableTidilyInPolyTime f encC (encPair encA encB))
    (h : ComputableTidilyInPolyTime (fun a => a) encA output) :
    ComputableTidilyInPolyTime (fun p => (f p).1) encC output :=
  h.comp hf.fst'

/-- Project a second component and convert its encoding. The pair certificate fixes the source
encoding; the conversion certificate supplies the efficient change of representation. -/
@[fun_prop]
theorem sndWithEncoding {γ : Type} {encC : γ ↪ List Bool}
    {output : β ↪ List Bool} {f : γ → α × β}
    (hf : ComputableTidilyInPolyTime f encC (encPair encA encB))
    (h : ComputableTidilyInPolyTime (fun a => a) encB output) :
    ComputableTidilyInPolyTime (fun p => (f p).2) encC output :=
  h.comp hf.snd'

/-- Every polynomial-time function admits explicit time and output degrees. -/
theorem exists_degree {f : α → β} (hf : ComputableTidilyInPolyTime f encA encB) :
    ∃ d e, ComputableTidilyInDegree f encA encB d e := by
  obtain ⟨t, s, ht, hs, hf⟩ := hf
  obtain ⟨ct, dt, ht⟩ := ht.exists_le
  obtain ⟨cs, ds, hs⟩ := hs.exists_le
  exact ⟨max dt ds, max dt ds, .of_bounds
    (DegreeBounded.mono_deg ⟨ct, ht⟩ (le_max_left dt ds))
    (DegreeBounded.mono_deg ⟨cs, hs⟩ (le_max_right dt ds)) hf⟩

/-- Reuse a computation when the new function emits the same encoded output word. -/
theorem of_enc_eq {δ : Type} {encD : δ ↪ List Bool} {f : α → β} {g : α → δ}
    (hf : ComputableTidilyInPolyTime f encA encB)
    (h : ∀ a, encD (g a) = encB (f a)) : ComputableTidilyInPolyTime g encA encD :=
  let ⟨t, s, ht, hs, hf⟩ := hf
  ⟨t, s, ht, hs, hf.of_enc_eq h⟩

/-- Expose an already encoded value as a raw word. No inverse for the encoding is required. -/
@[fun_prop]
theorem encode (enc : α ↪ List Bool) : ComputableTidilyInPolyTime enc enc encBits :=
  of_eq fun _ => rfl

/-- Compute a value and expose its representation, inferring that representation from the
supplied certificate before composing. -/
@[fun_prop]
theorem encoded {f : α → β} (hf : ComputableTidilyInPolyTime f encA encB) :
    ComputableTidilyInPolyTime (fun a => encB (f a)) encA encBits :=
  hf.of_enc_eq fun _ => rfl

/-- Read the first frame from any raw word, including malformed encodings. -/
@[fun_prop]
theorem unframe : ComputableTidilyInPolyTime Turing.MultiTapeTM.unframe encBits encBits :=
  of_linear (.of_unframe fun _ => rfl)

/-- Drop the first frame from any raw word, including malformed encodings. -/
@[fun_prop]
theorem dropFrame : ComputableTidilyInPolyTime Turing.MultiTapeTM.dropFrame encBits encBits :=
  of_linear (.of_dropFrame fun _ => rfl)

/-- Every function on a finite domain is polynomial-time for any fixed encodings. -/
theorem of_finite [Finite α] (f : α → β) : ComputableTidilyInPolyTime f encA encB :=
  (ComputableTidilyInDegree.of_finite f).computableTidilyInPolyTime

@[fun_prop]
theorem bool_not : ComputableTidilyInPolyTime Bool.not encBool encBool := of_finite _

@[fun_prop]
theorem bool_and : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 && p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Conjoin computed guards, fixing both intermediate Boolean encodings. -/
@[fun_prop]
theorem bool_and' {left right : α → Bool}
    (hleft : ComputableTidilyInPolyTime left encA encBool)
    (hright : ComputableTidilyInPolyTime right encA encBool) :
    ComputableTidilyInPolyTime (fun a => left a && right a) encA encBool :=
  bool_and.comp (hleft.prod hright)

@[fun_prop]
theorem bool_or : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 || p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Exclusive-or is a finite Boolean computation. -/
@[fun_prop]
theorem bool_xor : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 ^^ p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Conjunction of efficiently decidable propositions uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_and {left right : α → Prop} [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hleft : ComputableTidilyInPolyTime (fun a => decide (left a)) encA encBool)
    (hright : ComputableTidilyInPolyTime (fun a => decide (right a)) encA encBool) :
    ComputableTidilyInPolyTime (fun a => decide (left a ∧ right a)) encA encBool := by
  simpa only [Bool.decide_and, Function.comp_def] using bool_and.comp (hleft.prod hright)

/-- Disjunction of efficiently decidable propositions uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_or {left right : α → Prop} [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hleft : ComputableTidilyInPolyTime (fun a => decide (left a)) encA encBool)
    (hright : ComputableTidilyInPolyTime (fun a => decide (right a)) encA encBool) :
    ComputableTidilyInPolyTime (fun a => decide (left a ∨ right a)) encA encBool := by
  simpa only [Bool.decide_or, Function.comp_def] using bool_or.comp (hleft.prod hright)

/-- A Boolean conditional fixes the guard encoding before automation synthesizes its proof. -/
@[fun_prop]
theorem cond {condition : α → Bool} {yes no : α → β}
    (hcondition : ComputableTidilyInPolyTime condition encA encBool)
    (hyes : ComputableTidilyInPolyTime yes encA encB)
    (hno : ComputableTidilyInPolyTime no encA encB) :
    ComputableTidilyInPolyTime (fun a => if condition a then yes a else no a) encA encB :=
  hcondition.ite' hyes hno

/-- A proposition-valued conditional computes its decision in the standard Boolean encoding. -/
@[fun_prop]
theorem ite_decide {condition : α → Prop} [∀ a, Decidable (condition a)] {yes no : α → β}
    (hcondition : ComputableTidilyInPolyTime (fun a => decide (condition a)) encA encBool)
    (hyes : ComputableTidilyInPolyTime yes encA encB)
    (hno : ComputableTidilyInPolyTime no encA encB) :
    ComputableTidilyInPolyTime (fun a => if condition a then yes a else no a) encA encB := by
  simpa only [decide_eq_true_eq] using hcondition.cond hyes hno

/-- Comparing two Boolean values is a finite-domain computation. -/
@[fun_prop]
theorem bool_beq : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 == p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Equality is polynomial-time for any encoding. -/
@[fun_prop]
theorem decide_eq [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : α × α => decide (p.1 = p.2))
      (encPair enc enc) encBool :=
  (ComputableTidilyInDegree.eq enc).computableTidilyInPolyTime

/-- Compare computed values for equality, inferring their common encoding from the arguments. -/
@[fun_prop]
theorem decide_eq' [DecidableEq β] {left right : α → β}
    (hleft : ComputableTidilyInPolyTime left encA encB)
    (hright : ComputableTidilyInPolyTime right encA encB) :
    ComputableTidilyInPolyTime (fun x => decide (left x = right x)) encA encBool :=
  (decide_eq encB).comp (hleft.prod hright)

/-- Lawful Boolean equality compares computed values through their common encoding. -/
@[fun_prop]
theorem beq [BEq β] [LawfulBEq β] {left right : α → β}
    (hleft : ComputableTidilyInPolyTime left encA encB)
    (hright : ComputableTidilyInPolyTime right encA encB) :
    ComputableTidilyInPolyTime (fun x => left x == right x) encA encBool := by
  classical
  simpa only [beq_eq_decide] using hleft.decide_eq' hright

/-- Compare two computed values using their common encoding. -/
@[fun_prop]
theorem decide_ne [DecidableEq β] {left right : α → β}
    (hleft : ComputableTidilyInPolyTime left encA encB)
    (hright : ComputableTidilyInPolyTime right encA encB) :
    ComputableTidilyInPolyTime (fun x => decide (left x ≠ right x)) encA encBool := by
  simpa only [Function.comp_def, decide_not] using
    bool_not.comp (hleft.decide_eq' hright)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_or` for plain certificates. -/
@[fun_prop]
theorem decide_or {left right : α → Prop} [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hleft : ComputableInPolyTime (fun a => decide (left a)) encA encBool)
    (hright : ComputableInPolyTime (fun a => decide (right a)) encA encBool) :
    ComputableInPolyTime (fun a => decide (left a ∨ right a)) encA encBool := by
  simpa only [Bool.decide_or, Function.comp_def] using bool_or.comp (hleft.prod hright)

/-- Lawful Boolean inequality compares computed values through their common encoding. -/
@[fun_prop]
theorem bne [BEq β] [LawfulBEq β] {left right : α → β}
    (hleft : ComputableInPolyTime left encA encB)
    (hright : ComputableInPolyTime right encA encB) :
    ComputableInPolyTime (fun x => left x != right x) encA encBool := by
  simpa only [_root_.bne, Function.comp_def] using bool_not.comp (hleft.beq hright)

end Turing.MultiTapeTM.ComputableInPolyTime



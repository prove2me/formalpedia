-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_EqualityPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_EqualityPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:46:40.548014+00:00
-- url     : https://prove2.me/theorems/0d06400f-2f98-4a6d-aa48-23aed1952f7c
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives — Direct word equality at the original resource bounds
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Plain word leaves feed a reachable-prefix fold. Both encoded inputs are charged, with the
--   original product time bound and linear workspace bound; no higher tidy calculus is imported.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_EqualityPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/EqualityPrimitives.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeComposition
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeClosure
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreePrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OLoops
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_WordEquality
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Bounds
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Direct word equality at the original resource bounds

Plain word leaves feed a reachable-prefix fold. Both encoded inputs are charged, with the
original product time bound and linear workspace bound; no higher tidy calculus is imported.
-/

@[expose] public section
namespace Turing.MultiTapeTM
namespace ComputableInDegree

/-- A step of comparing words. -/
public theorem eqWordsStep : ComputableInDegree (fun q : (List Bool × Bool) × Bool =>
    EqWords.step q.1 q.2) (encPair (encPair encBits encBool) encBool) (encPair encBits encBool)
    1 1 := by
  -- the rest of the second word, and the facts it is compared by
  have hq := fst (encPair encBits encBool) encBool
  have hrest := (fst encBits encBool).comp hq
  have hlast := (Internal.DecoderWords.bool_degree.comp hrest).pair
    (snd (encPair encBits encBool) encBool) (enc := encPair encBool encBool)
  have hempty := Internal.DecoderWords.empty_degree.comp hrest
  have hfacts := ((snd encBits encBool).comp hq).prod (hempty.prod hlast)
  exact ((Internal.DecoderWords.tail_degree.comp hrest).prod
    ((of_finite (encIn := encPair encBool (encPair encBool (encPair encBool encBool)))
      (encMid := encBool) fun t : Bool × Bool × Bool × Bool =>
        t.1 && !t.2.1 && (t.2.2.1 == t.2.2.2)).comp hfacts)).mono

/-- The result of comparing words, from the state after the last step. -/
public theorem eqWordsResult :
    ComputableInDegree (fun s : List Bool × Bool => s.2 && s.1.isEmpty)
      (encPair encBits encBool) encBool 1 0 :=
  ((of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun t : Bool × Bool => t.1 && t.2).comp ((snd encBits encBool).prod
      (Internal.DecoderWords.empty_degree.comp (fst encBits encBool)))).mono

end ComputableInDegree

namespace ComputableInO

/-- Equality of words, within the length of the first word times the length of both, and linear
space. -/
public theorem eqWords :
    ComputableInO (fun p : List Bool × List Bool => decide (p.1 = p.2))
      (encPair encBits encBits) encBool
      (fun p => (p.1.length + 1) * (p.1.length + p.2.length + 1))
      fun p => p.1.length + p.2.length + 1 := by
  have hfold := foldl (encA := encBool) (encL := encBits) (encB := encPair encBits encBool)
    (fst encBits encBits) ((snd encBits encBits).prod (const true))
    (ComputableInDegree.inO_one ComputableInDegree.eqWordsStep)
    (R := fun p => 4 * (encPair encBits encBits p).length + 8)
    (Q := fun p => 4 * (encPair encBits encBits p).length + 8)
    (B := fun p => 4 * (encPair encBits encBits p).length + 8)
    (fun p i hi => by
      have := EqWords.foldl_fst (p.1.take i) p.2 true
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton]
      rw [this, List.length_drop]
      omega)
    (fun p i hi => by
      have := EqWords.foldl_fst (p.1.take i) p.2 true
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton]
      rw [this, List.length_drop]
      omega)
    (fun p i hi => by
      have := EqWords.foldl_fst (p.1.take i) p.2 true
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton]
      rw [this, List.length_drop]
      omega)
  refine (((ComputableInDegree.inO_one ComputableInDegree.eqWordsResult).comp_linear
    hfold).mono 64 (fun p => ?_) fun p => ?_).of_enc_eq fun p => ?_
  · simp only [length_encPair, encBits_apply]
    nlinarith
  · simp only [length_encPair, encBits_apply]
    omega
  · simpa using congrArg encBool (EqWords.foldl_result p.1 p.2 true).symm

/-- Equality, for any encoding. -/
public theorem eq {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInO (fun p : α × α => decide (p.1 = p.2)) (encPair enc enc) encBool
      (fun p => ((enc p.1).length + 1) * ((enc p.1).length + (enc p.2).length + 1))
      fun p => (encPair enc enc p).length := by
  refine ((eqWords.comp (of_linear (.of_eq (f := fun p : α × α => (enc p.1, enc p.2))
    (encIn := encPair enc enc) (encMid := encPair encBits encBits) fun _ => rfl))).mono 4
    (fun p => ?_) fun p => ?_).of_enc_eq fun p => ?_
  · simp only [length_encPair]
    nlinarith
  · simp only [length_encPair]
    omega
  · simp [enc.injective.eq_iff]

end ComputableInO
end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Compare computed values for equality, inferring their common encoding from the arguments. -/
@[fun_prop]
theorem decide_eq' {α : Type}
    {β : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    [_inst4 : DecidableEq β]
    {left : α → β}
    {right : α → β}
    (hleft : ComputableInPolyTime left encA encB)
    (hright : ComputableInPolyTime right encA encB) :
    ComputableInPolyTime
  (fun (x : α) => Decidable.decide (left x = right x)) encA encBool := by
  have heq := (ComputableInO.eq encB).computableInPolyTime
    (.of_forall_le 1 2 fun p => by simp only [length_encPair]; nlinarith) .self
  exact heq.comp (hleft.prod hright)

/-- Lawful Boolean equality compares computed values through their common encoding. -/
@[fun_prop]
theorem beq {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    [BEq β] [LawfulBEq β] {left right : α → β}
    (hleft : ComputableInPolyTime left encA encB)
    (hright : ComputableInPolyTime right encA encB) :
    ComputableInPolyTime (fun x => left x == right x) encA encBool := by
  classical
  simpa only [beq_eq_decide] using hleft.decide_eq' hright

end Turing.MultiTapeTM.ComputableInPolyTime



-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListBinaryLookup
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListBinaryLookup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:48:58.21884+00:00
-- url     : https://prove2.me/theorems/fef09221-e8f1-4460-956d-e2ff1c27e891
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup — Direct plain list lookup at a binary index
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Lookup in a computed list at a computed index encoded in binary. The index is first capped at the
--   length of the list by the saturating fold `Cslib.BitString.boundedBinaryValue`, which reads the
--   binary digits most significant first and caps every partial value. An index far beyond the list
--   therefore costs only its encoded length and is never expanded to unary; beyond the list every
--   lookup returns the default.
--
--   The capped-binary fold is the one used by the binary lookup rule of the raw calculus in
--   `Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/List.lean`. Here it is
--   certified directly, with the plain fold, the unary list length, unary subtraction and lookup at a
--   unary index. The saturating step `min cap (2 * v + b)` is computed as `cap - (cap - v - v - b)`.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime.listGetD_binary`: lookup with a fixed default at a
--     binary index, in any sized list encoding.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListBinaryLookup`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimeListBinaryLookup.lean

/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListLookup
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeNatFrontends
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
import Mathlib.Data.List.GetD

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct plain list lookup at a binary index

Lookup in a computed list at a computed index encoded in binary. The index is first capped at the
length of the list by the saturating fold `Cslib.BitString.boundedBinaryValue`, which reads the
binary digits most significant first and caps every partial value. An index far beyond the list
therefore costs only its encoded length and is never expanded to unary; beyond the list every
lookup returns the default.

The capped-binary fold is the one used by the binary lookup rule of the raw calculus in
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/List.lean`. Here it is
certified directly, with the plain fold, the unary list length, unary subtraction and lookup at a
unary index. The saturating step `min cap (2 * v + b)` is computed as `cap - (cap - v - v - b)`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.listGetD_binary`: lookup with a fixed default at a
  binary index, in any sized list encoding.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib

/-- Lookup in a computed list at a computed binary index, with a fixed default, in any sized list
encoding. The index is first capped at the length of the list, reading its binary digits most
significant first and capping every partial value, so an index far beyond the list costs only its
encoded length; beyond the list every lookup returns the default. -/
theorem listGetD_binary {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encL : List α ↪ List Bool} [ListEncoding encA encL] [SizedListEncoding encA encL]
    {l : γ → List α} {i : γ → ℕ} (d : α)
    (hl : ComputableInPolyTime l encIn encL)
    (hi : ComputableInPolyTime i encIn encNat) :
    ComputableInPolyTime (fun x => (l x).getD (i x) d) encIn encA := by
  have hlen : ComputableInPolyTime (fun x => (l x).length) encIn encUnary := by
    have h := foldl' (encA := encA) (encL := encL) (encB := encUnary) (list := l)
      (init := fun _ => 0) (step := fun n _ => n + 1) hl (const 0)
      (unary_succ.comp (fst encUnary encA)) (B := fun x => (encL (l x)).length)
      hl.polyBounded_length (fun x j _ => by
        simpa [List.foldl_const] using (Nat.min_le_right j (l x).length).trans
          (SizedListEncoding.length_le (encA := encA) (encL := encL) (l x)))
    simpa [List.foldl_const] using h
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × Bool => min p.1.1 (2 * p.1.2 + p.2.toNat))
      (encPair (encPair encUnary encUnary) encBool) encUnary := by
    have hq := fst (encPair encUnary encUnary) encBool
    have hb : ComputableInPolyTime (fun p : (ℕ × ℕ) × Bool => p.2.toNat)
        (encPair (encPair encUnary encUnary) encBool) encUnary :=
      (of_finite (encIn := encBool) (encOut := encUnary) Bool.toNat).comp
        (snd (encPair encUnary encUnary) encBool)
    have h := unary_sub.comp (hq.fst'.prod (unary_sub.comp
      ((unary_sub.comp ((unary_sub.comp (hq.fst'.prod hq.snd')).prod hq.snd')).prod hb)))
    have heq : (fun p : (ℕ × ℕ) × Bool => min p.1.1 (2 * p.1.2 + p.2.toNat)) =
        fun p => p.1.1 - (p.1.1 - p.1.2 - p.1.2 - p.2.toNat) := by
      funext p
      omega
    rw [heq]
    simpa only [Function.comp_def] using h
  have hcap : ComputableInPolyTime
      (fun x => BitString.boundedBinaryValue (l x).length (encNat (i x)).reverse)
      encIn encUnary :=
    foldlWith (encA := encBool) (encL := encBits) (encP := encUnary) (encB := encUnary)
      (par := fun x => (l x).length) (list := fun x => (encNat (i x)).reverse)
      (step := fun cap value bit => min cap (2 * value + bit.toNat))
      hlen (bitsReverse.comp (hi.of_enc_eq (encD := encBits) fun _ => rfl)) (const 0) hstep
      (B := fun x => (l x).length)
      (by simpa only [encUnary_apply, List.length_replicate] using hlen.polyBounded_length)
      (fun x j _ => by
        simpa only [encUnary_apply, List.length_replicate, BitString.boundedBinaryValue] using
          BitString.boundedBinaryValue_le (l x).length ((encNat (i x)).reverse.take j))
  have heq : (fun x => (l x).getD (i x) d) = fun x =>
      (l x).getD (BitString.boundedBinaryValue (l x).length (encNat (i x)).reverse) d := by
    funext x
    rw [BitString.boundedBinaryValue_eq, encNat_apply, BitString.binaryValue_reverse_bits]
    rcases le_total (i x) (l x).length with h | h
    · rw [Nat.min_eq_right h]
    · rw [Nat.min_eq_left h, List.getD_eq_default _ _ h, List.getD_eq_default _ _ le_rfl]
  rw [heq]
  exact (listGetD d).comp (hl.prod hcap)

end Turing.MultiTapeTM.ComputableInPolyTime



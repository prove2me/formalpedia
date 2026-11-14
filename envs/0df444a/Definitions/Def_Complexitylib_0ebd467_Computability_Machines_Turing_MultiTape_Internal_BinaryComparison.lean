-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryComparison
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryComparison
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:48:06.645478+00:00
-- url     : https://prove2.me/theorems/b8d55803-2283-4aea-af6a-9638c81f9596
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison — Binary subtraction and comparison
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The existing borrow algorithm runs through consuming input-word cursors, so every round costs
--   only a linear amount and there are at most as many rounds as input digits. The plain machine
--   certificate retains quadratic time and linear output-charged workspace, independently of the
--   numeric operands.
--
--   Comparison is computed by one zip transducer (`Turing.MultiTapeTM.ZipTransducer`) that reads both
--   operands in lockstep, least significant digit first, and remembers whether the digits read so far
--   compare as less than (or as less than or equal); equality by one that remembers whether they agree.
--   Both run in linear time and in work space linear in the first operand.
--
--   ### Main results
--
--   * `ComputableInO.natSub`: truncated subtraction in quadratic time and linear charged space.
--   * `Turing.MultiTapeTM.computableInTimeAndSpace_natLt`: strict comparison within
--     `3 * (encPair encNat encNat p).length + 1` steps and `(encNat p.1).length + 2` work-tape cells.
--   * `Turing.MultiTapeTM.computableInTimeAndSpace_natLe`,
--     `Turing.MultiTapeTM.computableInTimeAndSpace_natEq`: non-strict comparison and equality
--     within the same bounds.
--   * `Turing.MultiTapeTM.ComputableInDegree.natLt`, `.natLe`, `.natEq`: their linear
--     forms.
--   * `ComputableInO.natLt`: strict comparison with the bounds of `ComputableInO.natSub`.
--
--   **Contents.** The module is published as a whole: 18 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryComparison`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/BinaryComparison.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryNormalization
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeClosure
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreePrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeComposition
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Subtraction
import Mathlib.Tactic.Linarith
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_ZipTransducer

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Binary subtraction and comparison

The existing borrow algorithm runs through consuming input-word cursors, so every round costs
only a linear amount and there are at most as many rounds as input digits. The plain machine
certificate retains quadratic time and linear output-charged workspace, independently of the
numeric operands.

Comparison is computed by one zip transducer (`Turing.MultiTapeTM.ZipTransducer`) that reads both
operands in lockstep, least significant digit first, and remembers whether the digits read so far
compare as less than (or as less than or equal); equality by one that remembers whether they agree.
Both run in linear time and in work space linear in the first operand.

## Main results

* `ComputableInO.natSub`: truncated subtraction in quadratic time and linear charged space.
* `Turing.MultiTapeTM.computableInTimeAndSpace_natLt`: strict comparison within
  `3 * (encPair encNat encNat p).length + 1` steps and `(encNat p.1).length + 2` work-tape cells.
* `Turing.MultiTapeTM.computableInTimeAndSpace_natLe`,
  `Turing.MultiTapeTM.computableInTimeAndSpace_natEq`: non-strict comparison and equality
  within the same bounds.
* `Turing.MultiTapeTM.ComputableInDegree.natLt`, `.natLe`, `.natEq`: their linear
  forms.
* `ComputableInO.natLt`: strict comparison with the bounds of `ComputableInO.natSub`.
-/

@[expose] public section
namespace Turing.MultiTapeTM

/-- Comparison as a zip transducer. The state records whether the digits read so far, which are
the low-order digits, compare as less than; a differing digit overrides it. Started in `false` it
decides `<`, started in `true` it decides `≤`. -/
private def ltZip (q₀ : Bool) : ZipTransducer Bool where
  q₀ := q₀
  step c x := (if x.1.getD false = x.2.getD false then c else x.2.getD false, [])
  final c := [c]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma run_ltZip (q₀ c : Bool) (u v : List Bool) :
    (ltZip q₀).run c u v = [decide (ofBits u < ofBits v ∨ ofBits u = ofBits v ∧ c = true)] := by
  induction u generalizing v c with
  | nil =>
    induction v generalizing c with
    | nil => cases c <;> simp [ltZip, ofBits]
    | cons b v ih =>
      rw [ZipTransducer.run_nil_cons, ih]
      simp only [ltZip, ofBits, List.foldr_cons, List.foldr_nil, Nat.bit_val, List.nil_append,
        List.cons.injEq, and_true, decide_eq_decide]
      cases b <;> cases c <;> simp <;> omega
  | cons a u ih =>
    cases v with
    | nil =>
      rw [ZipTransducer.run_cons_nil, ih]
      simp only [ltZip, ofBits, List.foldr_cons, List.foldr_nil, Nat.bit_val, List.nil_append,
        List.cons.injEq, and_true, decide_eq_decide]
      cases a <;> cases c <;> simp
    | cons b v =>
      rw [ZipTransducer.run_cons_cons, ih]
      simp only [ltZip, ofBits, List.foldr_cons, Nat.bit_val, List.nil_append,
        List.cons.injEq, and_true, decide_eq_decide]
      cases a <;> cases b <;> cases c <;> simp <;> omega

private lemma ofBits_bits (n : ℕ) : ofBits n.bits = n := Nat.foldr_bit_bits n

private lemma encBool_natLt (p : ℕ × ℕ) :
    encBool (decide (p.1 < p.2)) = (ltZip false).run false (encNat p.1) (encNat p.2) := by
  rw [encBool_apply, encNat_apply, encNat_apply, run_ltZip, ofBits_bits, ofBits_bits]
  simp

private lemma encBool_natLe (p : ℕ × ℕ) :
    encBool (decide (p.1 ≤ p.2)) = (ltZip true).run true (encNat p.1) (encNat p.2) := by
  rw [encBool_apply, encNat_apply, encNat_apply, run_ltZip, ofBits_bits, ofBits_bits]
  simp [Nat.le_iff_lt_or_eq]

/-- **Binary comparison in linear time.** One zip transducer decides `a < b` from
`encPair encNat encNat (a, b)` within `3 * (encPair encNat encNat p).length + 1` steps and
`(encNat p.1).length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace_natLt :
    ComputableInTimeAndSpace (fun p : ℕ × ℕ => decide (p.1 < p.2)) (encPair encNat encNat) encBool
      (fun p => 3 * (encPair encNat encNat p).length + 1) (fun p => (encNat p.1).length + 2) :=
  (ltZip false).computableInTimeAndSpace encBool_natLt

/-- Binary comparison in linear time and work space, from `computableInTimeAndSpace_natLt`. -/
public theorem ComputableInDegree.natLt :
    ComputableInDegree (fun p : ℕ × ℕ => decide (p.1 < p.2))
      (encPair encNat encNat) encBool 1 1 :=
  (ltZip false).computableInDegree encBool_natLt

/-- **Non-strict binary comparison in linear time.** One zip transducer decides `a ≤ b` from
`encPair encNat encNat (a, b)` within `3 * (encPair encNat encNat p).length + 1` steps and
`(encNat p.1).length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace_natLe :
    ComputableInTimeAndSpace (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) (encPair encNat encNat) encBool
      (fun p => 3 * (encPair encNat encNat p).length + 1) (fun p => (encNat p.1).length + 2) :=
  (ltZip true).computableInTimeAndSpace encBool_natLe

/-- Non-strict binary comparison in linear time and work space, from
`computableInTimeAndSpace_natLe`. -/
public theorem ComputableInDegree.natLe :
    ComputableInDegree (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
      (encPair encNat encNat) encBool 1 1 :=
  (ltZip true).computableInDegree encBool_natLe

/-- Equality as a zip transducer; the state records whether all digits read so far agree. -/
private def eqZip : ZipTransducer Bool where
  q₀ := true
  step c x := (c && x.1.getD false == x.2.getD false, [])
  final c := [c]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma run_eqZip (c : Bool) (u v : List Bool) :
    eqZip.run c u v = [decide (c = true ∧ ofBits u = ofBits v)] := by
  induction u generalizing v c with
  | nil =>
    induction v generalizing c with
    | nil => cases c <;> simp [eqZip, ofBits]
    | cons b v ih =>
      rw [ZipTransducer.run_nil_cons, ih]
      cases b <;> cases c <;> simp [eqZip, ofBits, Nat.bit_val, eq_comm]
  | cons a u ih =>
    cases v with
    | nil =>
      rw [ZipTransducer.run_cons_nil, ih]
      cases a <;> cases c <;> simp [eqZip, ofBits, Nat.bit_val]
    | cons b v =>
      rw [ZipTransducer.run_cons_cons, ih]
      cases a <;> cases b <;> cases c <;> simp [eqZip, ofBits, Nat.bit_val] <;> omega

private lemma encBool_natEq (p : ℕ × ℕ) :
    encBool (decide (p.1 = p.2)) = eqZip.run eqZip.q₀ (encNat p.1) (encNat p.2) := by
  rw [encBool_apply, encNat_apply, encNat_apply, run_eqZip, ofBits_bits, ofBits_bits]
  simp [eqZip]

/-- **Binary equality in linear time.** One zip transducer decides `a = b` from
`encPair encNat encNat (a, b)` within `3 * (encPair encNat encNat p).length + 1` steps and
`(encNat p.1).length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace_natEq :
    ComputableInTimeAndSpace (fun p : ℕ × ℕ => decide (p.1 = p.2)) (encPair encNat encNat) encBool
      (fun p => 3 * (encPair encNat encNat p).length + 1) (fun p => (encNat p.1).length + 2) :=
  eqZip.computableInTimeAndSpace encBool_natEq

/-- Binary equality in linear time and work space, from `computableInTimeAndSpace_natEq`. -/
public theorem ComputableInDegree.natEq :
    ComputableInDegree (fun p : ℕ × ℕ => decide (p.1 = p.2))
      (encPair encNat encNat) encBool 1 1 :=
  eqZip.computableInDegree encBool_natEq

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInO

private abbrev encCursor :=
  encPair (encPair encBits encBits) (encPair encBool encBits)

private theorem cursorStep_inO :
    ComputableInO (fun p => BinarySub.cursorStep p.1 p.2) (encPair encCursor encBool) encCursor
      (fun p => (encPair encCursor encBool p).length)
      (fun p => (encPair encCursor encBool p).length) := by
  have hs := ComputableInDegree.fst encCursor encBool
  have hw := (ComputableInDegree.fst (encPair encBits encBits)
    (encPair encBool encBits)).comp hs
  have hl := (ComputableInDegree.fst encBits encBits).comp hw
  have hr := (ComputableInDegree.snd encBits encBits).comp hw
  have ha := (ComputableInDegree.snd (encPair encBits encBits)
    (encPair encBool encBits)).comp hs
  have hc := (ComputableInDegree.fst encBool encBits).comp ha
  have hout := (ComputableInDegree.snd encBool encBits).comp ha
  have hheads := (Internal.DecoderWords.bool_degree.comp hl).prod
    (Internal.DecoderWords.bool_degree.comp hr)
  have hflags := (ComputableInDegree.of_finite
    (encIn := encPair encBool (encPair encBool encBool))
    (encMid := encPair encBool encBool) fun q : Bool × (Bool × Bool) =>
      (BinarySub.borrow q.1 q.2.1 q.2.2, q.1 ^^ q.2.1 ^^ q.2.2)).comp (hc.prod hheads)
  have hborrow := (ComputableInDegree.fst encBool encBool).comp hflags
  have hdigit := (ComputableInDegree.snd encBool encBool).comp hflags
  have hround := ((Internal.DecoderWords.tail_degree.comp hl).prod
    (Internal.DecoderWords.tail_degree.comp hr)).prod
    (hborrow.prod (hout.append hdigit (encOut := encBits) fun _ => rfl))
  exact (show ComputableInDegree (fun p => BinarySub.cursorStep p.1 p.2)
    (encPair encCursor encBool) encCursor 1 1 from hround.mono).inO_one

/-- **Truncated subtraction in binary**, `b - a` from `(a, b)`. -/
public theorem natSub :
    ComputableInO (fun p : ℕ × ℕ => p.2 - p.1) (encPair encNat encNat) encNat
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 := by
  let clock (p : ℕ × ℕ) := p.2.bits ++ p.1.bits
  let init (p : ℕ × ℕ) := ((p.2.bits, p.1.bits), (false, ([] : List Bool)))
  have hbits : ComputableInO Nat.bits encNat encBits (fun n => (encNat n).length)
      (fun n => (encNat n).length) := of_eq fun _ => rfl
  have hl := hbits.comp_linear (snd encNat encNat)
  have hr := hbits.comp_linear (fst encNat encNat)
  have hclock := hl.append hr (encOut := encBits) (g := clock) fun _ => rfl
  have hinit := (hl.prod hr).prod
    (const (encMid := encPair encBool encBits) (false, ([] : List Bool)))
  have hstate (p : ℕ × ℕ) (i : ℕ) :
      (encCursor (((clock p).take i).foldl BinarySub.cursorStep (init p))).length ≤
        8 * (encPair encNat encNat p).length + 10 := by
    obtain ⟨hl, hr, ho⟩ := BinarySub.cursorStep_lengths ((clock p).take i)
      p.2.bits p.1.bits (false, [])
    have ht : ((clock p).take i).length ≤ p.2.bits.length + p.1.bits.length :=
      (List.length_take_le' i (clock p)).trans_eq (by simp only [clock, List.length_append])
    simp only [encCursor, init, length_encPair, encBits_apply, encBool_apply,
      List.length_singleton, encNat_apply]
    simp only [List.length_nil, Nat.zero_add] at ho
    omega
  have hround (p : ℕ × ℕ) (i : ℕ) (hi : i < (clock p).length) :
      (encPair encCursor encBool
        (((clock p).take i).foldl BinarySub.cursorStep (init p), (clock p)[i])).length ≤
        20 * (encPair encNat encNat p).length + 30 := by
    have := hstate p i
    rw [length_encPair]
    simp only [encBool_apply, List.length_singleton]
    omega
  have hfold := (foldl hclock hinit cursorStep_inO
    (R := fun p => 20 * (encPair encNat encNat p).length + 30)
    (Q := fun p => 20 * (encPair encNat encNat p).length + 30)
    (B := fun p => 8 * (encPair encNat encNat p).length + 10)
    hround hround (fun p i _ => hstate p i)).mono
    (T' := fun p => ((encPair encNat encNat p).length + 1) ^ 2)
    (S' := fun p => (encPair encNat encNat p).length + 1) 100
    (fun p => by
      simp only [clock, encBits_apply, List.length_append, length_encPair, encNat_apply]
      nlinarith)
    (fun p => by
      simp only [clock, encBits_apply, List.length_append, length_encPair, encNat_apply]
      omega)
  have hacc := hfold.snd'
  have heq (p : ℕ × ℕ) : ((clock p).foldl BinarySub.cursorStep (init p)).2 =
      (BinarySub.digitPairs (p.2, p.1)).foldl BinarySub.subStep (false, []) := by
    rw [BinarySub.foldl_cursorStep]
    simp only [clock, List.length_append, BinarySub.digitPairs]
  have h := hacc.fst'.ite (const 0) (bitsToNat.comp_linear hacc.snd')
  refine (h.mono 3 (fun p => ?_) (fun p => ?_)).of_enc_eq fun p => ?_
  · split_ifs <;> simp only [length_encPair, encNat_apply] <;> nlinarith
  · split_ifs <;> omega
  · change encNat (p.2 - p.1) = encNat
      (if ((clock p).foldl BinarySub.cursorStep (init p)).2.1 then 0
        else ofBits ((clock p).foldl BinarySub.cursorStep (init p)).2.2)
    rw [heq]
    exact congrArg encNat (BinarySub.sub_eq (p.2, p.1))

/-- **The strict order in binary**, from the linear zip-transducer certificate
`Turing.MultiTapeTM.computableInTimeAndSpace_natLt`. -/
public theorem natLt :
    ComputableInO (fun p : ℕ × ℕ => decide (p.1 < p.2)) (encPair encNat encNat) encBool
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 :=
  (of_linear ComputableInDegree.natLt).mono 1
    (fun p => by have := Nat.le_self_pow two_ne_zero ((encPair encNat encNat p).length + 1); omega)
    (fun _ => by omega)

end Turing.MultiTapeTM.ComputableInO



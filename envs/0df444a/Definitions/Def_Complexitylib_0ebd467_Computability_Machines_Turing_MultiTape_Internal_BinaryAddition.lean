-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryAddition
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryAddition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:47:47.902877+00:00
-- url     : https://prove2.me/theorems/1e31dd84-7a37-47f8-91f7-a189921c8bbe
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition — Binary addition, bitwise disjunction and multiplication
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Addition and bitwise disjunction are computed by zip transducers
--   (`Turing.MultiTapeTM.ZipTransducer`) that read both operands in lockstep, least significant digit
--   first. The addition transducer keeps the carry as its state, emits one digit of the word adder
--   `NatAdd.addBits` per pair of digits and the final carry at the end. The disjunction transducer
--   emits the disjunction of each pair of digits; the longer operand ends in a one, so the output has
--   no trailing zero. Both run in linear time and in work space linear in the first operand.
--
--   Multiplication folds the shift-and-add round `NatMul.mulStep` over the digits of the first factor.
--   Its states have linear length and each round is one addition, so it takes cubic time and linear
--   charged workspace. This is the only machine certificate for binary multiplication; the degree,
--   space and polynomial-time forms are weakenings of it.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.computableInTimeAndSpace_natAdd`: binary addition within
--     `3 * (encPair encNat encNat p).length + 1` steps and `(encNat p.1).length + 2` work-tape cells.
--   * `Turing.MultiTapeTM.computableInTimeAndSpace_natOr`: bitwise disjunction within the same bounds.
--   * `Turing.MultiTapeTM.ComputableInDegree.natAdd`, `.natOr`: their linear forms.
--   * `Turing.MultiTapeTM.ComputableInO.natAdd`: binary addition in quadratic time and linear charged
--     workspace.
--   * `Turing.MultiTapeTM.ComputableInO.natMul`: binary multiplication in cubic time and linear
--     charged workspace.
--
--   **Contents.** The module is published as a whole: 13 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryAddition`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/BinaryAddition.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Arithmetic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_ZipTransducer
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Binary addition, bitwise disjunction and multiplication

Addition and bitwise disjunction are computed by zip transducers
(`Turing.MultiTapeTM.ZipTransducer`) that read both operands in lockstep, least significant digit
first. The addition transducer keeps the carry as its state, emits one digit of the word adder
`NatAdd.addBits` per pair of digits and the final carry at the end. The disjunction transducer
emits the disjunction of each pair of digits; the longer operand ends in a one, so the output has
no trailing zero. Both run in linear time and in work space linear in the first operand.

Multiplication folds the shift-and-add round `NatMul.mulStep` over the digits of the first factor.
Its states have linear length and each round is one addition, so it takes cubic time and linear
charged workspace. This is the only machine certificate for binary multiplication; the degree,
space and polynomial-time forms are weakenings of it.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_natAdd`: binary addition within
  `3 * (encPair encNat encNat p).length + 1` steps and `(encNat p.1).length + 2` work-tape cells.
* `Turing.MultiTapeTM.computableInTimeAndSpace_natOr`: bitwise disjunction within the same bounds.
* `Turing.MultiTapeTM.ComputableInDegree.natAdd`, `.natOr`: their linear forms.
* `Turing.MultiTapeTM.ComputableInO.natAdd`: binary addition in quadratic time and linear charged
  workspace.
* `Turing.MultiTapeTM.ComputableInO.natMul`: binary multiplication in cubic time and linear
  charged workspace.
-/

public section

namespace Turing.MultiTapeTM

/-- Binary addition as a zip transducer; the state is the carry. -/
private def addZip : ZipTransducer Bool where
  q₀ := false
  step c x := (NatAdd.carry (x.1.getD false) (x.2.getD false) c,
    [x.1.getD false ^^ (x.2.getD false ^^ c)])
  final c := if c then [true] else []
  length_step_le _ _ := by simp
  length_final_le c := by cases c <;> simp

private lemma run_addZip (c : Bool) (u v : List Bool) :
    addZip.run c u v = NatAdd.addBits c u v := by
  induction u generalizing c v with
  | nil =>
    rw [NatAdd.addBits]
    induction v generalizing c with
    | nil => cases c <;> simp [addZip, NatSucc.incr]
    | cons b v ih =>
      rw [ZipTransducer.run_nil_cons, ih]
      cases b <;> cases c <;> simp [addZip, NatSucc.incr, NatAdd.carry]
  | cons a u ih =>
    cases v <;> simp only [ZipTransducer.run_cons_nil, ZipTransducer.run_cons_cons, ih] <;>
      simp [addZip, NatAdd.addBits]

private lemma encNat_natAdd (p : ℕ × ℕ) :
    encNat (p.1 + p.2) = addZip.run addZip.q₀ (encNat p.1) (encNat p.2) := by
  rw [encNat_apply, encNat_apply, encNat_apply, run_addZip, NatAdd.addBits_bits]
  rfl

/-- **Binary addition in linear time.** One zip transducer computes `a + b` from
`encPair encNat encNat (a, b)` within `3 * (encPair encNat encNat p).length + 1` steps and
`(encNat p.1).length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace_natAdd :
    ComputableInTimeAndSpace (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat
      (fun p => 3 * (encPair encNat encNat p).length + 1) (fun p => (encNat p.1).length + 2) :=
  addZip.computableInTimeAndSpace encNat_natAdd

/-- Binary addition in linear time and work space, from `computableInTimeAndSpace_natAdd`. -/
public theorem ComputableInDegree.natAdd :
    ComputableInDegree (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat 1 1 :=
  addZip.computableInDegree encNat_natAdd

/-- Bitwise disjunction as a zip transducer with a single state. -/
private def orZip : ZipTransducer Unit where
  q₀ := ()
  step _ x := ((), [x.1.getD false || x.2.getD false])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma run_orZip (m n : ℕ) : orZip.run () m.bits n.bits = (m ||| n).bits := by
  have hnil (u : List Bool) : orZip.run () u [] = u ∧ orZip.run () [] u = u := by
    induction u <;> simp_all [orZip]
  induction m using Nat.binaryRec' generalizing n with
  | zero => simp [hnil]
  | bit a m hm ih =>
    induction n using Nat.binaryRec' with
    | zero => simp [hnil]
    | bit b n hn _ =>
      rw [Nat.bits_append_bit _ _ hm, Nat.bits_append_bit _ _ hn, ZipTransducer.run_cons_cons, ih,
        Nat.lor_bit, Nat.bits_append_bit _ _ fun h => by simp [hm (Nat.or_eq_zero_iff.mp h).1]]
      rfl

/-- **Bitwise disjunction in linear time.** One zip transducer computes `a ||| b` from
`encPair encNat encNat (a, b)` within `3 * (encPair encNat encNat p).length + 1` steps and
`(encNat p.1).length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace_natOr :
    ComputableInTimeAndSpace (fun p : ℕ × ℕ => p.1 ||| p.2) (encPair encNat encNat) encNat
      (fun p => 3 * (encPair encNat encNat p).length + 1) (fun p => (encNat p.1).length + 2) :=
  orZip.computableInTimeAndSpace fun p => (run_orZip p.1 p.2).symm

/-- Bitwise disjunction in linear time and work space, from `computableInTimeAndSpace_natOr`. -/
public theorem ComputableInDegree.natOr :
    ComputableInDegree (fun p : ℕ × ℕ => p.1 ||| p.2) (encPair encNat encNat) encNat 1 1 :=
  orZip.computableInDegree fun p => (run_orZip p.1 p.2).symm

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInO

/-- **Binary addition** within the quadratic clock and linear charged workspace used by its
clients, from the linear zip-transducer certificate `computableInTimeAndSpace_natAdd`. -/
theorem natAdd :
    ComputableInO (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      (fun p => (encPair encNat encNat p).length + 1) :=
  (of_linear ComputableInDegree.natAdd).mono 1
    (fun p => by have := Nat.le_self_pow two_ne_zero ((encPair encNat encNat p).length + 1); omega)
    (fun _ => by omega)

private abbrev encMul := encPair encNat encNat

private theorem mulStep_inO :
    ComputableInO (fun p : (ℕ × ℕ) × Bool => NatMul.mulStep p.1 p.2) (encPair encMul encBool)
      encMul (fun p => ((encPair encMul encBool p).length + 1) ^ 2)
      (fun p => (encPair encMul encBool p).length + 1) := by
  have hs := fst encMul encBool
  have hr := (snd encNat encNat).comp_linear hs
  have h := ((snd encMul encBool).ite (natAdd.comp hs) ((fst encNat encNat).comp_linear hs)).prod
    (natAdd.comp (hr.prod hr))
  refine (h.mono 8 (fun p => ?_) (fun p => ?_)).of_enc_eq fun p => ?_
  · simp only [Function.comp_apply, length_encPair, encBool_apply, List.length_singleton]
    split_ifs <;> nlinarith
  · simp only [Function.comp_apply, length_encPair, encBool_apply, List.length_singleton]
    split_ifs <;> omega
  · rfl

/-- **Binary multiplication** by the shift-and-add fold `NatMul.mulStep` over the digits of the
first factor. Each of the linearly many rounds adds numbers of linear length, so time is cubic and
charged workspace linear in the framed input length, independently of the numeric operands. -/
theorem natMul :
    ComputableInO (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat
      (fun p => ((encPair encNat encNat p).length + 1) ^ 3)
      (fun p => (encPair encNat encNat p).length + 1) := by
  have hbits : ComputableInO Nat.bits encNat encBits (fun n => (encNat n).length)
      (fun n => (encNat n).length) := of_eq fun _ => rfl
  have hstate (p : ℕ × ℕ) (i : ℕ) :
      (encMul ((p.1.bits.take i).foldl NatMul.mulStep (0, p.2))).length ≤
        3 * (encPair encNat encNat p).length + 1 := by
    obtain ⟨h₁, h₂⟩ := NatMul.foldl_mulStep_le (p.1.bits.take i) 0 p.2
    have hi : (p.1.bits.take i).length ≤ p.1.size := by simp [← Nat.size_eq_bits_len]
    have hacc := NatMul.size_le_of_le _ (by omega :
      (List.foldl NatMul.mulStep (0, p.2) (p.1.bits.take i)).1 ≤
        2 ^ (p.1.bits.take i).length * p.2)
    have hsh := NatMul.size_le_of_le _ h₂.le
    simp only [encMul, length_encPair, encNat_apply, Nat.size_eq_bits_len] at hacc hsh hi ⊢
    omega
  have hround (p : ℕ × ℕ) (i : ℕ) (hi : i < p.1.bits.length) :
      (encPair encMul encBool
        ((p.1.bits.take i).foldl NatMul.mulStep (0, p.2), p.1.bits[i])).length + 1 ≤
        6 * (encPair encNat encNat p).length + 6 := by
    have := hstate p i
    rw [length_encPair]
    simp only [encBool_apply, List.length_singleton]
    omega
  have hfold := foldl (hbits.comp_linear (fst encNat encNat))
    ((const (encMid := encNat) 0).prod (snd encNat encNat)) mulStep_inO
    (R := fun p => (6 * (encPair encNat encNat p).length + 6) ^ 2)
    (Q := fun p => 6 * (encPair encNat encNat p).length + 6)
    (B := fun p => 3 * (encPair encNat encNat p).length + 1)
    (fun p i hi => Nat.pow_le_pow_left (hround p i hi) 2)
    (fun p i hi => hround p i hi)
    (fun p i _ => hstate p i)
  refine ((fst encNat encNat).comp_linear hfold |>.mono 100 (fun p => ?_) (fun p => ?_))
    |>.of_enc_eq fun p => ?_
  · simp only [Function.comp_apply, encBits_apply, length_encPair, encNat_apply]
    nlinarith
  · simp only [Function.comp_apply, encBits_apply, length_encPair, encNat_apply]
    omega
  · simp only [Function.comp_apply, NatMul.foldl_mulStep, zero_add]

end Turing.MultiTapeTM.ComputableInO



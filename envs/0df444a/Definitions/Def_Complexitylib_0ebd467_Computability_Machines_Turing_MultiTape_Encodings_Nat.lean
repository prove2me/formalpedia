-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:11.97154+00:00
-- url     : https://prove2.me/theorems/a0832778-15a2-4a1a-8e59-e1cdf2b6417c
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat — The successor, predecessor and zero test in binary
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `encNat`, reexported from `Encodings.Nat.Bits`, encodes a natural number by its binary digits,
--   least significant first (`Nat.bits`).
--   Each of the three counter operations is computed by one streaming transducer that reads its input
--   once and uses no work tape:
--
--   * the successor's state is the carry: on each digit `b` in carry `c` it emits `c ^^ b` and keeps
--     the carry `c && b`, and at the end it emits a final `1` exactly when a carry remains;
--   * the predecessor turns the borrowed `0`s into `1`s and the first `1` into a `0`, which it holds
--     back until a further digit shows that it is not the leading digit, and then copies the rest;
--   * the zero test emits whether the input was empty.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.computableInTimeAndSpace_succ`, `computableInTimeAndSpace_pred`,
--     `computableInTimeAndSpace_isZero`: the operations are computable within
--     `2 * (encNat n).length + 3` steps and zero work space.
--   * `Turing.MultiTapeTM.ComputableInDegree.natSucc`, `.natPred`, `.natIsZero`: their
--     linear forms.
--
--   **Contents.** The module is published as a whole: 15 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Nat.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer_Copy
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Bits

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The successor, predecessor and zero test in binary

`encNat`, reexported from `Encodings.Nat.Bits`, encodes a natural number by its binary digits,
least significant first (`Nat.bits`).
Each of the three counter operations is computed by one streaming transducer that reads its input
once and uses no work tape:

* the successor's state is the carry: on each digit `b` in carry `c` it emits `c ^^ b` and keeps
  the carry `c && b`, and at the end it emits a final `1` exactly when a carry remains;
* the predecessor turns the borrowed `0`s into `1`s and the first `1` into a `0`, which it holds
  back until a further digit shows that it is not the leading digit, and then copies the rest;
* the zero test emits whether the input was empty.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_succ`, `computableInTimeAndSpace_pred`,
  `computableInTimeAndSpace_isZero`: the operations are computable within
  `2 * (encNat n).length + 3` steps and zero work space.
* `Turing.MultiTapeTM.ComputableInDegree.natSucc`, `.natPred`, `.natIsZero`: their
  linear forms.
-/
namespace Turing.MultiTapeTM

/-- The framed binary encoding of triples of natural numbers. -/
public abbrev encNat3 : ℕ × ℕ × ℕ ↪ List Bool := encPair encNat (encPair encNat encNat)

namespace NatSucc

/-- The successor as a transducer: the state is the carry, initially set. -/
private def succTransducer : Transducer Bool Bool where
  q₀ := true
  step c b := (c && b, [c ^^ b])
  final c := if c then [true] else []
  length_step_le _ _ := by simp
  length_final_le c := by cases c <;> simp

private lemma run_succTransducer (c : Bool) (l : List Bool) :
    succTransducer.run c l = incr c l := by
  induction l generalizing c with
  | nil => cases c <;> rfl
  | cons b l ih =>
    rw [Transducer.run_cons, ih]
    cases c <;> cases b <;> simp [succTransducer, incr]

end NatSucc

namespace NatPred

/-- The predecessor as a transducer. In the borrow state `none` each `0` becomes `1`; the first
`1` becomes a pending `0` (state `some false`), emitted only once a further digit shows it is not
the leading digit; from then on (state `some true`) the digits are copied. -/
private def predTransducer : Transducer Bool (Option Bool) where
  q₀ := none
  step
    | none, false => (none, [true])
    | none, true => (some false, [])
    | some false, b => (some true, [false, b])
    | some true, b => (some true, [b])
  final _ := []
  length_step_le q b := by rcases q with _ | _ | _ <;> cases b <;> simp
  length_final_le _ := by simp

private lemma run_predTransducer_pending (l : List Bool) :
    predTransducer.run (some false) l = if l = [] then [] else false :: l := by
  cases l with
  | nil => rfl
  | cons b l =>
    change [false, b] ++ predTransducer.run (some true) l = _
    rw [Transducer.run_eq_self predTransducer (some true) (fun _ => rfl) rfl]
    rfl

private lemma run_predTransducer (n : ℕ) : predTransducer.run none n.bits = (n - 1).bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m (by omega), show 2 * m - 1 = 2 * (m - 1) + 1 by omega,
          Nat.bit1_bits, ← ih m (by omega)]
        rfl
    · rw [Nat.bit1_bits, Nat.add_sub_cancel]
      change predTransducer.run (some false) m.bits = _
      rw [run_predTransducer_pending]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m hm.ne']
        simp [Nat.bits_eq_nil_iff, hm.ne']

/-- The zero test as a transducer: the state records that no digit has been read yet. -/
private def isZeroTransducer : Transducer Bool Bool where
  q₀ := true
  step _ _ := (false, [])
  final b := [b]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma run_isZeroTransducer (q : Bool) (l : List Bool) :
    isZeroTransducer.run q l = [q && l.isEmpty] := by
  induction l generalizing q with
  | nil => simp [isZeroTransducer]
  | cons b l ih =>
    change [] ++ isZeroTransducer.run false l = _
    simp [ih]

end NatPred

/-- A transducer certificate on `encNat` is linear in time and work space. -/
private theorem ComputableInTimeAndSpace.linear {β : Type} {encOut : β ↪ List Bool} {f : ℕ → β}
    (h : ComputableInTimeAndSpace f encNat encOut (fun n => 2 * (encNat n).length + 3)
      (fun _ => 0)) :
    ComputableInDegree f encNat encOut 1 1 :=
  ComputableInDegree.of_bounds ⟨3, fun _ => by simp only [pow_one]; omega⟩
    (DegreeBounded.const 0) h

open NatSucc in
/-- **Binary successor in linear time and zero work space.** One streaming transducer computes
`n + 1` from `encNat n` within `2 * (encNat n).length + 3` steps without work tapes. -/
public theorem computableInTimeAndSpace_succ :
    ComputableInTimeAndSpace (· + 1) encNat encNat (fun n => 2 * (encNat n).length + 3)
      (fun _ => 0) :=
  ⟨0, _, inferInstance, succTransducer.toTM, fun n => by
    rw [encNat_apply, encNat_apply, bits_succ, ← run_succTransducer]
    exact succTransducer.computesInTimeAndSpace_toTM n.bits⟩

/-- Binary successor in linear time and work space, from `computableInTimeAndSpace_succ`. -/
public theorem ComputableInDegree.natSucc :
    ComputableInDegree (· + 1) encNat encNat 1 1 :=
  computableInTimeAndSpace_succ.linear

open NatPred in
/-- **Binary predecessor in linear time and zero work space.** One streaming transducer computes
`n - 1` (so `0 ↦ 0`) from `encNat n` within `2 * (encNat n).length + 3` steps without work
tapes. -/
public theorem computableInTimeAndSpace_pred :
    ComputableInTimeAndSpace (· - 1) encNat encNat (fun n => 2 * (encNat n).length + 3)
      (fun _ => 0) :=
  ⟨0, _, inferInstance, predTransducer.toTM, fun n => by
    rw [encNat_apply, encNat_apply, ← run_predTransducer]
    exact predTransducer.computesInTimeAndSpace_toTM n.bits⟩

/-- Binary predecessor in linear time and work space, from `computableInTimeAndSpace_pred`. -/
public theorem ComputableInDegree.natPred :
    ComputableInDegree (· - 1) encNat encNat 1 1 :=
  computableInTimeAndSpace_pred.linear

open NatPred in
/-- **Binary zero test in linear time and zero work space.** One streaming transducer decides
`n = 0` from `encNat n` within `2 * (encNat n).length + 3` steps without work tapes. -/
public theorem computableInTimeAndSpace_isZero :
    ComputableInTimeAndSpace (fun n => decide (n = 0)) encNat encBool
      (fun n => 2 * (encNat n).length + 3) (fun _ => 0) :=
  ⟨0, _, inferInstance, isZeroTransducer.toTM, fun n => by
    beta_reduce
    rw [encNat_apply, encBool_apply, show decide (n = 0) = (true && n.bits.isEmpty) by
      rw [Bool.true_and, Bool.eq_iff_iff, List.isEmpty_iff, Nat.bits_eq_nil_iff,
        decide_eq_true_iff], ← run_isZeroTransducer]
    exact isZeroTransducer.computesInTimeAndSpace_toTM n.bits⟩

/-- Binary zero test in linear time and work space, from `computableInTimeAndSpace_isZero`. -/
public theorem ComputableInDegree.natIsZero :
    ComputableInDegree (fun n => decide (n = 0)) encNat encBool 1 1 :=
  computableInTimeAndSpace_isZero.linear

end Turing.MultiTapeTM



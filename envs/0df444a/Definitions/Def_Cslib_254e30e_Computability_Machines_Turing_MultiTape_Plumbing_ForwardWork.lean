-- Prove2me | Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ForwardWork
-- name    : Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ForwardWork
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:58.173514+00:00
-- url     : https://prove2.me/theorems/ab5c92b0-384a-44b6-988a-6a373d05298e
-- title:
--   Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ForwardWork — A machine that moves to the end of a word
-- statement:
--   This is module `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ForwardWork` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   `forwardWork Symbol` moves the head of its work tape to the right over the word it holds and halts
--   on the frontier, the first blank cell just past the word. It never modifies a tape, never moves the
--   input head and never outputs.
--
--   On a word of length `l`, started with the head at cell `p ≤ l`, the machine takes `l - p + 1` steps
--   and the head stays within the cells `p, …, l`.
--
--   This is a one-tape machine; to move the head of tape `i` of a `k`-tape machine to the end of its
--   word, place it there with `Turing.MultiTapeTM.tapeEmb` and transport its run with
--   `Turing.MultiTapeTM.runFrom_tapeEmb`. The input head, the output and every other tape are then
--   untouched by construction.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.forwardWork`: the one-tape machine that moves its head to the frontier of
--     its word.
--   * `Turing.MultiTapeTM.runFrom_forwardWork`: its run from the initial state.
--   * `Turing.MultiTapeTM.workTapePos_runFrom_forwardWork`: its head stays within `[p, w.length]`.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ForwardWork`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Plumbing/ForwardWork.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_WordsCfg
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_TapeLemmas

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ForwardWork` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# A machine that moves to the end of a word

`forwardWork Symbol` moves the head of its work tape to the right over the word it holds and halts
on the frontier, the first blank cell just past the word. It never modifies a tape, never moves the
input head and never outputs.

On a word of length `l`, started with the head at cell `p ≤ l`, the machine takes `l - p + 1` steps
and the head stays within the cells `p, …, l`.

This is a one-tape machine; to move the head of tape `i` of a `k`-tape machine to the end of its
word, place it there with `Turing.MultiTapeTM.tapeEmb` and transport its run with
`Turing.MultiTapeTM.runFrom_tapeEmb`. The input head, the output and every other tape are then
untouched by construction.

## Main results

* `Turing.MultiTapeTM.forwardWork`: the one-tape machine that moves its head to the frontier of
  its word.
* `Turing.MultiTapeTM.runFrom_forwardWork`: its run from the initial state.
* `Turing.MultiTapeTM.workTapePos_runFrom_forwardWork`: its head stays within `[p, w.length]`.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The one-tape machine that moves its head to the end of its word. Over a symbol it moves right;
on the first blank it halts without moving. -/
public def forwardWork (Symbol : Type*) : MultiTapeTM 1 Symbol Unit :=
  ofTr () fun _ _ work ↦
    match work 0 with
    | some _ => ⟨0, fun _ => (none, 1), none, some ()⟩
    | none => ⟨0, fun _ => (none, 0), none, none⟩

namespace ForwardWork

variable {inpos : Fin (input.length + 2)} {out : List Symbol}

/-- Walking right over the word: from cell `p`, after `n` steps with `p + n ≤ w.length` the head
is at cell `p + n`. -/
lemma runFrom_walk {w : List Symbol} {p : ℕ} (n : ℕ) (hn : p + n ≤ w.length) :
    (forwardWork Symbol).runFrom
        ⟨some (), inpos, fun _ => tapeOfList w, fun _ => (p : ℤ), out⟩ n =
      ⟨some (), inpos, fun _ => tapeOfList w, fun _ => (p : ℤ) + n, out⟩ := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    have hsym : tapeOfList w ((p : ℤ) + n) = some (w[p + n]'(by lia)) := by
      rw [← Nat.cast_add, tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by lia)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by lia), step_of_state rfl]
    simp [forwardWork, Action.apply, Cfg.workTapeSymbols, hsym, add_assoc]

end ForwardWork

open ForwardWork in
/-- **The run of the machine that moves to the end of the word.** Started with the tape holding a
word `w` and the head at a cell `p` with `p + n = w.length`, after `n + 1` steps the machine has
halted with the head on the frontier `w.length` and nothing else changed. -/
public theorem runFrom_forwardWork (inpos : Fin (input.length + 2)) (w : List Symbol)
    (out : List Symbol) {p n : ℕ} (hpn : p + n = w.length) :
    (forwardWork Symbol).runFrom
        ⟨some (forwardWork Symbol).q₀, inpos, fun _ => tapeOfList w, fun _ => (p : ℤ), out⟩
        (n + 1) =
      ⟨none, inpos, fun _ => tapeOfList w, fun _ => (w.length : ℤ), out⟩ := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, runFrom_walk _ hpn.le,
    show (p : ℤ) + n = w.length by lia, step_of_state rfl]
  simp [forwardWork, Action.apply, Cfg.workTapeSymbols]

/-- At every step, the head is within `[p, w.length]`. -/
public theorem workTapePos_runFrom_forwardWork (inpos : Fin (input.length + 2))
    (w : List Symbol) (out : List Symbol) {p : ℕ} (hp : p ≤ w.length) (m : ℕ) :
    ((forwardWork Symbol).runFrom
        ⟨some (forwardWork Symbol).q₀, inpos, fun _ => tapeOfList w, fun _ => (p : ℤ), out⟩
        m).workTapePos 0 ∈ Set.Icc (p : ℤ) w.length := by
  rcases Nat.lt_or_ge m (w.length - p + 1) with hlt | hge
  · rw [ForwardWork.runFrom_walk m (by lia)]
    simp only [Set.mem_Icc]
    constructor <;> lia
  · have hrun := runFrom_forwardWork inpos w out (Nat.add_sub_cancel' hp)
    rw [runFrom_eq_of_halt _ _ hge (by rw [hrun]), hrun]
    simp [hp]

end Turing.MultiTapeTM



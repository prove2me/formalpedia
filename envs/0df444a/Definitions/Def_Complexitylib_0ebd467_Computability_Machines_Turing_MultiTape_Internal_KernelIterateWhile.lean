-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelIterateWhile
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelIterateWhile
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:11.271206+00:00
-- url     : https://prove2.me/theorems/27ffae43-f3cd-4af5-8f7c-0a1cc5fe68bc
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelIterateWhile — The existing iterate-while machine and its fixed-machine run law
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelIterateWhile` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Machine programs, tape layouts and resource formulas are preserved from the original module.
--
--   **Contents.** The module is published as a whole: 34 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelIterateWhile`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/KernelIterateWhile.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- The newer version of cslib PR #1112 @0b9e55ce, which is on an older base.

public import Mathlib.Data.Finite.Sum
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_CopyWord
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ClearWork
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_RepeatUntilBlank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelIterateWhile` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # The existing iterate-while machine and its fixed-machine run law

Machine programs, tape layouts and resource formulas are preserved from the original module.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-! ### The tapes -/

namespace IterateWhile

section Tapes

variable (k)

/-- The tape holding the current word: the input tape of `Turing.MultiTapeTM.onWords`. -/
abbrev curTape : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 0

/-- The tape holding the next word: the output tape of `Turing.MultiTapeTM.onWords`. -/
abbrev nextTape : Fin (k + 1 + 2) := (Fin.last k).castAdd 2

/-- The flag tape of `Turing.MultiTapeTM.onWords`. -/
abbrev flagTape : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 1

/-- The tapes of `Turing.MultiTapeTM.copyWord`: from the next tape to the current tape, flagged on
the flag tape. -/
def copyEmb : Fin (0 + 1 + 2) ↪ Fin (k + 1 + 2) :=
  ⟨![curTape k, nextTape k, flagTape k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff] at h ⊢ <;> omega⟩

/-- The tapes of `Turing.MultiTapeTM.emitWord`: the current tape, flagged on the flag tape. -/
def emitEmb : Fin (0 + 2) ↪ Fin (k + 1 + 2) :=
  ⟨![curTape k, flagTape k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff] at h ⊢⟩

end Tapes

@[simp] lemma copyEmb_zero : copyEmb k 0 = curTape k := rfl
@[simp] lemma copyEmb_one : copyEmb k 1 = nextTape k := rfl
@[simp] lemma copyEmb_two : copyEmb k 2 = flagTape k := rfl
@[simp] lemma emitEmb_zero : emitEmb k 0 = curTape k := rfl
@[simp] lemma emitEmb_one : emitEmb k 1 = flagTape k := rfl

lemma curTape_ne_nextTape : curTape k ≠ nextTape k := Fin.ne_of_val_ne (by simp)

lemma flagTape_ne_nextTape : flagTape k ≠ nextTape k :=
  Fin.ne_of_val_ne (by simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_last]; omega)

lemma flagTape_ne_curTape : flagTape k ≠ curTape k := Fin.ne_of_val_ne (by simp)

/-- The words between two phases: `vc` on the current tape, `vn` on the next tape, all other
tapes blank. -/
def words (vc vn : List Symbol) : Fin (k + 1 + 2) → List Symbol :=
  Function.update (Function.update (fun _ => []) (curTape k) vc) (nextTape k) vn

@[simp]
lemma words_cur (vc vn : List Symbol) : words (k := k) vc vn (curTape k) = vc := by
  simp [words, curTape_ne_nextTape]

@[simp]
lemma words_next (vc vn : List Symbol) : words (k := k) vc vn (nextTape k) = vn := by
  simp [words]

@[simp]
lemma words_flag (vc vn : List Symbol) : words (k := k) vc vn (flagTape k) = [] := by
  simp [words, flagTape_ne_nextTape, flagTape_ne_curTape]

lemma update_words_cur (vc vn v : List Symbol) :
    Function.update (words (k := k) vc vn) (curTape k) v = words v vn := by
  rw [words, Function.update_comm curTape_ne_nextTape.symm, Function.update_idem, ← words]

lemma update_words_next (vc vn v : List Symbol) :
    Function.update (words (k := k) vc vn) (nextTape k) v = words vc v := by
  rw [words, Function.update_idem, ← words]

lemma words_nil_next (v : List Symbol) :
    words (k := k) v [] = Function.update (fun _ => []) (curTape k) v :=
  Function.update_eq_self_iff.mpr (by simp [curTape_ne_nextTape.symm])

lemma words_nil_cur (v : List Symbol) :
    words (k := k) [] v = Function.update (fun _ => []) (nextTape k) v := by
  rw [words, Function.update_eq_self]

lemma words_nil_nil : words (k := k) (Symbol := Symbol) [] [] = fun _ => [] := by
  rw [words_nil_next, Function.update_eq_self]

end IterateWhile

open IterateWhile

/-! ### The machine -/

/-- The states of `Turing.MultiTapeTM.iterateWhileRound`. -/
public abbrev IterateWhileRoundState (State : Type*) :=
  (Unit ⊕ RewindWorkState) ⊕
    (MarkWorkState ⊕ ((Unit ⊕ RewindState) ⊕ RewindWorkState) ⊕ MarkWorkState) ⊕
      (Unit ⊕ RewindWorkState) ⊕ (MarkWorkState ⊕ (State ⊕ RewindWorkState) ⊕ MarkWorkState)

/-- The states of `Turing.MultiTapeTM.iterateWhile`. -/
public abbrev IterateWhileState (State : Type*) :=
  ((Unit ⊕ RewindState) ⊕ RewindWorkState) ⊕
    RepeatUntilBlankState (IterateWhileRoundState State) ⊕
      (MarkWorkState ⊕ (Unit ⊕ RewindState) ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState

section Machine

variable (tm : MultiTapeTM k Symbol State) (mark : Symbol)

/-- One round: clear the current tape, copy the next word to it, clear the next tape and apply
`tm` from the current tape to the next tape, using `mark` to flag the left end of words. -/
noncomputable def iterateWhileRound :
    MultiTapeTM (k + 1 + 2) Symbol (IterateWhileRoundState State) :=
  ((clearWork Symbol).extendTapes (tapeEmb (curTape k))).seq
    ((copyWord (copyEmb k) mark).seq
      (((clearWork Symbol).extendTapes (tapeEmb (nextTape k))).seq (tm.onWords mark)))

/-- `tm`, applied repeatedly while its result is non-empty, using `mark` to flag the left end of
words: load the input to the next tape, repeat rounds until the next tape is empty, then output
the current word and clear its tape. -/
public noncomputable def iterateWhile :
    MultiTapeTM (k + 1 + 2) Symbol (IterateWhileState State) :=
  (loadWord Symbol (nextTape k)).seq
    ((repeatUntilBlank (nextTape k) (iterateWhileRound tm mark)).seq
      ((emitWord (emitEmb k) mark).seq ((clearWork Symbol).extendTapes (tapeEmb (curTape k)))))

end Machine

/-! ### The phases -/

namespace IterateWhile

variable (Symbol) in
lemma transformsTapes_clearCur (vc vn : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb (curTape k)))
      (fun _ ws => ws = words vc vn) (fun _ _ ws' e => ws' = words [] vn ∧ e = [])
      (3 * (vc.length + 1)) (vc.length + 1 + (k + 1 + 2)) :=
  (transformsTapes_clearWork_tapeEmb _ vc).imp (fun _ _ h => by rw [h, words_cur])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_cur], he⟩) le_rfl le_rfl

variable (Symbol) in
lemma transformsTapes_clearNext (vc vn : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb (nextTape k)))
      (fun _ ws => ws = words vc vn) (fun _ _ ws' e => ws' = words vc [] ∧ e = [])
      (3 * (vn.length + 1)) (vn.length + 1 + (k + 1 + 2)) :=
  (transformsTapes_clearWork_tapeEmb _ vn).imp (fun _ _ h => by rw [h, words_next])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_next], he⟩) le_rfl le_rfl

lemma transformsTapes_copy (mark : Symbol) (v : List Symbol) :
    TransformsTapes (copyWord (copyEmb k) mark) (fun _ ws => ws = words [] v)
      (fun _ _ ws' e => ws' = words v v ∧ e = [])
      (3 * v.length + 10) (4 * v.length + (k + 1 + 2) + 15) :=
  (transformsTapes_copyWord (copyEmb k) mark v).imp (fun _ _ h => by subst h; simp)
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, copyEmb_zero, update_words_cur], he⟩) le_rfl le_rfl

-- vendored: the space bounds of `onWords` and `loadWord` from here on are 3 and 1 cells larger
-- than in crei:crei/tidy-universal, following the space bounds of cslib #1111
lemma transformsTapes_onWords_step {tm : MultiTapeTM k Symbol State} (mark : Symbol)
    {v v' : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace v v' t s) :
    TransformsTapes (tm.onWords mark) (fun _ ws => ws = words v [])
      (fun _ _ ws' e => ws' = words v v' ∧ e = [])
      (t + v'.length + 6) (s + 2 * v.length + 2 * v'.length + 3 * k + 18) :=
  (h.onWords mark).imp (fun _ _ hws => hws.trans (words_nil_next v))
    (fun _ _ _ _ hws ⟨h', he⟩ => ⟨by rw [h', hws, update_words_next], he⟩) le_rfl le_rfl

/-- One round takes `vp` on the current tape and `v` on the next tape to `v` on the current tape
and `v'` on the next tape. -/
lemma transformsTapes_iterateWhileRound {tm : MultiTapeTM k Symbol State} (mark : Symbol)
    {vp v v' : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace v v' t s) :
    TransformsTapes (iterateWhileRound tm mark) (fun _ ws => ws = words vp v)
      (fun _ _ ws' e => ws' = words v v' ∧ e = [])
      (t + 3 * vp.length + 6 * v.length + v'.length + 22)
      (s + vp.length + 7 * v.length + 2 * v'.length + 6 * k + 44) :=
  ((transformsTapes_clearCur Symbol vp v).seq_eq ((transformsTapes_copy mark v).seq_eq
    ((transformsTapes_clearNext Symbol v v).seq_eq (transformsTapes_onWords_step mark h)))).imp
    (fun _ _ h => h) (fun _ _ _ _ _ ⟨h', he⟩ => ⟨h', by simp [he]⟩) (by omega) (by omega)

lemma transformsTapes_load (v : List Symbol) :
    TransformsTapes (loadWord Symbol (nextTape k)) (fun inp ws => inp = v ∧ ws = fun _ => [])
      (fun _ _ ws' e => ws' = words [] v ∧ e = [])
      (3 * v.length + 6) (2 * v.length + (k + 1 + 2) + 3) :=
  (transformsTapes_loadWord (nextTape k) v).imp (fun _ _ ⟨hin, hws⟩ => ⟨hin, by rw [hws]⟩)
    (fun _ _ _ _ ⟨_, hws⟩ ⟨h', he⟩ => ⟨by rw [h', hws, words_nil_cur], he⟩) le_rfl le_rfl

lemma transformsTapes_emit (mark : Symbol) (v : List Symbol) :
    TransformsTapes (emitWord (emitEmb k) mark) (fun _ ws => ws = words v [])
      (fun _ _ ws' e => ws' = words v [] ∧ e = v)
      (2 * v.length + 8) (2 * v.length + (k + 1 + 2) + 10) :=
  (transformsTapes_emitWord (emitEmb k) mark v).imp (fun _ _ h => by subst h; simp)
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨h'.trans h, he⟩) le_rfl le_rfl

end IterateWhile

/-! ### Iterating a machine -/

open IterateWhile in
/-- If `tm` computes `w (n + 1)` from `w n` tidily within `t` steps and `s` cells for every
`n ≤ r`, the words `w n` for `n ≤ r` have length at most `l`, and `w (n + 1)` is empty exactly for
`n = r`, then `tm.iterateWhile mark` computes `w r` from `w 0` tidily. -/
public theorem computesTidily_iterateWhile {tm : MultiTapeTM k Symbol State}
    {w : ℕ → List Symbol} {r t s l : ℕ}
    (h : ∀ n ≤ r, tm.ComputesTidilyInTimeAndSpace (w n) (w (n + 1)) t s)
    (hl : ∀ n ≤ r, (w n).length ≤ l) (hne : ∀ n < r, w (n + 1) ≠ []) (hnil : w (r + 1) = [])
    (mark : Symbol) :
    (tm.iterateWhile mark).ComputesTidilyInTimeAndSpace (w 0) (w r)
      ((r + 1) * (t + 10 * l + 24) + 8 * l + 17)
      (2 * (k + 3) * (s + 10 * l + 6 * k + 44) + 5 * l + 4 * k + 26) := by
  have hl' (n : ℕ) (hn : n ≤ r) : (w (n + 1)).length ≤ l := by
    rcases hn.lt_or_eq with hn | rfl
    exacts [hl _ hn, by simp [hnil]]
  -- the word on the current tape at the start of round `n`
  let prev : ℕ → List Symbol := fun | 0 => [] | n + 1 => w n
  have hprev (n : ℕ) (hn : n ≤ r) : (prev n).length ≤ l := by
    cases n with
    | zero => simp [prev]
    | succ n => exact hl n (by omega)
  -- each round, within uniform bounds
  have hround (n : ℕ) (hn : n ≤ r) := by
    have := hprev n hn; have := hl n hn; have := hl' n hn
    exact (transformsTapes_iterateWhileRound mark (vp := prev n) (h n hn)).mono
      (t' := t + 10 * l + 23) (s' := s + 10 * l + 6 * k + 44) (by omega) (by omega)
  have hloop := (transformsTapes_repeatUntilBlank (nextTape k) (tm := iterateWhileRound tm mark)
    (P := fun n _ ws emitted => ws = words (prev n) (w n) ∧ emitted = [])
    (R := fun _ ws emitted => ws = words (w r) [] ∧ emitted = [])
    (fun n hn _ => (hround n hn.le).imp (fun _ _ hP => hP.1)
      (fun _ _ _ _ ⟨_, hem⟩ ⟨hws', he⟩ => ⟨⟨hws', by simp [hem, he]⟩,
        by rw [hws', words_next]; exact hne n hn⟩) le_rfl le_rfl)
    (fun _ => (hround r le_rfl).imp (fun _ _ hP => hP.1)
      (fun _ _ _ _ ⟨_, hem⟩ ⟨hws', he⟩ => ⟨⟨by rw [hws', hnil], by simp [hem, he]⟩,
        by rw [hws', words_next, hnil]⟩) le_rfl le_rfl)).imp
    (P' := fun _ ws => ws = words [] (w 0))
    (Q' := fun _ _ ws' e => ws' = words (w r) [] ∧ e = [])
    (fun _ _ h => ⟨h, rfl⟩) (fun _ _ _ _ _ h => h) le_rfl le_rfl
  refine ((transformsTapes_load (k := k) (w 0)).seq_eq (hloop.seq_eq
    ((transformsTapes_emit mark (w r)).seq_eq (transformsTapes_clearCur Symbol (w r) [])))).imp
    (fun _ _ h => h) (fun _ _ _ _ _ ⟨hws, he⟩ => ⟨hws.trans words_nil_nil, by simp [he]⟩) ?_ ?_
  all_goals have := hl 0 (Nat.zero_le _); have := hl r le_rfl; ring_nf; omega

end Turing.MultiTapeTM



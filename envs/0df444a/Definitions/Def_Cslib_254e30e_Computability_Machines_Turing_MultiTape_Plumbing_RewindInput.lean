-- Prove2me | Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput
-- name    : Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:00.287866+00:00
-- url     : https://prove2.me/theorems/c1924d0b-29b5-48fb-8fb7-2ff1ab2f1350
-- title:
--   Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput — A machine that rewinds the input head
-- statement:
--   This is module `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   A two-state machine that, when started in its initial state at any input-head position, returns the
--   head to position 1 (the first input symbol when the input is nonempty, otherwise the right boundary)
--   and halts there. It has no work tapes at all and never outputs, so running it in between two phases
--   of a computation re-normalizes the input head without disturbing anything else: place it inside a
--   machine with `k` work tapes with `Turing.MultiTapeTM.noTapes` and transport its run with
--   `Turing.MultiTapeTM.runFrom_noTapes`, which leaves every work tape and work head where it was.
--
--   In its initial state `start` the machine moves the input head one cell left and enters state `walk`.
--   The input head is clamped at the left boundary, so this has no effect if the head already is at
--   position `0`, and it moves a head at the right boundary `input.length + 1` back onto the input.
--   In state `walk` the machine moves left over symbols. Since the input tape holds a list of
--   (non-blank) symbols, the first blank to the left of the head is the cell at position `0`; the
--   halting transition moves right, onto position `1`.
--
--   From position `p` the run halts after `p + 1` steps, or after `2` steps if `p = 0`.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.rewindInput`: the machine that rewinds the input head.
--   * `Turing.MultiTapeTM.runFrom_rewindInput`: its run from the initial state.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Plumbing/RewindInput.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# A machine that rewinds the input head

A two-state machine that, when started in its initial state at any input-head position, returns the
head to position 1 (the first input symbol when the input is nonempty, otherwise the right boundary)
and halts there. It has no work tapes at all and never outputs, so running it in between two phases
of a computation re-normalizes the input head without disturbing anything else: place it inside a
machine with `k` work tapes with `Turing.MultiTapeTM.noTapes` and transport its run with
`Turing.MultiTapeTM.runFrom_noTapes`, which leaves every work tape and work head where it was.

In its initial state `start` the machine moves the input head one cell left and enters state `walk`.
The input head is clamped at the left boundary, so this has no effect if the head already is at
position `0`, and it moves a head at the right boundary `input.length + 1` back onto the input.
In state `walk` the machine moves left over symbols. Since the input tape holds a list of
(non-blank) symbols, the first blank to the left of the head is the cell at position `0`; the
halting transition moves right, onto position `1`.

From position `p` the run halts after `p + 1` steps, or after `2` steps if `p = 0`.

## Main results

* `Turing.MultiTapeTM.rewindInput`: the machine that rewinds the input head.
* `Turing.MultiTapeTM.runFrom_rewindInput`: its run from the initial state.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The control states of the rewinding machine: `start` takes one unconditional step left,
`walk` moves left towards the left boundary of the input. -/
public inductive RewindState : Type
  | start
  | walk
  deriving DecidableEq

public instance : Fintype RewindState := ⟨{.start, .walk}, fun q => by cases q <;> simp⟩

/-- The only kind of action the rewinding machine takes: move the input head by `m` and enter
`state`, without output. -/
abbrev inputAction (m : SignType) (state : Option RewindState) : Action 0 Symbol RewindState :=
  ⟨m, nofun, none, state⟩

/-- The rewinding machine. In state `start` it moves the input head left, unconditionally, and
enters `walk`. In state `walk` it moves left over a symbol; on the first blank it moves right and
halts. The machine has no work tapes and nothing is output. -/
public def rewindInput (Symbol : Type*) : MultiTapeTM 0 Symbol RewindState :=
  ofTr .start fun q inp _ =>
    match q, inp with
    | .start, _ => inputAction (-1) (some .walk)
    | .walk, some _ => inputAction (-1) (some .walk)
    | .walk, none => inputAction 1 none

namespace Rewind

variable {tapes : Fin 0 → ℤ → Option Symbol} {heads : Fin 0 → ℤ} {out : List Symbol}

/-- A live step moves the input head and changes the state; nothing else changes. -/
lemma step_eq {c : Cfg 0 Symbol RewindState input} {q : RewindState} (hc : c.state = some q) :
    (rewindInput Symbol).step c =
      let a := (rewindInput Symbol).tr q c.inputSymbol c.workTapeSymbols
      ⟨a.state, moveInputPos c.inputPos a.inputTape, c.workTapes, c.workTapePos, c.output⟩ := by
  rw [step_of_state hc]
  refine Cfg.ext rfl rfl (Subsingleton.elim _ _) (Subsingleton.elim _ _) ?_
  simp only [rewindInput, tr_ofTr, Action.apply_output]
  split <;> simp

/-- From `walk` at position `p ≤ input.length` the machine halts with the input head at position `1`
after `p + 1` steps. -/
lemma runFrom_walk (p : Fin (input.length + 2)) (hp : p.val ≤ input.length) :
    (rewindInput Symbol).runFrom ⟨some .walk, p, tapes, heads, out⟩ (p.val + 1) =
      ⟨none, 1, tapes, heads, out⟩ := by
  induction hj : p.val generalizing p with
  | zero =>
    obtain rfl : p = 0 := Fin.ext hj
    rw [runFrom, Function.iterate_one, step_eq rfl, inputSymbol_eq_none_of_boundary (.inl rfl)]
    simp only [rewindInput, tr_ofTr]
    rfl
  | succ j ih =>
    rw [runFrom, Function.iterate_succ_apply, ← runFrom, step_eq rfl,
      inputSymbolInner j (by grind) (by omega)]
    simp only [rewindInput, tr_ofTr]
    exact ih (moveInputPos p .neg) (by grind [SignType.cast]) (by grind [SignType.cast])

end Rewind

/-- From its initial state at input position `p` the machine halts after `p - 1 + 2` steps, with
the input head at position `1` and everything else unchanged. -/
public theorem runFrom_rewindInput (p : Fin (input.length + 2))
    (tapes : Fin 0 → ℤ → Option Symbol) (heads : Fin 0 → ℤ) (out : List Symbol) :
    (rewindInput Symbol).runFrom ⟨some (rewindInput Symbol).q₀, p, tapes, heads, out⟩
      (p.val - 1 + 2) = ⟨none, 1, tapes, heads, out⟩ := by
  have h : (moveInputPos p .neg).val = p.val - 1 := by grind [SignType.cast]
  rw [runFrom, Function.iterate_succ_apply, Rewind.step_eq rfl, ← runFrom, ← h]
  simp only [rewindInput, tr_ofTr]
  exact Rewind.runFrom_walk (moveInputPos p .neg) (by omega)

end Turing.MultiTapeTM



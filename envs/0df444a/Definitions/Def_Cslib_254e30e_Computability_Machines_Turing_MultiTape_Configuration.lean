-- Prove2me | Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Configuration
-- name    : Cslib_254e30e_Computability_Machines_Turing_MultiTape_Configuration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:04.068143+00:00
-- url     : https://prove2.me/theorems/e1a75709-b36c-477c-b838-6d0b66ca36f8
-- title:
--   Cslib.Computability.Machines.Turing.MultiTape.Configuration — Configurations of Multi-Tape Turing Machines
-- statement:
--   This is module `Cslib.Computability.Machines.Turing.MultiTape.Configuration` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
--   write-only output tape, together with what a single transition does to a configuration.
--
--   The configurations are used by both deterministic and nondeterministic multi-tape Turing machines
--   and give instantaneous descriptions of their state. An `Action` describes how one configuration
--   transitions to the next. It records which way the input head moves, what is written and where the
--   work heads move, which symbol is emitted and which state follows. `Action.apply` carries out the
--   action on a configuration.
--
--   ### Design
--
--   Configurations and actions are defined independently of a machine.
--
--   The output tape is part of the configuration, so the string emitted along a run can be read off
--   the configuration the run ends in. An action can optionally output one symbol, which models the
--   write-only output tape.
--
--   The input head can move freely on the input, but any move attempt beyond one cell outside the input
--   results in no movement. Restricting the movement of the input head is not essential, but useful
--   because it allows us to easily bound the number of possible configurations of a space-bounded
--   machine. Most textbooks have this restriction.
--
--   This definition is adapted from the one in [Papadimitriou94], chapter 2.3 including
--   the sub-linear space modifications from chapter 2.5 with the following changes:
--
--   - We allow Turing machines to choose to not write on a tape. This is equivalent to
--     writing the read symbol again but makes it easier to reason about the semantics.
--   - Our tapes are infinite in both directions instead of just to the right. This definition is
--     equivalent (see [AroraBarak09], Claim 1.4). It saves us from having to add a "start marker" to
--     the alphabet.
--   - We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
--     be distinguished based on the output.
--   - The input-head restriction is enforced by `Action.apply`, rather than by restricting the
--     transition relation. The two definitions are equivalent, but allowing all actions makes it
--     easier to define a universal machine.
--
--   ### Important Declarations
--
--   * `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
--       output tape
--   * `Action`: what a machine does in one step
--   * `Action.apply`: the effect of one action on a configuration
--   * `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in
--
--   ### References
--
--   * [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
--
--   **Contents.** The module is published as a whole: 23 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Configuration`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Sign.Defs
public import Mathlib.Data.Fin.Basic
public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Computability.Machines.Turing.MultiTape.Configuration` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single transition does to a configuration.

The configurations are used by both deterministic and nondeterministic multi-tape Turing machines
and give instantaneous descriptions of their state. An `Action` describes how one configuration
transitions to the next. It records which way the input head moves, what is written and where the
work heads move, which symbol is emitted and which state follows. `Action.apply` carries out the
action on a configuration.

## Design

Configurations and actions are defined independently of a machine.

The output tape is part of the configuration, so the string emitted along a run can be read off
the configuration the run ends in. An action can optionally output one symbol, which models the
write-only output tape.

The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement. Restricting the movement of the input head is not essential, but useful
because it allows us to easily bound the number of possible configurations of a space-bounded
machine. Most textbooks have this restriction.

This definition is adapted from the one in [Papadimitriou94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:

- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AroraBarak09], Claim 1.4). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The input-head restriction is enforced by `Action.apply`, rather than by restricting the
  transition relation. The two definitions are equivalent, but allowing all actions makes it
  easier to define a universal machine.

## Important Declarations

* `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
    output tape
* `Action`: what a machine does in one step
* `Action.apply`: the effect of one action on a configuration
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state or none to halt. -/
  state : Option State

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads,
- the contents of the write-only output tape
-/
@[ext]
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
  /-- the contents of the write-only output tape -/
  output : List Symbol
deriving Inhabited

/-- Two configurations with no work tapes are equal when their state, input head and output
agree. -/
lemma Cfg.ext_zero_tapes {Symbol State : Type*} {input : List Symbol}
    {cfg₁ cfg₂ : Cfg 0 Symbol State input} (state : cfg₁.state = cfg₂.state)
    (inputPos : cfg₁.inputPos = cfg₂.inputPos) (output : cfg₁.output = cfg₂.output) :
    cfg₁ = cfg₂ :=
  Cfg.ext state inputPos (funext fun i => i.elim0) (funext fun i => i.elim0) output

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement.

The addition is performed in `ℤ` before clamping. Performing it in `Fin (n + 2)` would wrap an
outward boundary move to the opposite end of the input. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m.cast : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

@[simp]
lemma moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) :
    moveInputPos pos 0 = pos := by
  apply Fin.ext
  simp [moveInputPos, pos.isLt]

@[simp]
lemma moveInputPos_leftBoundary {n : ℕ} :
    moveInputPos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  simp [moveInputPos]

@[simp]
lemma moveInputPos_rightBoundary {n : ℕ} :
    moveInputPos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  unfold moveInputPos
  rw [dif_neg (by simp; omega)]

/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => h (Fin.ext hz))
  unfold moveInputPos
  apply Fin.ext
  rw [dif_pos] <;> simp <;> omega

/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  unfold moveInputPos
  rw [dif_pos]
  · apply Fin.ext
    simp
  · simp
    omega

/-- The value of the input head after a move, as a clamped integer. `omega`-friendly. -/
lemma val_moveInputPos_eq {n : ℕ} (pos : Fin (n + 2)) (m : SignType) :
    ((moveInputPos pos m).val : ℤ) = min ((n : ℤ) + 1) (max 0 ((pos.val : ℤ) + (m.cast : ℤ))) := by
  grind

/-- The input head moves by at most one position. -/
lemma val_moveInputPos_le {n : ℕ} (pos : Fin (n + 2)) (m : SignType) :
    (moveInputPos pos m).val ≤ pos.val + 1 := by
  have h := val_moveInputPos_eq pos m
  have hmc : (m.cast : ℤ) = -1 ∨ (m.cast : ℤ) = 0 ∨ (m.cast : ℤ) = 1 := by
    rcases m with _ | _ | _ <;> simp [SignType.cast]
  omega

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by grind)

/-- At either boundary of the input, the head reads a blank. -/
lemma inputSymbol_eq_none_of_boundary {cfg : Cfg k Symbol State input}
    (h : cfg.inputPos.val = 0 ∨ cfg.inputPos.val = input.length + 1) :
    cfg.inputSymbol = none := by
  grind [Cfg.inputSymbol]

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  grind [Cfg.inputSymbol]

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- A configuration is halted when it has no state to continue from. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The same configuration with a word prepended to the output tape. A machine never reads its
output, so prepending to it preserves steps: cf. `Turing.MultiTapeNTM.prependOutputHom`. -/
@[simps] def Cfg.prependOutput (c : Cfg k Symbol State input) (pre : List Symbol) :
    Cfg k Symbol State input :=
  ⟨c.state, c.inputPos, c.workTapes, c.workTapePos, pre ++ c.output⟩

/-- The same configuration in a different control state, possibly of a different state type. -/
@[simps] def Cfg.withState (cfg : Cfg k Symbol State input)
    {State' : Type*} (q : Option State') : Cfg k Symbol State' input :=
  ⟨q, cfg.inputPos, cfg.workTapes, cfg.workTapePos, cfg.output⟩

/-- Forget the control state of a configuration, keeping the input head, the work tapes, the
work-tape heads and the output. A property of this part of a configuration makes sense for every
machine, whatever its state type. -/
@[simps] def Cfg.forgetState (cfg : Cfg k Symbol State input) : Cfg k Symbol Unit input :=
  ⟨some (), cfg.inputPos, cfg.workTapes, cfg.workTapePos, cfg.output⟩

/-- Remap the (optional) state of a configuration through `φ`, leaving the input head, the work
tapes, the work-tape heads and the output alone. Control-flow combinators such as `seq` embed a
sub-machine's configurations into the combined machine by exactly such a state remap. -/
@[simps] def Cfg.mapState {State' : Type*} (φ : Option State → Option State')
    (c : Cfg k Symbol State input) : Cfg k Symbol State' input :=
  ⟨φ c.state, c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- The initial configuration for a starting state and an input string. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/--
The effect of an action on a configuration: move the input head, write and move on the work tapes,
append the emitted symbol to the output tape, and go to the successor state. This is the part of a
step that does not depend on how the action was chosen.
-/
@[simps -fullyApplied]
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-- A work tape head moves by at most one cell when an action is applied. -/
lemma workTapePos_apply_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    |(action.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [Action.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

end Turing



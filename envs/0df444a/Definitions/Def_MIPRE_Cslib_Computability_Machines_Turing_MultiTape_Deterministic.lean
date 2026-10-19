-- Prove2me | Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
-- name    : MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:43.624032+00:00
-- url     : https://prove2.me/theorems/7d232758-eb92-40df-bee3-2dcafdce99b9
-- title:
--   Definitions of Deterministic: Deterministic Multi-Tape Turing Machines Defines deterministic Turing machines with a read-only input tape, `k` work…
-- statement:
--   The definitions of the module `MIPRE.Cslib.Computability.Machines.Turing.MultiTape.Deterministic` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Deterministic Multi-Tape Turing Machines. Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one write-only output tape. The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the blank symbol).
--
--   The module is vendored from [CSLib](https://github.com/leanprover/cslib) (commit `3aa9d441`, 2026-08-03; Apache 2.0): upstream file `Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`, by Christian Reitwiessner; the file header lists the adaptations. The declarations, statements and proofs are upstream's, not this repository's.
--
--   **Definitions** (13): `Turing.MultiTapeTM` (A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none` is the blank `BiTape` symbol).); `Turing.MultiTapeTM.Cfg` (The configurations of a Turing machine is relative to the input of the machine and consist of: - an `Option`al state (or none for the…); `Turing.MultiTapeTM.Cfg.inputSymbol` (The symbol currently under the input tape head.); `Turing.MultiTapeTM.Cfg.workTapeSymbols` (The symbol read by work tape `i`.); `Turing.MultiTapeTM.TransitionRelation` (The `TransitionRelation` corresponding to a `MultiTapeTM k Symbol` is defined by the `step` function, which maps a configuration to its…); `Turing.MultiTapeTM.configs` (The sequence of configurations of the Turing machine starting from `cfg`.); `Turing.MultiTapeTM.moveInputPos` (Attempt to move the input tape head.); `Turing.MultiTapeTM.outputSymbol` (The symbol (optionally) output when executing one step starting from configuration `cfg`.); `Turing.MultiTapeTM.spaceUsed` (The number of work tape cells touched by a computation starting from configuration `cfg` up to step `t`.); `Turing.MultiTapeTM.spaceUsedByTape` (The number of work tape cells touched by the head of tape `i` in the computation starting from configuration `cfg` up to step `t`.); `Turing.MultiTapeTM.step` (The step function corresponding to a `MultiTapeTM`.); and -15 more.
--
--   **Embedded lemmas** (11): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `configs_of_halts`, `configs_succ_eq_step'`, `configs_zero`, `inputSymbolInner`, `moveInputPos_leftBoundary`, `moveInputPos_rightBoundary`, `moveInputPos_zero`, `outputSymbol_of_halt`, `relatesInSteps_iff_configs_eq`, `spaceUsed_zero_tapes_eq_zero`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Cslib.Computability.Machines.Turing.MultiTape.Deterministic` (`MIPRE/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

/-
Vendored from CSLib (https://github.com/leanprover/cslib), upstream file
  Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean
at commit 3aa9d4416c185e0b9faeb72bbd65abe85b95dbcc (2026-08-03); fetched 2026-08-05.

CSLib cannot currently be a Lake dependency of this project: its MultiTape development
requires Lean >= v4.33.0-rc1, while this project pins v4.32.0. See
`planning/tm-infrastructure.md` (decision D1). Delete this copy and `require` CSLib once
the toolchains align.

Adaptations (the only differences from upstream):
* module-system markers removed: the `module` line, `public import` -> `import`, and the
  `@[expose] public section` line (replaced by the `set_option` lines below);
* `set_option autoImplicit true` / `set_option relaxedAutoImplicit true` added to restore
  the upstream Lean defaults (this project's lakefile disables both);
* the `RelatesInSteps` import redirected to the vendored copy (`MIPRE.Cslib...`);
* `open Cslib Relation` -> `open Relation` (the `Cslib` namespace is not vendored).
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Theorems.Thm_Relation_RelatesInSteps_succ_iff

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one write-only
output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AroraBarak09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Papadimitriou94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AroraBarak09], Claim 1.4). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Important Declarations

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `Cfg`: the configuration of a TM: the internal state, the work tape contents and head positions
* `spaceUsed`: the number of work tape cells touched by the heads until a certain step
* `TransitionRelation`: the transition relation from one configuration to the next
* `spaceUsed`: the number of tape cells touched by work tape heads, our main space measure
* `ComputesInTimeAndSpace`: a proof that a specific TM computes an output from an input in a certain
    number of steps and using a certain number of tape cells
* `ComputableInTimeAndSpace`: a proof that there is a multi-tape TM that computes a function
    (on strings) respecting a time and space bound in the input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

There are two ways to talk about the behaviour of a multi-tape Turing machine, and they are
proven to be equivalent.

* `MultiTapeTM.configs`: a sequence of configurations by execution step
* `RelatesInSteps tm.TransitionRelation cfg cfg' t`: a proof that `tm` transforms the configuration
    `cfg` into `cfg'` in exactly `t` steps

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]

-/

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Relation

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- The output of the transition function. -/
structure TransitionOut (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputMove : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workActions : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  outS : Option Symbol
  /-- The successor state or none to halt. -/
  q' : Option State

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank `BiTape` symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    TransitionOut k Symbol State

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Configurations of a Turing Machine

This section defines the configurations of a Turing machine,
the step function that lets the machine transition from one configuration to the next,
the resulting sequence of configurations and the initial configuration.
-/

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads.
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
deriving Inhabited

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

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by grind)

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  grind [Cfg.inputSymbol]

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q =>
    let {inputMove, workActions, q', ..} := tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    {
      state := q',
      inputPos := moveInputPos cfg.inputPos inputMove,
      workTapes i := match (workActions i).1 with
        | none => cfg.workTapes i
        | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
      workTapePos i := (cfg.workTapePos i) + (workActions i).2
    }

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).outS

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The sequence of configurations of the Turing machine starting from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def configs (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

@[simp]
lemma configs_zero {cfg : Cfg k Symbol State input} :
    tm.configs cfg 0 = cfg := by
  simp [configs]

lemma configs_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.configs cfg (t + 1) = tm.step (tm.configs cfg t) := by
  simp [configs, Function.iterate_succ_apply']

/-- The sequence of configurations from a halting state is constant. -/
@[simp]
lemma configs_of_halts (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.configs cfg n = cfg := by
  induction n with
  | zero => rfl
  | succ d ih =>
    rw [configs_succ_eq_step', ih, step_of_halt h]

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.configs cfg t').workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

end Space

open Cfg

/--
The `TransitionRelation` corresponding to a `MultiTapeTM k Symbol`
is defined by the `step` function,
which maps a configuration to its next configuration.
-/
@[scoped grind =]
def TransitionRelation (c₁ c₂ : Cfg k Symbol State input) : Prop := tm.step c₁ = c₂

/-- This lemma translates between the relational notion and the iterated step notion. The latter
can be more convenient especially for deterministic machines as we have here. -/
@[scoped grind =]
lemma relatesInSteps_iff_configs_eq
    (tm : MultiTapeTM k Symbol State)
    (cfg₁ cfg₂ : Cfg k Symbol State input)
    (t : ℕ) :
    RelatesInSteps tm.TransitionRelation cfg₁ cfg₂ t ↔ tm.configs cfg₁ t = cfg₂ := by
  unfold configs
  induction t generalizing cfg₁ cfg₂ with
  | zero => simp
  | succ t ih =>
    rw [RelatesInSteps.succ_iff, Function.iterate_succ_apply']
    constructor
    · grind
    · intro h_configs
      use tm.step^[t] cfg₁
      grind

end MultiTapeTM

end Turing



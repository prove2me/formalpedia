-- Prove2me | Definitions.Def_MIPRE_TM_MultiInput_Deterministic
-- name    : MIPRE_TM_MultiInput_Deterministic
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:40.245011+00:00
-- url     : https://prove2.me/theorems/3006f132-a7b0-4715-93da-3704b33a58f2
-- title:
--   Definitions of Deterministic: Deterministic multi-input multi-tape Turing machines Defines deterministic Turing machines with `i` two-way read-only…
-- statement:
--   The definitions of the module `MIPRE.TM.MultiInput.Deterministic` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Deterministic multi-input multi-tape Turing machines. Defines deterministic Turing machines with `i` two-way read-only input tapes, `w` work tapes and one write-only output tape — the machine model of MIP* = RE's normal form verifiers (a decider is a 5-input Turing machine; blueprint `def:decider`). This file generalizes the vendored CSLib development (`MIPRE.Cslib.Computability.Machines.Turing.MultiTape.Deterministic`, upstream `Turing.MultiTapeTM`) from one input tape to `i` of them, declaration for declaration and under the same names; `Turing.MultiTapeTM` is exactly the case `i = 1` (the…
--
--   **Definitions** (15): `Turing.MultiInputTM` (A deterministic Turing machine with `i` two-way read-only input tapes and `w` work tapes over the alphabet `Option Symbol` (where `none` is…); `Turing.MultiInputTM.Cfg` (The configurations of a multi-input Turing machine are relative to the tuple of inputs of the machine and consist of: - an `Option`al state…); `Turing.MultiInputTM.Cfg.inputSymbol` (The symbol currently under the head of input tape `j`.); `Turing.MultiInputTM.Cfg.inputSymbols` (The tuple of symbols under the input heads.); `Turing.MultiInputTM.Cfg.workTapeSymbols` (The symbol read by work tape `d`.); `Turing.MultiInputTM.TransitionOut` (The output of the transition function of a multi-input Turing machine.); `Turing.MultiInputTM.TransitionRelation` (The `TransitionRelation` corresponding to a `MultiInputTM i w Symbol State` is defined by the `step` function, which maps a configuration…); `Turing.MultiInputTM.configs` (The sequence of configurations of the Turing machine starting from `cfg`.); `Turing.MultiInputTM.initCfg` (The initial configuration corresponding to a tuple of input strings.); `Turing.MultiInputTM.outputString` (The string output by the Turing machine `tm` starting in configuration `cfg₀`, executing for `t` steps.); `Turing.MultiInputTM.outputSymbol` (The symbol (optionally) output when executing one step starting from configuration `cfg`.); and -11 more.
--
--   **Embedded lemmas** (9): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `inputSymbols_apply`, `configs_of_halts`, `configs_succ_eq_step'`, `configs_zero`, `inputSymbolInner`, `outputSymbol_of_halt`, `relatesInSteps_iff_configs_eq`, `spaceUsed_zero_tapes_eq_zero`, `step_of_halt`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.MultiInput.Deterministic` (`MIPRE/TM/MultiInput/Deterministic.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/MultiInput/Deterministic.lean; blueprint def:multiinput-tm

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/MultiInput/Deterministic.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Theorems.Thm_Relation_RelatesInSteps_succ_iff

/-!
# Deterministic multi-input multi-tape Turing machines

Defines deterministic Turing machines with `i` two-way read-only input tapes, `w` work
tapes and one write-only output tape — the machine model of MIP* = RE's normal form
verifiers (a decider is a 5-input Turing machine; blueprint `def:decider`).

This file generalizes the vendored CSLib development
(`MIPRE.Cslib.Computability.Machines.Turing.MultiTape.Deterministic`, upstream
`Turing.MultiTapeTM`) from one input tape to `i` of them, declaration for declaration and
under the same names; `Turing.MultiTapeTM` is exactly the case `i = 1` (the exact
correspondence is proved in `MIPRE.TM.MultiInput.OneInputEquiv`). All conventions are
inherited:

* tape symbols are `Option Symbol`, with `none` the blank symbol;
* each input head moves freely on its own input, clamped one cell beyond either end
  (`Turing.moveInputPos` is reused unchanged, one input tape at a time);
* the transition can optionally write and move on every work tape, and optionally emit one
  output symbol;
* halting is the absent successor state (`none`), and halted configurations are fixed
  points of `step`;
* space usage counts the work-tape cells visited by the heads; the input and output tapes
  are ignored for space.

Native multiple input tapes (rather than packing several inputs onto one tape by
concatenation) keep the paper's per-input time bounds honest: accessing one input never
costs time proportional to the lengths of the others. See
`planning/tm-infrastructure.md` (Milestone A) for the design record.

## Important declarations

* `MultiInputTM`: the machine
* `MultiInputTM.Cfg`: configurations, relative to the tuple of inputs
* `MultiInputTM.step`, `MultiInputTM.configs`: one step, and the step-indexed run
* `MultiInputTM.outputString`: the output emitted during the first `t` steps
* `MultiInputTM.spaceUsed`: the number of work-tape cells visited up to a step
* `MultiInputTM.TransitionRelation`: the relational view of `step`, tied to the iterated
  view by `relatesInSteps_iff_configs_eq`
* `MultiInputTM.haltsAtStep`, `MultiInputTM.halting_step_unique`: the exact halting step

The resource-bound packaging (`ComputesInTimeAndSpace`, `ComputesFunWithBounds`) is in
`MIPRE.TM.MultiInput.Complexity`.
-/

namespace Turing

open Relation

variable {i w : ℕ} {State Symbol : Type*}

/-- The output of the transition function of a multi-input Turing machine. -/
@[ext]
structure MultiInputTM.TransitionOut (i w : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of each input head. -/
  inputMoves : Fin i → SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workActions : Fin w → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  outS : Option Symbol
  /-- The successor state or `none` to halt. -/
  q' : Option State

/--
A deterministic Turing machine with `i` two-way read-only input tapes and `w` work tapes
over the alphabet `Option Symbol` (where `none` is the blank symbol). Note that it is not
required that `Symbol` or `State` are finite; finiteness enters only with the canonically
coded machines of `MIPRE.TM.Code`.
-/
structure MultiInputTM (i w : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the tuple of symbols under the input heads and
  the tuple of symbols under the work heads to a movement for each input head, actions on
  the work tapes, optionally a symbol to output and the successor state -/
  tr (q : State) (inputs : Fin i → Option Symbol) (work : Fin w → Option Symbol) :
    MultiInputTM.TransitionOut i w Symbol State

namespace MultiInputTM

-- Input-head movement is shared verbatim with the vendored one-input model.
open MultiTapeTM (moveInputPos)

variable {tm : MultiInputTM i w Symbol State}

section Cfg

/-!
## Configurations

This section defines the configurations of a multi-input Turing machine, the step function
that lets the machine transition from one configuration to the next, the resulting
sequence of configurations and the initial configuration. Input-head movement reuses
`Turing.moveInputPos` from the vendored CSLib file, one input tape at a time.
-/

/--
The configurations of a multi-input Turing machine are relative to the tuple of inputs of
the machine and consist of:
- an `Option`al state (or `none` for the halting state),
- the position of each input head (shifted by one),
- the contents of the work tapes,
- the positions of the work tape heads.
-/
@[ext]
structure Cfg (i w : ℕ) (Symbol State : Type*) (input : Fin i → List Symbol) where
  /-- the state of the machine (or `none` for the halting state) -/
  state : Option State
  /-- the position of each input head, shifted by one -/
  inputPos : (j : Fin i) → Fin ((input j).length + 2)
  /-- the work tapes -/
  workTapes : Fin w → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin w → ℤ
deriving Inhabited

variable {input : Fin i → List Symbol}

/-- The symbol currently under the head of input tape `j`. -/
def Cfg.inputSymbol (cfg : Cfg i w Symbol State input) (j : Fin i) : Option Symbol :=
  if h₁ : cfg.inputPos j = 0 then none
  else if h₂ : cfg.inputPos j = (input j).length + 1 then none
  else (input j)[(cfg.inputPos j).val - 1]'(by grind)

@[simp]
lemma inputSymbolInner {cfg : Cfg i w Symbol State input} (j : Fin i) (p : ℕ)
    (h₁ : (cfg.inputPos j).val = 1 + p)
    (h₂ : p < (input j).length) :
    cfg.inputSymbol j = some (input j)[p] := by
  grind [Cfg.inputSymbol]

/-- The tuple of symbols under the input heads. -/
def Cfg.inputSymbols (cfg : Cfg i w Symbol State input) : Fin i → Option Symbol :=
  fun j => cfg.inputSymbol j

@[simp]
lemma Cfg.inputSymbols_apply (cfg : Cfg i w Symbol State input) (j : Fin i) :
    cfg.inputSymbols j = cfg.inputSymbol j := rfl

/-- The symbol read by work tape `d`. -/
def Cfg.workTapeSymbols (cfg : Cfg i w Symbol State input) (d : Fin w) : Option Symbol :=
  cfg.workTapes d (cfg.workTapePos d)

/-- The step function corresponding to a `MultiInputTM`. -/
def step (cfg : Cfg i w Symbol State input) : Cfg i w Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q =>
    let {inputMoves, workActions, q', ..} := tm.tr q cfg.inputSymbols cfg.workTapeSymbols
    {
      state := q',
      inputPos j := moveInputPos (cfg.inputPos j) (inputMoves j),
      workTapes d := match (workActions d).1 with
        | none => cfg.workTapes d
        | some s => Function.update (cfg.workTapes d) (cfg.workTapePos d) s
      workTapePos d := (cfg.workTapePos d) + (workActions d).2
    }

/-- The symbol (optionally) output when executing one step starting from configuration
`cfg`. -/
def outputSymbol (cfg : Cfg i w Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbols cfg.workTapeSymbols).outS

/-- The initial configuration corresponding to a tuple of input strings. -/
@[simp]
def initCfg (input : Fin i → List Symbol) : Cfg i w Symbol State input :=
  ⟨some tm.q₀, fun _ => 1, fun _ _ => none, fun _ => 0⟩

@[simp]
lemma step_of_halt {cfg : Cfg i w Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The sequence of configurations of the Turing machine starting from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def configs (cfg : Cfg i w Symbol State input) (t : ℕ) : Cfg i w Symbol State input :=
  tm.step^[t] cfg

@[simp]
lemma configs_zero {cfg : Cfg i w Symbol State input} :
    tm.configs cfg 0 = cfg := by
  simp [configs]

lemma configs_succ_eq_step' {cfg : Cfg i w Symbol State input} {t : ℕ} :
    tm.configs cfg (t + 1) = tm.step (tm.configs cfg t) := by
  simp [configs, Function.iterate_succ_apply']

/-- The sequence of configurations from a halting state is constant. -/
@[simp]
lemma configs_of_halts (cfg : Cfg i w Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.configs cfg n = cfg := by
  induction n with
  | zero => rfl
  | succ d ih =>
    rw [configs_succ_eq_step', ih, step_of_halt h]

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg i w Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

end Cfg

section Space

/-! ## Space usage -/

variable {input : Fin i → List Symbol}

/-- The set of positions visited by the head of work tape `d` in the computation starting
from configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg i w Symbol State input) (t : ℕ) (d : Fin w) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.configs cfg t').workTapePos d

/--
The number of work tape cells touched by the head of tape `d` in the computation starting
from configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg i w Symbol State input) (t : ℕ) (d : Fin w) : ℕ :=
  (tm.visitedByTapeHead cfg t d).card

/--
The number of work tape cells touched by a computation starting from configuration `cfg`
up to step `t`.
-/
def spaceUsed (cfg : Cfg i w Symbol State input) (t : ℕ) : ℕ :=
  ∑ d, tm.spaceUsedByTape cfg t d

/-- A machine without work tapes uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg i w Symbol State input) (t : ℕ)
    (h_zero : w = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

end Space

open Cfg

variable {input : Fin i → List Symbol}

/--
The `TransitionRelation` corresponding to a `MultiInputTM i w Symbol State` is defined by
the `step` function, which maps a configuration to its next configuration.
-/
@[scoped grind =]
def TransitionRelation (c₁ c₂ : Cfg i w Symbol State input) : Prop := tm.step c₁ = c₂

/-- The string output by the Turing machine `tm` starting in configuration `cfg₀`,
executing for `t` steps. It is the concatenation of the symbols (optionally) emitted at
each of the first `t` steps. -/
def outputString
    (tm : MultiInputTM i w Symbol State)
    (cfg₀ : Cfg i w Symbol State input) (t : ℕ) : List Symbol :=
  (List.range t).flatMap fun t' => (tm.outputSymbol (tm.configs cfg₀ t')).toList

/-- This lemma translates between the relational notion and the iterated step notion. The
latter can be more convenient especially for deterministic machines as we have here. -/
@[scoped grind =]
lemma relatesInSteps_iff_configs_eq
    (tm : MultiInputTM i w Symbol State)
    (cfg₁ cfg₂ : Cfg i w Symbol State input)
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

end MultiInputTM

end Turing



-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:42.580545+00:00
-- url     : https://prove2.me/theorems/0f28a4fa-b44a-4f88-8354-43271be0fd47
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.Basic — Simulating multi-tape machines on numbers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.Basic` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The universal machine simulates a multi-tape Turing machine over the states and symbols `ℕ` from a
--   description (`Turing.MultiTapeTM.Universal.Desc`): the number of work tapes, the initial state and
--   a transition table. A transition maps a key (`Turing.MultiTapeTM.Universal.Key`) — the state and
--   the symbols under the heads, as the arguments of `Turing.MultiTapeTM.tr` — to an action
--   (`Turing.MultiTapeTM.Universal.Act`), which mirrors `Turing.Action` with the work tapes in a list.
--   A missing transition halts the machine.
--
--   The configurations (`Turing.MultiTapeTM.Universal.SCfg`) mirror `Turing.Cfg` without the output:
--   a step returns the symbol it emits, if any, and it is up to the caller to collect, use or discard
--   it. A work tape (`Turing.MultiTapeTM.Universal.Tape`) is a zipper: the position of its head, the
--   cells left of the head, nearest first, and the cells from the head on. It holds no more cells than
--   the head has visited, so a configuration takes space linear in the space of the simulated machine.
--   The input head is a number, encoded in binary by the universal machine.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Universal.Desc`: descriptions of machines.
--   * `Turing.MultiTapeTM.Universal.SCfg`: configurations of the simulation.
--   * `Turing.MultiTapeTM.Universal.step`: one step of the simulation, and the symbol it emits.
--   * `Turing.MultiTapeTM.Universal.simulate`: the output after a number of steps, and whether the
--     machine has halted.
--
--   **Contents.** The module is published as a whole: 22 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/Basic.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

-- vendored: every module imports `Cslib.Init`, which the test driver checks
public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Sign.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Iterate

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.Basic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Simulating multi-tape machines on numbers

The universal machine simulates a multi-tape Turing machine over the states and symbols `ℕ` from a
description (`Turing.MultiTapeTM.Universal.Desc`): the number of work tapes, the initial state and
a transition table. A transition maps a key (`Turing.MultiTapeTM.Universal.Key`) — the state and
the symbols under the heads, as the arguments of `Turing.MultiTapeTM.tr` — to an action
(`Turing.MultiTapeTM.Universal.Act`), which mirrors `Turing.Action` with the work tapes in a list.
A missing transition halts the machine.

The configurations (`Turing.MultiTapeTM.Universal.SCfg`) mirror `Turing.Cfg` without the output:
a step returns the symbol it emits, if any, and it is up to the caller to collect, use or discard
it. A work tape (`Turing.MultiTapeTM.Universal.Tape`) is a zipper: the position of its head, the
cells left of the head, nearest first, and the cells from the head on. It holds no more cells than
the head has visited, so a configuration takes space linear in the space of the simulated machine.
The input head is a number, encoded in binary by the universal machine.

## Main definitions

* `Turing.MultiTapeTM.Universal.Desc`: descriptions of machines.
* `Turing.MultiTapeTM.Universal.SCfg`: configurations of the simulation.
* `Turing.MultiTapeTM.Universal.step`: one step of the simulation, and the symbol it emits.
* `Turing.MultiTapeTM.Universal.simulate`: the output after a number of steps, and whether the
  machine has halted.
-/

namespace Turing.MultiTapeTM.Universal

/-- The key of a transition: the state and the symbols under the input head and the work-tape
heads. -/
public structure Key where
  /-- The state. -/
  state : ℕ
  /-- The symbol under the input head. -/
  input : Option ℕ
  /-- The symbols under the work-tape heads. -/
  work : List (Option ℕ)
-- vendored: imported transition lookups must reduce through the derived equality implementation.
deriving @[expose] DecidableEq, Inhabited

/-- An action, as `Turing.Action` with the work tapes in a list. -/
public structure Act where
  /-- The move of the input head. -/
  inputTape : SignType
  /-- What to write on each work tape, if anything, and how to move its head. -/
  workTapes : List (Option (Option ℕ) × SignType)
  /-- The symbol to emit, if any. -/
  output : Option ℕ
  /-- The next state, or `none` to halt. -/
  state : Option ℕ
deriving Inhabited

/-- A description of a machine: the number of work tapes, the initial state and the transitions. -/
public structure Desc where
  /-- The number of work tapes. -/
  tapes : ℕ
  /-- The initial state. -/
  q₀ : ℕ
  /-- The transitions. -/
  table : List (Key × Act)
deriving Inhabited

/-- A simulated work tape, as a zipper. -/
public structure Tape where
  /-- The position of the head. -/
  head : ℤ
  /-- The cells left of the head, nearest first. -/
  left : List (Option ℕ)
  /-- The cells from the head on. -/
  right : List (Option ℕ)
deriving Inhabited

/-- A configuration of the simulation, as `Turing.Cfg` with the work tapes in a list and without
the output. -/
public structure SCfg where
  /-- The state, or `none` once halted. -/
  state : Option ℕ
  /-- The position of the input head. -/
  inputPos : ℕ
  /-- The work tapes. -/
  workTapes : List Tape
deriving Inhabited

namespace Tape

/-- The symbol under the head. -/
@[expose] public def read (t : Tape) : Option ℕ := t.right.headD none

/-- Writes `o` under the head. -/
@[expose] public def write (t : Tape) (o : Option ℕ) : Tape := ⟨t.head, t.left, o :: t.right.tail⟩

/-- Moves the head by `m`. -/
@[expose] public def move (t : Tape) : SignType → Tape
  | .zero => t
  | .pos => ⟨t.head + 1, t.read :: t.left, t.right.tail⟩
  | .neg => ⟨t.head - 1, t.left.tail, t.left.headD none :: t.right⟩

/-- Applies the action on a work tape: write, then move. -/
@[expose] public def apply (t : Tape) (a : Option (Option ℕ) × SignType) : Tape :=
  (a.1.elim t t.write).move a.2

end Tape

/-- The symbol at position `p` of the input `x`, with blanks at position `0` and after the
input. -/
@[expose] public def inputSymbol (x : List ℕ) (p : ℕ) : Option ℕ :=
  if p = 0 then none else (x.drop (p - 1)).head?

/-- Moves the input head at position `p`, reading `a`, by `m`: right moves stop at the blank after
the input, which is the only blank right of position `0`. -/
@[expose] public def moveInput (p : ℕ) (a : Option ℕ) : SignType → ℕ
  | .zero => p
  | .neg => p - 1
  | .pos => if p = 0 ∨ a.isSome then p + 1 else p

public lemma isSome_inputSymbol (x : List ℕ) (p : ℕ) :
    (inputSymbol x p).isSome ↔ 0 < p ∧ p ≤ x.length := by
  unfold inputSymbol
  split_ifs with h
  · simp [h]
  · simp only [Option.isSome_iff_ne_none, ne_eq, List.head?_eq_none_iff, List.drop_eq_nil_iff]
    omega

public lemma moveInput_le {x : List ℕ} {p : ℕ} (h : p ≤ x.length + 1) (m : SignType) :
    moveInput p (inputSymbol x p) m ≤ x.length + 1 := by
  have hs := isSome_inputSymbol x p
  rcases m with _ | _ | _ <;> simp only [moveInput]
  · omega
  · omega
  · by_cases h : (inputSymbol x p).isSome
    · simp only [h, or_true, ↓reduceIte]
      have := hs.mp h
      omega
    · split_ifs with hc
      · rcases hc with hc | hc
        · omega
        · exact absurd hc h
      · omega

/-- Applies the actions to the work tapes, in order; a tape without an action is unchanged. -/
@[expose] public def applyTapes : List Tape → List (Option (Option ℕ) × SignType) → List Tape
  | [], _ => []
  | t :: ts, [] => t :: ts
  | t :: ts, a :: as => t.apply a :: applyTapes ts as

/-- The effect of an action on a configuration on the input `x`, as `Turing.Action.apply`, without
the output. -/
@[expose] public def Act.apply (a : Act) (x : List ℕ) (c : SCfg) : SCfg :=
  ⟨a.state, moveInput c.inputPos (inputSymbol x c.inputPos) a.inputTape,
    applyTapes c.workTapes a.workTapes⟩

/-- The key of the transition to take in `c`, on the input `x`, in the state `q`. -/
@[expose] public def SCfg.key (c : SCfg) (x : List ℕ) (q : ℕ) : Key :=
  ⟨q, inputSymbol x c.inputPos, c.workTapes.map Tape.read⟩

/-- One step of the machine described by `d` with the input head reading `a`, and the symbol it
emits: the step without the input. -/
@[expose] public def stepWith (d : Desc) (c : SCfg) (a : Option ℕ) : SCfg × Option ℕ :=
  match c.state with
  | none => (c, none)
  | some q =>
    match d.table.find? (·.1 = ⟨q, a, c.workTapes.map Tape.read⟩) with
    | none => ({ c with state := none }, none)
    | some e =>
      (⟨e.2.state, moveInput c.inputPos a e.2.inputTape, applyTapes c.workTapes e.2.workTapes⟩,
        e.2.output)

/-- One step of the machine described by `d` on the input `x`, and the symbol it emits. -/
@[expose] public def step (d : Desc) (x : List ℕ) (c : SCfg) : SCfg × Option ℕ :=
  match c.state with
  | none => (c, none)
  | some q =>
    match d.table.find? (·.1 = c.key x q) with
    | none => ({ c with state := none }, none)
    | some e => (e.2.apply x c, e.2.output)

/-- A step reads the input only at the input head. -/
public lemma step_eq_stepWith (d : Desc) (x : List ℕ) (c : SCfg) :
    step d x c = stepWith d c (inputSymbol x c.inputPos) := by
  obtain ⟨_ | q, ip, ts⟩ := c <;> rfl

/-- The initial configuration: the initial state, the input head on the first symbol and blank
work tapes. -/
@[expose] public def init (d : Desc) : SCfg := ⟨some d.q₀, 1, List.replicate d.tapes ⟨0, [], []⟩⟩

/-- A step that collects the emitted symbol. -/
@[expose] public def stepOut (d : Desc) (x : List ℕ) (c : SCfg × List ℕ) : SCfg × List ℕ :=
  ((step d x c.1).1, c.2 ++ (step d x c.1).2.toList)

/-- The output of the machine described by `d` on the input `x` after `t` steps, and whether it has
halted by then. -/
@[expose] public def simulate (d : Desc) (x : List ℕ) (t : ℕ) : List ℕ × Bool :=
  let c := (stepOut d x)^[t] (init d, [])
  (c.2, c.1.state.isNone)

end Turing.MultiTapeTM.Universal



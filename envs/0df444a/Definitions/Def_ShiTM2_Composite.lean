-- Prove2me | Definitions.Def_ShiTM2_Composite
-- name    : ShiTM2_Composite
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-14T19:09:56.238832+00:00
-- url     : https://prove2.me/theorems/b01a8aff-32e4-4bc9-8fa4-7421f45671b5
-- title:
--   Sequential composition of two multi-stack Turing machines: definitions
-- statement:
--   Definitions for the sequential composition of two finite multi-stack Turing machines: the combined stack index set with a scratch stack, the combined stack alphabet family, the combined label and internal-state types with a transfer register, the two program translations that relabel a component machine's statements into the composite and redirect the first machine's halt to the transfer loop, the two transfer loops, the composite program, the finiteness data, and the composite machine itself, together with the alphabet identifications at its input and output stacks.
--
--   The halt redirection is the reason a translation is needed at all: a halted machine takes no further steps, so the first component's program cannot be reused unchanged. The transfer proceeds in two passes through the scratch stack because popping a stack reverses it. The phase marker lives in the label type rather than the internal state because the halting configuration of a machine is required to have the initial internal state.
--
--   Definitions only. Nothing here asserts that the composite computes the composition, that its running time is bounded, or that any of the translations is correct.

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The sequential composite of two bundled TM2 machines -- DEFINITIONS ONLY.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

/-!
# The sequential composite of two `Turing.FinTM2` machines

Mathlib records `proof_wanted Turing.TM2ComputableInPolyTime.comp`
(`Mathlib/Computability/TuringMachine/Computable.lean:284`): the composite of two
polynomial-time bundled stack machines computes the composite function in polynomial time.
The informal recipe in that docstring is "one tape for each tape in both of the composed TMs;
run the first, copy its output tape onto the second's input tape, run the second".  A proof
has to **exhibit** that machine, which is data, so it cannot be built inside a theorem file
that is meant to be published as a theorem.  This file is that data and nothing else.

## The machine

Given `tm₁ tm₂ : Turing.FinTM2`, a symbol translation `tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀`
between the output alphabet of the first machine and the input alphabet of the second, and a
default symbol `dflt : tm₂.Γ tm₂.k₀`:

* stacks `CompK = tm₁.K ⊕ tm₂.K ⊕ Unit` -- both machines' stacks, plus one scratch stack whose
  alphabet is `tm₂.Γ tm₂.k₀`;
* labels `CompΛ = tm₁.Λ ⊕ tm₂.Λ ⊕ Bool` -- both machines' labels, plus two labels `lcopyA`
  (`false`) and `lcopyB` (`true`) for the two copy passes;
* internal state `Compσ = tm₁.σ × tm₂.σ × Option (tm₂.Γ tm₂.k₀)` -- both machines' states, plus
  a one-symbol transfer register;
* `k₀ = injK₁ tm₁.k₀`, `k₁ = injK₂ tm₂.k₁`, `main = injΛ₁ tm₁.main`.

A run of `comp tm₁ tm₂ tr dflt` has three phases:

1. **`tm₁`, relabelled** (`trStmt₁`).  Each stack index `k` becomes `injK₁ k`, each label `l`
   becomes `injΛ₁ l`, the internal state is projected in and out of the first component, and --
   the point of the exercise -- `Stmt.halt` becomes `Stmt.goto (fun _ => lcopyA)`.
2. **The copy phase** (`copyA`, `copyB`).  `copyA` pops `injK₁ tm₁.k₁` into the transfer
   register (applying `tr`) and pushes onto the scratch stack; `copyB` pops the scratch stack
   and pushes onto `injK₂ tm₂.k₀`, then `goto (injΛ₂ tm₂.main)`.  Two passes because a single
   pop/push pass reverses the list.
3. **`tm₂`, relabelled** (`trStmt₂`).  As phase 1 with `injK₂`/`injΛ₂` and the second state
   component, except that `Stmt.halt` stays `Stmt.halt`: the composite really does halt here.

## Three points where the design is forced

* **The halt redirection.**  `Turing.TM2.step M ⟨none, _, _⟩ = none`
  (`StackTuringMachine.lean:171-173`): a halted TM2 is *dead* and cannot be resumed.  So the
  first machine's program cannot be reused verbatim; its `halt` leaves must be rewritten to a
  `goto`.  This is the whole reason `trStmt₁` exists, and the reason `trStmt₁ ≠ trStmt₂`.
* **The phase marker lives in `Λ`, not in `σ`.**  `Turing.haltList`
  (`Computable.lean:118-123`) pins the final internal state to `tm.initialState`.  A
  σ-resident phase flag would have to be reset before halting; `Λ` is unconstrained at halt.
  With the marker in `Λ`, the final state is `(tm₁.initialState, tm₂.initialState, none)`,
  which is exactly `compInitialState`, because `tm₁`'s own halting state is `tm₁.initialState`
  (phase 1 leaves component 1 there), `tm₂`'s is `tm₂.initialState`, and the register is
  emptied by the last, failing, pop of `copyB`.
* **`Stmt.push k (f : σ → Γ k)` is total** (`StackTuringMachine.lean:128`), so every push must
  name a symbol even on branches that are never taken -- here the branch where the transfer
  register is empty.  `Turing.FinTM2` carries no `Inhabited (Γ k)` for any `k`, and
  `tm₂.Γ tm₂.k₀` can genuinely be empty, so a symbol has to come from outside: the explicit
  parameter `dflt`.  It is taken explicitly rather than as `[Inhabited (tm₂.Γ tm₂.k₀)]`
  because no instance for `tm₂.Γ tm₂.k₀` can ever be *found* by typeclass search (the
  `Fintype`/`DecidableEq` fields of `Turing.FinTM2` are structure fields, not instances --
  which is why Mathlib has to declare `Turing.FinTM2.decidableEqK` by hand,
  `Computable.lean:80-81`), so an instance binder would only force `@`-applications at every
  call site.  `dflt` is used *only* in the two unreachable push branches: it never appears in
  the output of a well-formed run.

## What is NOT here

This file contains **no theorem and no lemma**, not even a `private` one, and makes no claim
whatsoever about the behaviour of the machine it defines.  In particular none of the following
is stated or proved here:

1. that `comp tm₁ tm₂ tr dflt` computes `g ∘ f` when `tm₁` computes `f` and `tm₂` computes
   `g` -- the entire correctness claim;
2. that any phase of the run does what the prose above says: no simulation lemma for
   `trStmt₁`/`trStmt₂`, no transfer lemma for `copyA`/`copyB`, no step count;
3. that `liftStk₁`/`liftStk₂` commute with `Function.update` (the `Function.rec_update`
   application, `Mathlib/Logic/Function/Basic.lean:745`), nor that `injK₁`, `injK₂`, `injΛ₁`,
   `injΛ₂` are injective, nor that the three stack blocks are pairwise disjoint;
4. that `Turing.initList (comp ..) s` is the `liftStk₁`-lift of `Turing.initList tm₁ s`, or
   that `Turing.haltList (comp ..) t` is the `liftStk₂`-lift of `Turing.haltList tm₂ t`.
   Both `initList` and `haltList` are defined by a dependent `dite` that transports along an
   equality of stack indices, so these are real obligations, not `rfl`;
5. any time bound.  `comp` has no `time` field: `Turing.FinTM2` carries none.  The polynomial
   arithmetic, and the bound on the length of the intermediate string, are separate;
6. that `tr` is a bijection or that it is compatible with any encoding.  `tr` is an arbitrary
   function here; a caller composing `TM2ComputableInPolyTime` structures will instantiate it
   with `fun x => h₂.inputAlphabet.symm (h₁.outputAlphabet x)`
   (`Computable.lean:151-153`), but nothing in this file needs or records that;
7. that `dflt` is irrelevant.  `comp tm₁ tm₂ tr dflt` depends on `dflt` syntactically; the
   fact that no reachable configuration of a well-formed run reads it is a theorem.

Design decisions that a reader should check before building on this file:

* The alphabet family of the source machine is used in its **restricted** form
  `fun i => CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ i)`, which is *definitionally* `tm₁.Γ i` because
  `CompΓ` is a `Sum.elim` and `injK₁` is `Sum.inl`.  This is what lets the stack lifts have
  the type `((i : ι) → α (ctor i)) → ((i : κ) → α i)` that `Function.rec_update` demands, with
  no `Equiv`, no `List.map` and no cast anywhere.  Had the composite alphabet been an
  independent family with equivalences to `tm₁.Γ`/`tm₂.Γ`, every `push` and `pop` would carry
  a transport and the lifts would have the wrong type.
* The stack lifts take the background stacks as an **explicit first argument**
  (`liftStk₁ tm₁ tm₂ T`), so that the partially applied `liftStk₁ tm₁ tm₂ T` is a concrete
  function with a constant head.  A lift characterised only by hypotheses
  (`L S (injK₁ i) = S i`) leaves a metavariable in the head position and
  `Function.rec_update` then fails to unify.
* The two copy labels are indexed by `Bool` rather than `Fin 2`, because `false`/`true` are
  constructors and so usable as match patterns, whereas `(0 : Fin 2)` is an `OfNat` literal.
  Nothing else changes.
-/

namespace ShiTM2

open Turing

/-! ### Stacks -/

/-- Stack index type of the composite: the first machine's stacks, the second machine's
stacks, and one scratch stack. -/
abbrev CompK (tm₁ tm₂ : Turing.FinTM2) : Type := tm₁.K ⊕ tm₂.K ⊕ Unit

/-- The first machine's stacks inside the composite. -/
abbrev injK₁ (tm₁ tm₂ : Turing.FinTM2) (k : tm₁.K) : CompK tm₁ tm₂ := Sum.inl k

/-- The second machine's stacks inside the composite. -/
abbrev injK₂ (tm₁ tm₂ : Turing.FinTM2) (k : tm₂.K) : CompK tm₁ tm₂ := Sum.inr (Sum.inl k)

/-- The scratch stack, used to undo the reversal of a single pop/push pass. -/
abbrev kScr (tm₁ tm₂ : Turing.FinTM2) : CompK tm₁ tm₂ := Sum.inr (Sum.inr ())

/-- Alphabet family of the composite.  Written with `Sum.elim` (rather than a `match`) so that
`CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ i)` is `tm₁.Γ i` by `Sum.elim_inl`, i.e. by `rfl`, and so that
the restriction of `CompΓ` along `injK₁` is *literally* `tm₁.Γ`.  The scratch stack carries the
second machine's input symbols, since that is what is in transit. -/
abbrev CompΓ (tm₁ tm₂ : Turing.FinTM2) : CompK tm₁ tm₂ → Type :=
  Sum.elim tm₁.Γ (Sum.elim tm₂.Γ (fun _ : Unit => tm₂.Γ tm₂.k₀))

/-! ### Labels -/

/-- Label type of the composite: both machines' labels, plus the two copy-pass entry labels
`lcopyA` (`false`) and `lcopyB` (`true`). -/
abbrev CompΛ (tm₁ tm₂ : Turing.FinTM2) : Type := tm₁.Λ ⊕ tm₂.Λ ⊕ Bool

/-- The first machine's labels inside the composite. -/
abbrev injΛ₁ (tm₁ tm₂ : Turing.FinTM2) (l : tm₁.Λ) : CompΛ tm₁ tm₂ := Sum.inl l

/-- The second machine's labels inside the composite. -/
abbrev injΛ₂ (tm₁ tm₂ : Turing.FinTM2) (l : tm₂.Λ) : CompΛ tm₁ tm₂ := Sum.inr (Sum.inl l)

/-- Entry label of copy pass A: move `tm₁`'s output stack onto the scratch stack.  This is the
label that `trStmt₁` sends `Stmt.halt` to. -/
abbrev lcopyA (tm₁ tm₂ : Turing.FinTM2) : CompΛ tm₁ tm₂ := Sum.inr (Sum.inr false)

/-- Entry label of copy pass B: move the scratch stack onto `tm₂`'s input stack. -/
abbrev lcopyB (tm₁ tm₂ : Turing.FinTM2) : CompΛ tm₁ tm₂ := Sum.inr (Sum.inr true)

/-! ### Internal state -/

/-- Internal state of the composite: the first machine's state, the second machine's state, and
a one-symbol transfer register holding the symbol in flight during the copy phase. -/
abbrev Compσ (tm₁ tm₂ : Turing.FinTM2) : Type :=
  tm₁.σ × tm₂.σ × Option (tm₂.Γ tm₂.k₀)

/-- The initial (and, in a well-formed run, also the final) internal state of the composite.
`Turing.haltList` forces the final state to be this one, which is why the phase marker cannot
live in `σ`. -/
abbrev compInitialState (tm₁ tm₂ : Turing.FinTM2) : Compσ tm₁ tm₂ :=
  (tm₁.initialState, tm₂.initialState, none)

/-- Read the first machine's state out of the composite state. -/
abbrev prjσ₁ (tm₁ tm₂ : Turing.FinTM2) (s : Compσ tm₁ tm₂) : tm₁.σ := s.1

/-- Write the first machine's state into the composite state, leaving the rest alone. -/
abbrev injσ₁ (tm₁ tm₂ : Turing.FinTM2) (s : Compσ tm₁ tm₂) (u : tm₁.σ) : Compσ tm₁ tm₂ :=
  (u, s.2)

/-- Read the second machine's state out of the composite state. -/
abbrev prjσ₂ (tm₁ tm₂ : Turing.FinTM2) (s : Compσ tm₁ tm₂) : tm₂.σ := s.2.1

/-- Write the second machine's state into the composite state, leaving the rest alone. -/
abbrev injσ₂ (tm₁ tm₂ : Turing.FinTM2) (s : Compσ tm₁ tm₂) (u : tm₂.σ) : Compσ tm₁ tm₂ :=
  (s.1, u, s.2.2)

/-! ### Statements and configurations -/

/-- The statement type of the composite. -/
abbrev CompStmt (tm₁ tm₂ : Turing.FinTM2) : Type :=
  Turing.TM2.Stmt (CompΓ tm₁ tm₂) (CompΛ tm₁ tm₂) (Compσ tm₁ tm₂)

/-- The configuration type of the composite. -/
abbrev CompCfg (tm₁ tm₂ : Turing.FinTM2) : Type :=
  Turing.TM2.Cfg (CompΓ tm₁ tm₂) (CompΛ tm₁ tm₂) (Compσ tm₁ tm₂)

/-! ### Stack lifts

These are the concrete functions of type `((i : ι) → α (ctor i)) → ((i : κ) → α i)` that
`Function.rec_update` (`Mathlib/Logic/Function/Basic.lean:745`) requires as its `recursor`
argument.  The background stacks `T` come first, so that `liftStk₁ tm₁ tm₂ T` is a concrete
partial application: a lift described only by hypotheses leaves a metavariable in head
position and `rec_update` will not unify with it. -/

/-- Place the first machine's stacks into the composite, taking every other stack from the
background family `T`. -/
def liftStk₁ (tm₁ tm₂ : Turing.FinTM2) (T : ∀ k : CompK tm₁ tm₂, List (CompΓ tm₁ tm₂ k))
    (S : ∀ i : tm₁.K, List (CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ i))) :
    ∀ k : CompK tm₁ tm₂, List (CompΓ tm₁ tm₂ k)
  | Sum.inl i => S i
  | Sum.inr (Sum.inl j) => T (Sum.inr (Sum.inl j))
  | Sum.inr (Sum.inr ()) => T (Sum.inr (Sum.inr ()))

/-- Place the second machine's stacks into the composite, taking every other stack from the
background family `T`. -/
def liftStk₂ (tm₁ tm₂ : Turing.FinTM2) (T : ∀ k : CompK tm₁ tm₂, List (CompΓ tm₁ tm₂ k))
    (S : ∀ i : tm₂.K, List (CompΓ tm₁ tm₂ (injK₂ tm₁ tm₂ i))) :
    ∀ k : CompK tm₁ tm₂, List (CompΓ tm₁ tm₂ k)
  | Sum.inl i => T (Sum.inl i)
  | Sum.inr (Sum.inl j) => S j
  | Sum.inr (Sum.inr ()) => T (Sum.inr (Sum.inr ()))

/-- Lift a configuration of the first machine into the composite: its stacks go to the `injK₁`
block against the background `T`, its state to the first state component (the other two being
`w₂` and `r`), and its label to `injΛ₁` of itself -- except that the *halted* label `none`,
where the first machine dies, becomes the live label `lcopyA`.  That asymmetry is exactly what
`trStmt₁` implements. -/
def liftCfg₁ (tm₁ tm₂ : Turing.FinTM2) (T : ∀ k : CompK tm₁ tm₂, List (CompΓ tm₁ tm₂ k))
    (w₂ : tm₂.σ) (r : Option (tm₂.Γ tm₂.k₀))
    (c : Turing.TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) : CompCfg tm₁ tm₂ where
  l := Option.some (c.l.elim (lcopyA tm₁ tm₂) (injΛ₁ tm₁ tm₂))
  var := (c.var, w₂, r)
  stk := liftStk₁ tm₁ tm₂ T c.stk

/-- Lift a configuration of the second machine into the composite.  Here the halted label
`none` is carried over as `none`: the composite halts when the second machine does. -/
def liftCfg₂ (tm₁ tm₂ : Turing.FinTM2) (T : ∀ k : CompK tm₁ tm₂, List (CompΓ tm₁ tm₂ k))
    (w₁ : tm₁.σ) (r : Option (tm₂.Γ tm₂.k₀))
    (c : Turing.TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) : CompCfg tm₁ tm₂ where
  l := c.l.map (injΛ₂ tm₁ tm₂)
  var := (w₁, c.var, r)
  stk := liftStk₂ tm₁ tm₂ T c.stk

/-! ### Program translation -/

/-- The first machine's program, relabelled into the composite.  Stack indices go through
`injK₁`, labels through `injΛ₁`, the internal state through `prjσ₁`/`injσ₁` -- and
`Stmt.halt` becomes `Stmt.goto (fun _ => lcopyA)`, since a halted TM2 cannot be sequenced
after. -/
def trStmt₁ (tm₁ tm₂ : Turing.FinTM2) :
    Turing.TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ → CompStmt tm₁ tm₂
  | Turing.TM2.Stmt.push k f q =>
      Turing.TM2.Stmt.push (injK₁ tm₁ tm₂ k) (fun s => f (prjσ₁ tm₁ tm₂ s))
        (trStmt₁ tm₁ tm₂ q)
  | Turing.TM2.Stmt.peek k f q =>
      Turing.TM2.Stmt.peek (injK₁ tm₁ tm₂ k)
        (fun s o => injσ₁ tm₁ tm₂ s (f (prjσ₁ tm₁ tm₂ s) o)) (trStmt₁ tm₁ tm₂ q)
  | Turing.TM2.Stmt.pop k f q =>
      Turing.TM2.Stmt.pop (injK₁ tm₁ tm₂ k)
        (fun s o => injσ₁ tm₁ tm₂ s (f (prjσ₁ tm₁ tm₂ s) o)) (trStmt₁ tm₁ tm₂ q)
  | Turing.TM2.Stmt.load a q =>
      Turing.TM2.Stmt.load (fun s => injσ₁ tm₁ tm₂ s (a (prjσ₁ tm₁ tm₂ s)))
        (trStmt₁ tm₁ tm₂ q)
  | Turing.TM2.Stmt.branch f q₁ q₂ =>
      Turing.TM2.Stmt.branch (fun s => f (prjσ₁ tm₁ tm₂ s)) (trStmt₁ tm₁ tm₂ q₁)
        (trStmt₁ tm₁ tm₂ q₂)
  | Turing.TM2.Stmt.goto f =>
      Turing.TM2.Stmt.goto (fun s => injΛ₁ tm₁ tm₂ (f (prjσ₁ tm₁ tm₂ s)))
  | Turing.TM2.Stmt.halt => Turing.TM2.Stmt.goto (fun _ => lcopyA tm₁ tm₂)

/-- The second machine's program, relabelled into the composite.  As `trStmt₁`, with `injK₂`,
`injΛ₂` and the second state component, except that `Stmt.halt` stays `Stmt.halt`. -/
def trStmt₂ (tm₁ tm₂ : Turing.FinTM2) :
    Turing.TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ → CompStmt tm₁ tm₂
  | Turing.TM2.Stmt.push k f q =>
      Turing.TM2.Stmt.push (injK₂ tm₁ tm₂ k) (fun s => f (prjσ₂ tm₁ tm₂ s))
        (trStmt₂ tm₁ tm₂ q)
  | Turing.TM2.Stmt.peek k f q =>
      Turing.TM2.Stmt.peek (injK₂ tm₁ tm₂ k)
        (fun s o => injσ₂ tm₁ tm₂ s (f (prjσ₂ tm₁ tm₂ s) o)) (trStmt₂ tm₁ tm₂ q)
  | Turing.TM2.Stmt.pop k f q =>
      Turing.TM2.Stmt.pop (injK₂ tm₁ tm₂ k)
        (fun s o => injσ₂ tm₁ tm₂ s (f (prjσ₂ tm₁ tm₂ s) o)) (trStmt₂ tm₁ tm₂ q)
  | Turing.TM2.Stmt.load a q =>
      Turing.TM2.Stmt.load (fun s => injσ₂ tm₁ tm₂ s (a (prjσ₂ tm₁ tm₂ s)))
        (trStmt₂ tm₁ tm₂ q)
  | Turing.TM2.Stmt.branch f q₁ q₂ =>
      Turing.TM2.Stmt.branch (fun s => f (prjσ₂ tm₁ tm₂ s)) (trStmt₂ tm₁ tm₂ q₁)
        (trStmt₂ tm₁ tm₂ q₂)
  | Turing.TM2.Stmt.goto f =>
      Turing.TM2.Stmt.goto (fun s => injΛ₂ tm₁ tm₂ (f (prjσ₂ tm₁ tm₂ s)))
  | Turing.TM2.Stmt.halt => Turing.TM2.Stmt.halt

/-! ### The copy phase -/

/-- Load a symbol popped from `tm₁`'s output stack into the transfer register, translating it
along `tr`.  `none` (the pop failed, the stack was empty) clears the register. -/
abbrev loadRegA (tm₁ tm₂ : Turing.FinTM2) (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (s : Compσ tm₁ tm₂) (o : Option (tm₁.Γ tm₁.k₁)) : Compσ tm₁ tm₂ :=
  (s.1, s.2.1, o.map tr)

/-- Load a symbol popped from the scratch stack into the transfer register.  No translation:
the scratch stack and `tm₂`'s input stack have the same alphabet. -/
abbrev loadRegB (tm₁ tm₂ : Turing.FinTM2) (s : Compσ tm₁ tm₂)
    (o : Option (tm₂.Γ tm₂.k₀)) : Compσ tm₁ tm₂ :=
  (s.1, s.2.1, o)

/-- The loop test of both copy passes: did the pop succeed? -/
abbrev regIsSome (tm₁ tm₂ : Turing.FinTM2) (s : Compσ tm₁ tm₂) : Bool := s.2.2.isSome

/-- Read the transfer register back out, for pushing.  `Turing.TM2.Stmt.push` is total, so a
symbol is needed even on the branch where the register is empty; `dflt` supplies it and is
never read in a well-formed run. -/
abbrev pushReg (tm₁ tm₂ : Turing.FinTM2) (dflt : tm₂.Γ tm₂.k₀) (s : Compσ tm₁ tm₂) :
    tm₂.Γ tm₂.k₀ :=
  s.2.2.getD dflt

/-- **Copy pass A.**  Move `tm₁`'s output stack `injK₁ tm₁.k₁` onto the scratch stack,
translating symbols along `tr`, then fall through to `lcopyB`.  One pass reverses the list. -/
def copyA (tm₁ tm₂ : Turing.FinTM2) (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) : CompStmt tm₁ tm₂ :=
  Turing.TM2.Stmt.pop (injK₁ tm₁ tm₂ tm₁.k₁) (loadRegA tm₁ tm₂ tr)
    (Turing.TM2.Stmt.branch (regIsSome tm₁ tm₂)
      (Turing.TM2.Stmt.push (kScr tm₁ tm₂) (pushReg tm₁ tm₂ dflt)
        (Turing.TM2.Stmt.goto (fun _ => lcopyA tm₁ tm₂)))
      (Turing.TM2.Stmt.goto (fun _ => lcopyB tm₁ tm₂)))

/-- **Copy pass B.**  Move the scratch stack onto `tm₂`'s input stack `injK₂ tm₂.k₀`, undoing
the reversal of pass A, then enter the second machine at `injΛ₂ tm₂.main`. -/
def copyB (tm₁ tm₂ : Turing.FinTM2) (dflt : tm₂.Γ tm₂.k₀) : CompStmt tm₁ tm₂ :=
  Turing.TM2.Stmt.pop (kScr tm₁ tm₂) (loadRegB tm₁ tm₂)
    (Turing.TM2.Stmt.branch (regIsSome tm₁ tm₂)
      (Turing.TM2.Stmt.push (injK₂ tm₁ tm₂ tm₂.k₀) (pushReg tm₁ tm₂ dflt)
        (Turing.TM2.Stmt.goto (fun _ => lcopyB tm₁ tm₂)))
      (Turing.TM2.Stmt.goto (fun _ => injΛ₂ tm₁ tm₂ tm₂.main)))

/-- The program of the composite machine: the two relabelled programs on the two label blocks,
and the two copy passes on the two extra labels. -/
def compM (tm₁ tm₂ : Turing.FinTM2) (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) : CompΛ tm₁ tm₂ → CompStmt tm₁ tm₂
  | Sum.inl l => trStmt₁ tm₁ tm₂ (tm₁.m l)
  | Sum.inr (Sum.inl l) => trStmt₂ tm₁ tm₂ (tm₂.m l)
  | Sum.inr (Sum.inr false) => copyA tm₁ tm₂ tr dflt
  | Sum.inr (Sum.inr true) => copyB tm₁ tm₂ dflt

/-! ### Finiteness

The `DecidableEq`/`Fintype` fields of `Turing.FinTM2` are structure fields, not instances, so
they have to be fed to typeclass search by hand (`letI`) before the corresponding instance for
the sum/product can be found.  `Turing.FinTM2` provides `Fintype (Γ k₀)` only -- not
`Fintype (Γ k₁)`, not `∀ k, Fintype (Γ k)` -- and that is exactly enough here: the composite's
input alphabet is `tm₁.Γ tm₁.k₀` and its internal state mentions `tm₂.Γ tm₂.k₀`. -/

/-- Decidable equality of the composite's stack index type. -/
def compKDecEq (tm₁ tm₂ : Turing.FinTM2) : DecidableEq (CompK tm₁ tm₂) :=
  letI _i₁ : DecidableEq tm₁.K := tm₁.kDecidableEq
  letI _i₂ : DecidableEq tm₂.K := tm₂.kDecidableEq
  inferInstance

/-- The composite has finitely many stacks. -/
def compKFintype (tm₁ tm₂ : Turing.FinTM2) : Fintype (CompK tm₁ tm₂) :=
  letI _i₁ : Fintype tm₁.K := tm₁.kFin
  letI _i₂ : Fintype tm₂.K := tm₂.kFin
  inferInstance

/-- The composite has finitely many labels. -/
def compΛFintype (tm₁ tm₂ : Turing.FinTM2) : Fintype (CompΛ tm₁ tm₂) :=
  letI _i₁ : Fintype tm₁.Λ := tm₁.ΛFin
  letI _i₂ : Fintype tm₂.Λ := tm₂.ΛFin
  inferInstance

/-- The composite has finitely many internal states.  This is where
`tm₂.Γk₀Fin : Fintype (tm₂.Γ tm₂.k₀)` is needed: the transfer register ranges over the second
machine's input alphabet. -/
def compσFintype (tm₁ tm₂ : Turing.FinTM2) : Fintype (Compσ tm₁ tm₂) :=
  letI _i₁ : Fintype tm₁.σ := tm₁.σFin
  letI _i₂ : Fintype tm₂.σ := tm₂.σFin
  letI _i₃ : Fintype (tm₂.Γ tm₂.k₀) := tm₂.Γk₀Fin
  inferInstance

/-- The composite's input alphabet is finite: it *is* the first machine's input alphabet. -/
def compΓk₀Fintype (tm₁ tm₂ : Turing.FinTM2) :
    Fintype (CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ tm₁.k₀)) :=
  tm₁.Γk₀Fin

/-! ### The composite machine -/

/-- **The composite machine.**  Runs `tm₁` on its input stack, copies `tm₁`'s output stack onto
`tm₂`'s input stack through a scratch stack, then runs `tm₂` and halts.  `tr` translates the
first machine's output symbols into the second machine's input symbols; `dflt` is the dummy
symbol demanded by the totality of `Turing.TM2.Stmt.push` on the unreachable empty-register
branches.  Nothing here asserts that it computes anything. -/
def comp (tm₁ tm₂ : Turing.FinTM2) (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) : Turing.FinTM2 where
  K := CompK tm₁ tm₂
  kDecidableEq := compKDecEq tm₁ tm₂
  kFin := compKFintype tm₁ tm₂
  k₀ := injK₁ tm₁ tm₂ tm₁.k₀
  k₁ := injK₂ tm₁ tm₂ tm₂.k₁
  Γ := CompΓ tm₁ tm₂
  Λ := CompΛ tm₁ tm₂
  main := injΛ₁ tm₁ tm₂ tm₁.main
  ΛFin := compΛFintype tm₁ tm₂
  σ := Compσ tm₁ tm₂
  initialState := compInitialState tm₁ tm₂
  σFin := compσFintype tm₁ tm₂
  Γk₀Fin := compΓk₀Fintype tm₁ tm₂
  m := compM tm₁ tm₂ tr dflt

/-- The composite's input alphabet is the first machine's input alphabet, on the nose.  Stated
as an `Equiv` (rather than an equality of types) because that is the form
`Turing.TM2ComputableAux.inputAlphabet` (`Computable.lean:151`) consumes: a caller composes
this with the first machine's own `inputAlphabet`. -/
def compInputAlphabet (tm₁ tm₂ : Turing.FinTM2) (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) :
    (comp tm₁ tm₂ tr dflt).Γ (comp tm₁ tm₂ tr dflt).k₀ ≃ tm₁.Γ tm₁.k₀ :=
  Equiv.refl _

/-- The composite's output alphabet is the second machine's output alphabet, on the nose.  To
be composed with the second machine's own `outputAlphabet` (`Computable.lean:153`). -/
def compOutputAlphabet (tm₁ tm₂ : Turing.FinTM2) (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) :
    (comp tm₁ tm₂ tr dflt).Γ (comp tm₁ tm₂ tr dflt).k₁ ≃ tm₂.Γ tm₂.k₁ :=
  Equiv.refl _

end ShiTM2



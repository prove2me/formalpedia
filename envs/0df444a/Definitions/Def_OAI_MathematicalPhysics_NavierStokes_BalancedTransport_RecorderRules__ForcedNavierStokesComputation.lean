-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:01:20.961849+00:00
-- url     : https://prove2.me/theorems/496c256a-0536-49b3-86ca-47f19ae8428d
-- title:
--   The balanced three-stack recorder machine
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   The recorder is a three-stack machine that simulates a Turing machine $M$ reversibly. A configuration has a control state and three infinite stacks: left, right and history. Stack letters are work symbols $a$, marked symbols $\hat a$, a boundary marker, and records of executed transitions. Each step replaces finite prefixes of the three stacks and the control according to one row of a finite table.
--
--   1. **Machines.** A machine on states $Q$ and symbols $\Gamma$ has a halting state, a blank symbol, and a transition giving the next state, the written symbol and a head move (stay, left or right).
--   2. **Controls.** The control states are ready $q$, outward $q$, returning $q$ and execute $q$.
--   3. **Instructions.** An instruction prescribes a source and a target control and source and target prefixes for the three stacks. Applied to tails $t$, its source configuration puts the source prefixes in front of $t$, and its target configuration puts the target prefixes in front. An instruction is balanced when the total lengths of source and target prefixes agree.
--   4. **Rows.** There are nine kinds of row: enter, outward, supply, backward, restore, and the execution rows stay, left, right and extend. They mark the scanned cell, walk right to the boundary, take a fresh blank onto the history, walk back, and execute one transition of $M$. Execution consumes the blank on top of the history and pushes a record of the transition. Each row determines an instruction, and validity requires a non-halting state and, for execution rows, the matching head move.
--   5. **Decoding.** Functions read off from a configuration the unique row whose source (respectively target) it can be. So each step is determined by its source and also by its target, which makes the recorder reversible.
--   6. **Steps.** A step applies a valid row to some tails. The table is the finite set of valid rows, and $n$-step executions are defined inductively.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RecorderRules.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RecorderRules.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp__ForcedNavierStokesComputation

namespace OAI

noncomputable section
namespace BalancedTransport.Recorder

structure Machine (Q Γ : Type*) where
  halt : Q
  blank : Γ
  transition : Q → Γ → Transition Q Γ

inductive Record (Q Γ : Type*) where
  | stay (q : Q) (a : Γ)
  | left (q : Q) (a c : Γ)
  | right (q : Q) (a c : Γ)
  | extend (q : Q) (a : Γ)
  deriving DecidableEq, Fintype

inductive Letter (Q Γ : Type*) where
  | work (a : Γ)
  | marked (a : Γ)
  | boundary
  | record (r : Record Q Γ)
  deriving DecidableEq, Fintype

inductive Control (Q : Type*) where
  | ready (q : Q)
  | outward (q : Q)
  | returning (q : Q)
  | execute (q : Q)
  deriving DecidableEq, Fintype

structure Configuration (Q Γ : Type*) where
  control : Control Q
  left : Stream' (Letter Q Γ)
  right : Stream' (Letter Q Γ)
  history : Stream' (Letter Q Γ)

structure Tails (Q Γ : Type*) where
  left : Stream' (Letter Q Γ)
  right : Stream' (Letter Q Γ)
  history : Stream' (Letter Q Γ)

structure Instruction (Q Γ : Type*) where
  sourceControl : Control Q
  targetControl : Control Q
  sourceLeft : List (Letter Q Γ)
  sourceRight : List (Letter Q Γ)
  sourceHistory : List (Letter Q Γ)
  targetLeft : List (Letter Q Γ)
  targetRight : List (Letter Q Γ)
  targetHistory : List (Letter Q Γ)

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Instruction
open Stream'
variable {Q Γ : Type*}

def source (r : Instruction Q Γ) (t : Tails Q Γ) : Configuration Q Γ :=
  ⟨r.sourceControl, r.sourceLeft ++ₛ t.left,
    r.sourceRight ++ₛ t.right, r.sourceHistory ++ₛ t.history⟩

def target (r : Instruction Q Γ) (t : Tails Q Γ) : Configuration Q Γ :=
  ⟨r.targetControl, r.targetLeft ++ₛ t.left,
    r.targetRight ++ₛ t.right, r.targetHistory ++ₛ t.history⟩

def sourceTails (r : Instruction Q Γ) (c : Configuration Q Γ) : Tails Q Γ :=
  ⟨Stream'.drop r.sourceLeft.length c.left,
    Stream'.drop r.sourceRight.length c.right,
    Stream'.drop r.sourceHistory.length c.history⟩

def targetTails (r : Instruction Q Γ) (c : Configuration Q Γ) : Tails Q Γ :=
  ⟨Stream'.drop r.targetLeft.length c.left,
    Stream'.drop r.targetRight.length c.right,
    Stream'.drop r.targetHistory.length c.history⟩

@[simp] theorem sourceTails_source (r : Instruction Q Γ) (t : Tails Q Γ) :
    r.sourceTails (r.source t) = t := by
  cases t
  simp [sourceTails, source, Stream'.drop_append_stream]

@[simp] theorem targetTails_target (r : Instruction Q Γ) (t : Tails Q Γ) :
    r.targetTails (r.target t) = t := by
  cases t
  simp [targetTails, target, Stream'.drop_append_stream]

def Balanced (r : Instruction Q Γ) : Prop :=
  r.sourceLeft.length + r.sourceRight.length + r.sourceHistory.length =
    r.targetLeft.length + r.targetRight.length + r.targetHistory.length

end BalancedTransport.Recorder.Instruction
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

inductive Row (Q Γ : Type*) where
  | enter (q : Q) (a : Γ)
  | outward (q : Q) (c : Γ)
  | supply (q : Q)
  | backward (q : Q) (c : Γ)
  | restore (q : Q) (a : Γ)
  | stay (q : Q) (a : Γ)
  | left (q : Q) (a c : Γ)
  | right (q : Q) (a c : Γ)
  | extend (q : Q) (a : Γ)
  deriving DecidableEq, Fintype

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Row
open Stream'
variable {Q Γ : Type*}
open Control Letter

def valid (M : Machine Q Γ) : Row Q Γ → Prop
  | enter q _ | outward q _ | supply q | backward q _ | restore q _ => q ≠ M.halt
  | stay q a => q ≠ M.halt ∧ (M.transition q a).move = .stay
  | left q a _ => q ≠ M.halt ∧ (M.transition q a).move = .left
  | right q a _ | extend q a => q ≠ M.halt ∧ (M.transition q a).move = .right

def instruction (M : Machine Q Γ) : Row Q Γ → Instruction Q Γ
  | enter q a =>
      ⟨ready q, Control.outward q, [], [work a], [], [marked a], [], []⟩
  | outward q c =>
      ⟨Control.outward q, Control.outward q, [], [work c], [], [work c], [], []⟩
  | supply q =>
      ⟨Control.outward q, returning q, [], [boundary, work M.blank], [],
        [], [boundary], [work M.blank]⟩
  | backward q c =>
      ⟨returning q, returning q, [work c], [], [], [], [work c], []⟩
  | restore q a =>
      ⟨returning q, execute q, [marked a], [], [], [], [work a], []⟩
  | stay q a =>
      ⟨execute q, ready (M.transition q a).state, [], [work a], [work M.blank],
        [], [work (M.transition q a).write], [record (.stay q a)]⟩
  | left q a c =>
      ⟨execute q, ready (M.transition q a).state, [work c], [work a], [work M.blank],
        [], [work c, work (M.transition q a).write], [record (.left q a c)]⟩
  | right q a c =>
      ⟨execute q, ready (M.transition q a).state, [], [work a, work c], [work M.blank],
        [work (M.transition q a).write], [work c], [record (.right q a c)]⟩
  | extend q a =>
      ⟨execute q, ready (M.transition q a).state,
        [], [work a, boundary, work M.blank], [work M.blank],
        [work (M.transition q a).write], [work M.blank, boundary], [record (.extend q a)]⟩

end BalancedTransport.Recorder.Row
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} [DecidableEq Q] [DecidableEq Γ]
open Letter Control

def sourceRow (M : Machine Q Γ) (c : Configuration Q Γ) : Option (Row Q Γ) :=
  match c.control with
  | ready q =>
      if q = M.halt then none else
      match c.right.head with
      | work a => some (.enter q a)
      | _ => none
  | outward q =>
      if q = M.halt then none else
      match c.right.head with
      | work a => some (.outward q a)
      | boundary => if c.right.tail.head = work M.blank then some (.supply q) else none
      | _ => none
  | returning q =>
      if q = M.halt then none else
      match c.left.head with
      | work a => some (.backward q a)
      | marked a => some (.restore q a)
      | _ => none
  | execute q =>
      if q = M.halt then none else
      if c.history.head = work M.blank then
        match c.right.head with
        | work a =>
            match (M.transition q a).move with
            | .stay => some (.stay q a)
            | .left =>
                match c.left.head with
                | work v => some (.left q a v)
                | _ => none
            | .right =>
                match c.right.tail.head with
                | work v => some (.right q a v)
                | boundary =>
                    if c.right.tail.tail.head = work M.blank then some (.extend q a) else none
                | _ => none
        | _ => none
      else none

def targetRow (c : Configuration Q Γ) : Option (Row Q Γ) :=
  match c.control with
  | ready _ =>
      match c.history.head with
      | record (.stay q a) => some (.stay q a)
      | record (.left q a v) => some (.left q a v)
      | record (.right q a v) => some (.right q a v)
      | record (.extend q a) => some (.extend q a)
      | _ => none
  | outward q =>
      match c.left.head with
      | marked a => some (.enter q a)
      | work a => some (.outward q a)
      | _ => none
  | returning q =>
      match c.right.head with
      | boundary => some (.supply q)
      | work a => some (.backward q a)
      | _ => none
  | execute q =>
      match c.right.head with
      | work a => some (.restore q a)
      | _ => none

@[simp] theorem sourceRow_source (M : Machine Q Γ) (r : Row Q Γ)
    (hr : r.valid M) (t : Tails Q Γ) :
    sourceRow M ((r.instruction M).source t) = some r := by
  cases r <;>
    simp_all [Row.valid, Row.instruction, Instruction.source, sourceRow,
      Stream'.appendStream', Stream'.head]

omit [DecidableEq Q] [DecidableEq Γ] in

@[simp] theorem targetRow_target (M : Machine Q Γ) (r : Row Q Γ) (t : Tails Q Γ) :
    targetRow ((r.instruction M).target t) = some r := by
  cases r <;>
    simp [Row.instruction, Instruction.target, targetRow,
      Stream'.appendStream', Stream'.head]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

def Step {Q Γ : Type*} (M : Machine Q Γ) (c d : Configuration Q Γ) : Prop :=
  ∃ r : Row Q Γ, r.valid M ∧ ∃ t : Tails Q Γ,
    c = (r.instruction M).source t ∧ d = (r.instruction M).target t

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} [DecidableEq Q] [DecidableEq Γ]

instance (M : Machine Q Γ) : DecidablePred (Row.valid M) := by
  intro r
  cases r <;> simp only [Row.valid] <;> infer_instance

def table [Fintype Q] [Fintype Γ] (M : Machine Q Γ) : Finset (Row Q Γ) :=
  Finset.univ.filter (Row.valid M)

omit [DecidableEq Γ] in

@[simp] theorem mem_table [Fintype Q] [Fintype Γ] (M : Machine Q Γ) (r : Row Q Γ) :
    r ∈ table M ↔ r.valid M := by
  simp [table]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

inductive Exec {Q Γ : Type*} (M : Machine Q Γ) :
    ℕ → Configuration Q Γ → Configuration Q Γ → Prop
  | refl (c) : Exec M 0 c c
  | cons {n c d e} : Step M c d → Exec M n d e → Exec M (n + 1) c e

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} (M : Machine Q Γ)
open Letter Control

end BalancedTransport.Recorder
end

end OAI



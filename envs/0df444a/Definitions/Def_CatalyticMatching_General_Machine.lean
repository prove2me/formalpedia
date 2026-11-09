-- Prove2me | Definitions.Def_CatalyticMatching_General_Machine
-- name    : CatalyticMatching_General_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:57.128508+00:00
-- url     : https://prove2.me/theorems/bf73d973-6f9e-4084-8e33-62a8b67323ea
-- title:
--   Finite deterministic catalytic Turing machines and charged execution
-- statement:
--   A finite binary machine has a finite state set and a finite transition table. A transition reads only the control state, scanned input/work/catalyst symbols and three origin flags. It writes one work bit, optionally one catalyst bit, moves each head at most one cell, and appends at most one output bit. The input is read-only, the output is append-only and unreadable, and the work tape starts entirely zero.
--
--   $$C_{t+1}=\operatorname{step}_M(x,C_t).$$
--
--   The catalyst is exactly the arbitrary supplied finite bitstring, with an endmarker; attempts to leave its bounds or write its endmarker have no successor. Input has endmarkers, and the work tape is semi-infinite. All visited work positions count toward space. A run must reach a genuine halting configuration. This interface provides execution semantics, without a matching oracle or a resource correctness field.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Definitions 2.1–2.3 p.10

import Mathlib

namespace CatalyticMatching.General

/-- A finite instruction moves each head at most one cell. -/
inductive Move | left | stay | right
  deriving DecidableEq

def Move.apply : Move → ℕ → ℕ
  | .left, h => h - 1
  | .stay, h => h
  | .right, h => h + 1

/-- No instruction can inspect output, an address, or a whole tape. -/
structure Instruction (q : ℕ) where
  next : Option (Fin q)
  workWrite : Bool
  catalystWrite : Option Bool
  inputMove : Move
  workMove : Move
  catalystMove : Move
  emit : Option Bool

/-- Finite binary transition table with end/origin sensors. All its arguments
have finite types; in particular it has no input-dependent oracle. -/
structure Machine where
  states : ℕ
  start : Fin states
  table : Fin states → Option Bool → Bool → Option Bool →
    Bool → Bool → Bool → Instruction states

structure Configuration (M : Machine) where
  state : Option (Fin M.states)
  inputHead : ℕ
  workHead : ℕ
  catalystHead : ℕ
  work : ℕ → Bool
  catalyst : List Bool
  output : List Bool

/-- Initially blank work; every catalyst bit is supplied arbitrarily. -/
def Machine.initial (M : Machine) (τ : List Bool) : Configuration M :=
  ⟨some M.start, 0, 0, 0, fun _ => false, τ, []⟩

/-- Input has endmarkers at 0 and length+1. Input and catalyst heads cannot
move beyond their right endmarkers. A write on the catalyst endmarker is illegal.
Illegal steps have no successor and cannot satisfy a halting certificate. -/
def Machine.step (M : Machine) (x : List Bool) (c : Configuration M) :
    Option (Configuration M) :=
  match c.state with
  | none => some c
  | some q =>
    let a := M.table q (if c.inputHead = 0 then none else x[c.inputHead - 1]?)
      (c.work c.workHead) c.catalyst[c.catalystHead]?
      (c.inputHead == 0) (c.workHead == 0) (c.catalystHead == 0)
    if a.inputMove.apply c.inputHead ≤ x.length + 1 ∧
        a.catalystMove.apply c.catalystHead ≤ c.catalyst.length ∧
        (a.catalystWrite.isSome → c.catalystHead < c.catalyst.length) then
      some ⟨a.next, a.inputMove.apply c.inputHead, a.workMove.apply c.workHead,
        a.catalystMove.apply c.catalystHead,
        Function.update c.work c.workHead a.workWrite,
        (match a.catalystWrite with
          | none => c.catalyst
          | some b => c.catalyst.set c.catalystHead b),
        c.output ++ a.emit.toList⟩
    else none

/-- Each successor costs one actual finite-table step. -/
def Machine.run (M : Machine) (x τ : List Bool) : ℕ → Option (Configuration M)
  | 0 => some (M.initial τ)
  | t + 1 => (M.run x τ t).bind (M.step x)

/-- All visited work positions, including the halting head, count as work bits.
The append-only output is never passed to the transition table. -/
def Machine.workBound (M : Machine) (x τ : List Bool) (t bound : ℕ) : Prop :=
  ∀ s ≤ t, ∀ c, M.run x τ s = some c → c.workHead < bound

end CatalyticMatching.General



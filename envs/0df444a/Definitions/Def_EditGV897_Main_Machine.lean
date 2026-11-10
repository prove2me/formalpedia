-- Prove2me | Definitions.Def_EditGV897_Main_Machine
-- name    : EditGV897_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:23:50.225479+00:00
-- url     : https://prove2.me/theorems/2c5f8148-92d3-4a17-8ccc-ddfec5f78538
-- title:
--   Finite deterministic binary tape programs
-- statement:
--   A program is a finite transition table over finitely many states and a fixed finite number of two-way tapes. Each tape cell holds a bit or a distinct blank symbol. Tape 0 receives the explicit input and all other tapes, including output tape 1, start blank. One transition reads the heads, writes one symbol per tape, moves each head at most one position, and changes state; a missing transition halts.
--
--   For input and output bit lists $a,z$, the execution predicate is
--
--   $$\operatorname{Runs}(P,a,z,B)\iff\text{a halting execution of }P\text{ produces }z\text{ within }B\text{ transitions}.$$
--
--   This supplies an operational bit-time meaning for every deterministic polynomial-time assertion. Output is written on the initially blank output tape and terminated by a blank. Dimensions have self-delimiting unary headers; integer values have framed binary digits, with a sign bit for signed values. The common bound is $A(s+1)^d$.
--
--   **Formalization Note** Tape lists represent finite visited support of infinite blank tapes. Programs have finite state and tape types, never callbacks on unbounded integers or functions. Unit transitions are a standard fixed-tape Turing cost model, polynomially equivalent to bit complexity. No correctness or runtime is a structure field.
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §§2.2, 3.2, 4.1–4.3, printed pp. 5, 8–14 / PDF pp. 6, 9–15; explicit standard machine encoding of the computational claims

import Mathlib

namespace EditGV897.Main

/-- A binary tape has a distinct blank symbol. Lists represent finite visited support. -/
structure Tape where
  left : List (Option Bool)
  head : Option Bool
  right : List (Option Bool)
  deriving DecidableEq

inductive Motion where
  | left | stay | right
  deriving DecidableEq

def Tape.writeMove (s : Tape) (a : Option Bool) : Motion → Tape
  | .left => ⟨s.left.drop 1, s.left.headD none, a :: s.right⟩
  | .stay => ⟨s.left, a, s.right⟩
  | .right => ⟨a :: s.left, s.right.headD none, s.right.drop 1⟩

/-- Finite transition table; tape 0 is input and tape 1 is initially blank output. -/
structure Program where
  states : ℕ
  workTapes : ℕ
  transition : Fin (states + 1) → (Fin (workTapes + 2) → Option Bool) →
    Option (Fin (states + 1) × (Fin (workTapes + 2) → Option Bool × Motion))

structure Configuration (P : Program) where
  state : Fin (P.states + 1)
  tapes : Fin (P.workTapes + 2) → Tape

def initial (P : Program) (input : List Bool) : Configuration P :=
  ⟨0, fun i => if i.val = 0 then
    ⟨[], (input.map some).headD none, (input.map some).drop 1⟩ else ⟨[], none, []⟩⟩

def step (P : Program) (c : Configuration P) : Option (Configuration P) :=
  (P.transition c.state (fun i => (c.tapes i).head)).map fun a =>
    ⟨a.1, fun i => (c.tapes i).writeMove (a.2 i).1 (a.2 i).2⟩

/-- Fuel counts individual simultaneous fixed-tape transitions, including IO work. -/
def execute (P : Program) : ℕ → Configuration P → Configuration P
  | 0, c => c
  | k + 1, c => match step P c with
    | none => c
    | some c' => execute P k c'

/-- Halt with the output head at the first output bit and a blank terminator. -/
def Runs (P : Program) (input output : List Bool) (budget : ℕ) : Prop :=
  ∃ k ≤ budget, ∃ c : Configuration P,
    execute P k (initial P input) = c ∧ step P c = none ∧
    (c.tapes ⟨1, by omega⟩).head :: (c.tapes ⟨1, by omega⟩).right =
      output.map some ++ [none]

/-- Self-delimiting unary dimension/header and length-framed binary data. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]
def frame (x : List Bool) : List Bool := unary x.length ++ x

/-- Canonical binary integers, most significant bit first; zero has no digits. -/
def binary (n : ℕ) : List Bool := n.bits.reverse
def integerCode (z : ℤ) : List Bool := decide (z < 0) :: frame (binary z.natAbs)
def polyBudget (A d s : ℕ) : ℕ := A * (s + 1) ^ d

end EditGV897.Main



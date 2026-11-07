-- Prove2me | Definitions.Def_BoolCSPDel_Program
-- name    : BoolCSPDel_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:47.445533+00:00
-- url     : https://prove2.me/theorems/d32cd584-5105-42a2-ac3a-5ea1ee53bc9c
-- title:
--   The space-counted machine: finite program, work tape, one-way input and coins
-- statement:
--   A **program** has a finite control and one binary work tape, initially blank, with instructions: write a bit, move the head, branch on the current cell, branch on the next fair coin, branch on the next input bit, stop. Input and coins are one-way, so whatever the program wants to keep costs tape. **Space** is the number of tape cells visited; time is the number of steps.
--
--   A further instruction, `query`, is used only by the dictionary statements: it reads a self-delimiting number at the head and writes the oracle's answer on the tape from the head on, at unit time. The answer's cells count towards space.
--
--   **Formalization Note** The paper names no machine. It counts "all retained memory, including decoding workspace" and "stored randomness, output, and working space", and a family of automata with free output maps cannot express that, so this machine is the reading of those phrases. Numbers are coded by doubling each bit (least significant first) and ending with $01$. A `query` on a malformed argument has an empty answer.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), §3.1, p.17; Theorem 5.5, pp.32–33; Lemma A.4, p.55

import Mathlib

namespace BoolCSPDel

/-- Self-delimiting binary code: the bits of `x` (least significant first), each doubled, then the
terminator `01`. -/
def encNat (x : ℕ) : List Bool :=
  (Nat.bits x).flatMap (fun b => [b, b]) ++ [false, true]

/-- The tape cells from `start` on hold the word `w`. -/
def TapeHolds (tape : ℕ → Bool) (start : ℕ) (w : List Bool) : Prop :=
  ∀ (i : ℕ) (h : i < w.length), tape (start + i) = w[i]

/-- One instruction of a program with control states `Q`. -/
inductive Instr (Q : Type) : Type
  /-- `cell[head] := b`, go to `q`. -/
  | write (b : Bool) (q : Q)
  /-- Move the head left (stays at cell `0`), go to `q`. -/
  | left (q : Q)
  /-- Move the head right, go to `q`. -/
  | right (q : Q)
  /-- Branch on `cell[head]`. -/
  | test (q₀ q₁ : Q)
  /-- Branch on the next coin; the coin position advances. -/
  | coin (q₀ q₁ : Q)
  /-- Branch on the next input bit and advance; `qEnd` once the input is exhausted. -/
  | read (q₀ q₁ qEnd : Q)
  /-- Oracle call on the `encNat`-coded number starting at the head; the answer's bits overwrite the
  cells from the head on. -/
  | query (q : Q)
  /-- Stop. -/
  | halt

/-- **The space-counted machine of the upper bound.** Bandekar, Sharma, Velusamy, STOC 2027 submission
(manuscript sha256 15f83519…): p.17, "We allow unrestricted computation time and count all retained
memory, including decoding workspace"; Theorem 5.5, p.33, "including stored randomness, output, and
working space, for every choice of random seeds".

A finite program on one binary work tape, with a one-way input word and one-way fair coins.

**Formalization Note.** The paper names no machine. This is the reading that makes "all retained
memory" mean something: a per-`n` automaton with a free output map would have no decoding workspace
and could hold a free seed. Input and coins cannot be reread, so whatever the program keeps costs
tape. `query` is used only by the dictionary statements (Corollary 5.4, Theorem 5.5), where it models
"the time needed to obtain a row" at unit cost; its answer still occupies tape. -/
structure Program : Type 1 where
  /-- Control states. -/
  Q : Type
  [fin : Fintype Q]
  /-- Initial state. -/
  start : Q
  /-- The instruction of each state. -/
  act : Q → Instr Q

attribute [instance] Program.fin

/-- No `query` instruction. -/
def OracleFree (P : Program) : Prop := ∀ q q', P.act q ≠ Instr.query q'

/-- A machine configuration. `maxCell` is the largest cell ever at the head or written. -/
structure Config (Q : Type) : Type where
  /-- Control state. -/
  state : Q
  /-- Work tape. -/
  tape : ℕ → Bool
  /-- Head position. -/
  head : ℕ
  /-- The input not yet read. -/
  input : List Bool
  /-- Number of coins already used. -/
  coinPos : ℕ
  /-- Largest cell visited. -/
  maxCell : ℕ
  /-- Number of steps taken. -/
  steps : ℕ

/-- Cells visited: `maxCell + 1`. -/
def Config.space {Q : Type} (c : Config Q) : ℕ := c.maxCell + 1

/-- The initial configuration: blank (all `false`) tape, head at cell `0`. -/
def Config.init (P : Program) (word : List Bool) : Config P.Q :=
  { state := P.start, tape := fun _ => false, head := 0, input := word, coinPos := 0, maxCell := 0,
    steps := 0 }

open Classical in
/-- The argument of a `query`: the number whose `encNat` code starts at the head, if any (unique,
as the code is prefix-free). -/
noncomputable def queryArg (tape : ℕ → Bool) (head : ℕ) : Option ℕ :=
  if h : ∃ x, TapeHolds tape head (encNat x) then some (Classical.choose h) else none

/-- The tape after writing `w` from the head on. -/
def overwrite (tape : ℕ → Bool) (head : ℕ) (w : List Bool) : ℕ → Bool :=
  fun i => if head ≤ i then w.getD (i - head) (tape i) else tape i

/-- One step. A halted configuration stutters and takes no time. A `query` costs one step; with a
malformed argument its answer is empty. -/
noncomputable def step (P : Program) (O : ℕ → List Bool) (coins : ℕ → Bool) (c : Config P.Q) :
    Config P.Q :=
  match P.act c.state with
  | Instr.write b q =>
      { c with state := q, tape := Function.update c.tape c.head b, steps := c.steps + 1 }
  | Instr.left q => { c with state := q, head := c.head - 1, steps := c.steps + 1 }
  | Instr.right q =>
      { c with state := q, head := c.head + 1, maxCell := max c.maxCell (c.head + 1),
               steps := c.steps + 1 }
  | Instr.test q₀ q₁ =>
      { c with state := if c.tape c.head then q₁ else q₀, steps := c.steps + 1 }
  | Instr.coin q₀ q₁ =>
      { c with state := if coins c.coinPos then q₁ else q₀, coinPos := c.coinPos + 1,
               steps := c.steps + 1 }
  | Instr.read q₀ q₁ qEnd =>
      match c.input with
      | [] => { c with state := qEnd, steps := c.steps + 1 }
      | x :: xs => { c with state := if x then q₁ else q₀, input := xs, steps := c.steps + 1 }
  | Instr.query q =>
      let w := match queryArg c.tape c.head with
        | some x => O x
        | none => []
      { c with state := q, tape := overwrite c.tape c.head w,
               maxCell := max c.maxCell (c.head + w.length - 1), steps := c.steps + 1 }
  | Instr.halt => c

/-- The configuration after `t` steps. -/
noncomputable def run (P : Program) (O : ℕ → List Bool) (word : List Bool) (coins : ℕ → Bool)
    (t : ℕ) : Config P.Q :=
  (step P O coins)^[t] (Config.init P word)

/-- `c` is the halted configuration of the run. -/
def HaltsWith (P : Program) (O : ℕ → List Bool) (word : List Bool) (coins : ℕ → Bool)
    (c : Config P.Q) : Prop :=
  (∃ t, run P O word coins t = c) ∧ P.act c.state = Instr.halt

/-- The oracle of an `OracleFree` program; never consulted. -/
def noOracle : ℕ → List Bool := fun _ => []

end BoolCSPDel


